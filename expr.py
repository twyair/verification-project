from collections import defaultdict
from dataclasses import dataclass
import enum
from typing import (
    Any,
    Callable,
    DefaultDict,
    Dict,
    List,
    ClassVar,
    Tuple,
    Union,
)
import operator
from cast import AstType, AstNode
import z3


@enum.unique
class Type(enum.Enum):
    int = "int"
    float = "float"
    bool = "bool"
    array_int = "array_int"
    array_float = "array_float"
    array_bool = "array_bool"


@dataclass
class Environment:
    scopes: List[Dict[str, Type]]
    vars: Dict[str, Type]
    names_count: DefaultDict[str, int]
    renamer: List[Dict[str, str]]

    @staticmethod
    def empty():
        return Environment(
            scopes=[{}], vars={}, names_count=defaultdict(lambda: 0), renamer=[{}],
        )

    def __getitem__(self, var: str) -> Type:
        for scope in reversed(self.scopes):
            if var in scope:
                return scope[var]
        assert False, f"{var} is not in the environment"

    def __setitem__(self, var: str, type_: Type) -> None:
        self.scopes[-1][var] = type_
        if self.names_count[var] > 0:
            self.renamer[-1][var] = f"{var}${self.names_count[var]}"
        self.names_count[var] += 1
        self.vars[self.rename(var)] = type_

    def __contains__(self, var: str) -> bool:
        for scope in self.scopes:
            if var in scope:
                return True
        return False

    def rename(self, var: str) -> str:
        for scope in reversed(self.renamer):
            if var in scope:
                return scope[var]
        return var

    def open_scope(self) -> None:
        self.scopes.append({})
        self.renamer.append({})

    def close_scope(self) -> None:
        self.scopes.pop()
        self.renamer.pop()

    def get_vars(self) -> Dict[str, Type]:
        return self.vars.copy()


@dataclass(frozen=True)
class GenericExpr:
    def assign(self, vars: Dict[str, "GenericExpr"]) -> "GenericExpr":
        raise NotImplementedError

    def __str__(self) -> str:
        raise NotImplementedError

    def as_z3(self):
        raise NotImplementedError

    @staticmethod
    def from_ast(ast: AstNode, env: Environment) -> "GenericExpr":
        if ast.type in (AstType.relational_expression, AstType.equality_expression):
            lhs, op, rhs = ast.children
            assert op.text is not None
            return RelExpr(
                operator=op.text,
                lhs=GenericExpr.from_ast(lhs, env),
                rhs=GenericExpr.from_ast(rhs, env),
            )
        elif ast.type == AstType.IDENTIFIER:
            assert ast.text is not None
            return VarExpr(env.rename(ast.text), env[ast.text])
        elif ast.type in (
            AstType.logical_and_expression,
            AstType.logical_or_expression,
        ):
            operator = ast[1].text
            assert operator is not None
            return BinBoolExpr(
                operator=operator,
                lhs=GenericExpr.from_ast(ast[0], env),
                rhs=GenericExpr.from_ast(ast[2], env),
            )
        elif ast.type == AstType.primary_expression:
            return GenericExpr.from_ast(ast[1], env)
        elif ast.type == AstType.postfix_expression:
            if ast[1].type == AstType.paren_left and ast[0].type == AstType.IDENTIFIER:
                assert ast[0].text is not None
                if ast[0].text in ("forall", "exists"):
                    quantifier = ast[0].text
                    args = ast[2]
                    var = args[0][0].text
                    domain = args[0][2]
                    if domain.type == AstType.IDENTIFIER:
                        domain = Type(domain.text)
                    else:
                        domain = (
                            GenericExpr.from_ast(domain[2][0], env),
                            GenericExpr.from_ast(domain[2][2], env),
                        )
                    assert var is not None
                    env.open_scope()
                    ty = domain if isinstance(domain, Type) else Type.int
                    env[var] = ty
                    # TODO: is there a better way to exclude quantified variables
                    del env.vars[env.rename(var)]
                    prop = GenericExpr.from_ast(args[2], env)
                    var_name = env.rename(var)
                    env.close_scope()
                    if quantifier == "forall":
                        return ForAll(
                            var=VarExpr(var_name, ty), domain=domain, prop=prop
                        )
                    elif quantifier == "exists":
                        return Exists(
                            var=VarExpr(var_name, ty), domain=domain, prop=prop
                        )
                    else:
                        assert False, f"unknown quantifier {quantifier}"
                elif ast[0].text == "then":
                    args = ast[2]
                    return Then(
                        if_=GenericExpr.from_ast(args[0], env),
                        then=GenericExpr.from_ast(args[2], env),
                    )
                    # TODO? add an optional `else_` to `Then`
                else:
                    assert False, f"unknown function {ast[0].text}"

            assert ast[1].type == AstType.bracket_left
            return ArraySelect(
                array=GenericExpr.from_ast(ast[0], env),
                index=Expr.from_ast(ast[2], env),
            )
        elif ast.type == AstType.CONSTANT:
            assert ast.text is not None
            if ast.text in ("true", "false",):
                return BoolValue(ast.text == "true")
            else:
                return NumericExpr(ast.text)
        elif ast.type in (
            AstType.additive_expression,
            AstType.multiplicative_expression,
            AstType.shift_expression,
            AstType.and_expression,
            AstType.exclusive_or_expression,
            AstType.inclusive_or_expression,
        ):
            assert ast[1].text is not None
            return BinExpr(
                operator=ast[1].text,
                lhs=GenericExpr.from_ast(ast[0], env),
                rhs=GenericExpr.from_ast(ast[2], env),
            )
        elif ast.type == AstType.unary_expression:
            op = ast[0].text
            assert op is not None
            if op == "!":
                return NotBoolExpr(BoolExpr.from_ast(ast[1], env))
            else:
                return UnaryExpr(operator=op, operand=Expr.from_ast(ast[1], env))
        else:
            assert False, f"unknown type {ast.type.value}"


@dataclass(frozen=True)
class BoolExpr(GenericExpr):
    def assign(self, vars: Dict[str, GenericExpr]) -> "BoolExpr":
        raise NotImplementedError


@dataclass(frozen=True)
class RelExpr(BoolExpr):
    operator: str  # == != < <= > >=
    lhs: GenericExpr
    rhs: GenericExpr

    SYM2OPERATOR: ClassVar[Dict[str, Callable[[Any, Any], Any]]] = {
        "==": operator.eq,
        "!=": operator.ne,
        "<": operator.lt,
        "<=": operator.le,
        ">": operator.gt,
        ">=": operator.ge,
    }

    def assign(self, vars: Dict[str, GenericExpr]) -> "RelExpr":
        return RelExpr(
            operator=self.operator, lhs=self.lhs.assign(vars), rhs=self.rhs.assign(vars)
        )

    def __str__(self) -> str:
        op = {"<=": "≤", ">=": "≥", "==": "=", "!=": "≠"}.get(
            self.operator, self.operator
        )
        return f"{self.lhs} {op} {self.rhs}"

    def as_z3(self):
        return self.SYM2OPERATOR[self.operator](self.lhs.as_z3(), self.rhs.as_z3())


@dataclass(frozen=True)
class BinBoolExpr(BoolExpr):
    operator: str  # && ||
    lhs: GenericExpr
    rhs: GenericExpr

    SYM2OPERATOR: ClassVar[Dict[str, Callable[[Any, Any], Any]]] = {
        "&&": z3.And,
        "||": z3.Or,
    }

    def assign(self, vars: Dict[str, GenericExpr]) -> "BinBoolExpr":
        return BinBoolExpr(
            operator=self.operator, rhs=self.rhs.assign(vars), lhs=self.lhs.assign(vars)
        )

    def __str__(self) -> str:
        if self.operator == "&&":
            return " ∧ ".join(
                f"{p}"
                if isinstance(p, BinBoolExpr)
                and p.operator == "&&"
                or isinstance(p, NotBoolExpr)
                else f"({p})"
                for p in [self.lhs, self.rhs]
            )
        elif self.operator == "||":
            return " ∨ ".join(
                f"{p}"
                if isinstance(p, BinBoolExpr) or isinstance(p, NotBoolExpr)
                else f"({p})"
                for p in [self.lhs, self.rhs]
            )
        else:
            assert False

    def as_z3(self):
        return self.SYM2OPERATOR[self.operator](self.lhs.as_z3(), self.rhs.as_z3())


@dataclass(frozen=True)
class NotBoolExpr(BoolExpr):
    operand: GenericExpr

    def assign(self, vars: Dict[str, GenericExpr]) -> "NotBoolExpr":
        return NotBoolExpr(operand=self.operand.assign(vars))

    def __str__(self) -> str:
        return f"¬({self.operand})"

    def as_z3(self):
        return z3.Not(self.operand.as_z3())


@dataclass(frozen=True)
class Expr(GenericExpr):
    def assign(self, vars: Dict[str, GenericExpr]) -> "Expr":
        raise NotImplementedError


@dataclass(frozen=True)
class VarExpr(Expr):
    var: str
    type_: Type

    def assign(self, vars: Dict[str, Expr]) -> Expr:
        return vars.get(self.var, self)

    def __str__(self) -> str:
        return self.var

    def as_z3(self):
        # TODO: add more types
        if self.type_ == Type.int:
            return z3.Int(self.var)
        elif self.type_ == Type.float:
            return z3.Const(self.var, z3.FloatDouble())
        elif self.type_ == Type.bool:
            return z3.Bool(self.var)
        elif self.type_ == Type.array_int:
            return z3.Array(self.var, z3.IntSort(), z3.IntSort())
        elif self.type_ == Type.array_bool:
            return z3.Array(self.var, z3.IntSort(), z3.BoolSort())
        elif self.type_ == Type.array_float:
            return z3.Array(self.var, z3.IntSort(), z3.FloatDouble())
        else:
            assert False, f"unknown type: {self.type_}"


@dataclass(frozen=True)
class BinExpr(Expr):
    operator: str  # + - * / % << >> ^ & |
    lhs: GenericExpr
    rhs: GenericExpr

    SYM2OPERATOR: ClassVar[Dict[str, Callable[[Any, Any], Any]]] = {
        "+": operator.add,
        "-": operator.sub,
        "/": operator.floordiv,
        "%": operator.mod,
        "*": operator.mul,
        # "^": operator.xor,
        # "&": operator.and_,
        # "|": operator.or_,
        # ">>": operator.rshift,
        # "<<": operator.lshift,
    }

    def assign(self, vars: Dict[str, GenericExpr]) -> "BinExpr":
        return BinExpr(
            operator=self.operator, rhs=self.rhs.assign(vars), lhs=self.lhs.assign(vars)
        )

    def __str__(self) -> str:
        if self.operator in "*/%":
            return (
                (
                    f"({self.lhs})"
                    if isinstance(self.lhs, BinExpr) and self.lhs.operator in "+-"
                    else f"{self.lhs}"
                )
                + " "
                + self.operator
                + " "
                + (
                    f"({self.rhs})"
                    if isinstance(self.rhs, BinExpr)
                    and self.rhs.operator != self.operator
                    else f"{self.rhs}"
                )
            )
        elif self.operator in "+-":
            return f"{self.lhs} {self.operator} {self.rhs}"
        else:
            assert False

    def as_z3(self):
        return self.SYM2OPERATOR[self.operator](self.lhs.as_z3(), self.rhs.as_z3())


@dataclass(frozen=True)
class UnaryExpr(Expr):
    operator: str  # + - ~
    operand: GenericExpr

    SYM2OPERATOR: ClassVar[Dict[str, Callable[[Any], Any]]] = {
        "+": operator.pos,
        "-": operator.neg,
        # "~": operator.inv,
    }

    def assign(self, vars: Dict[str, GenericExpr]) -> "UnaryExpr":
        return UnaryExpr(operator=self.operator, operand=self.operand.assign(vars))

    def __str__(self) -> str:
        return self.operator + (
            f"({self.operand})"
            if isinstance(self.operand, BinExpr)
            else f"{self.operand}"
        )

    def as_z3(self):
        return self.SYM2OPERATOR[self.operator](self.operand.as_z3())


@dataclass(frozen=True)
class NumericExpr(Expr):
    number: str

    def assign(self, vars: Dict[str, GenericExpr]) -> "NumericExpr":
        return self

    def __str__(self) -> str:
        return f"{self.number}"

    def as_z3(self):
        try:
            return z3.IntVal(int(self.number))
        except ValueError:
            return float(self.number)


@dataclass(frozen=True)
class BoolValue(BoolExpr):
    value: bool

    def assign(self, vars: Dict[str, GenericExpr]) -> "BoolValue":
        return self

    def __str__(self) -> str:
        return f"{self.value}"

    def as_z3(self):
        return self.value


@dataclass(frozen=True)
class ArrayStore(Expr):
    array: GenericExpr
    index: GenericExpr
    value: GenericExpr

    def assign(self, vars: Dict[str, GenericExpr]) -> "ArrayStore":
        return ArrayStore(
            array=self.array.assign(vars),
            index=self.index.assign(vars),
            value=self.value.assign(vars),
        )

    def __str__(self) -> str:
        return f"Store({self.array}, {self.index}, {self.value})"

    def as_z3(self):
        return z3.Store(self.array.as_z3(), self.index.as_z3(), self.value.as_z3())


@dataclass(frozen=True)
class ArraySelect(Expr):
    array: GenericExpr
    index: GenericExpr

    def assign(self, vars: Dict[str, GenericExpr]) -> "ArraySelect":
        return ArraySelect(array=self.array.assign(vars), index=self.index.assign(vars))

    def __str__(self) -> str:
        return f"{self.array}[{self.index}]"

    def as_z3(self):
        return z3.Select(self.array.as_z3(), self.index.as_z3())


@dataclass(frozen=True)
class Prop(GenericExpr):
    def assign(self, vars: Dict[str, GenericExpr]) -> "Prop":
        raise NotImplementedError

    def __str__(self) -> str:
        raise NotImplementedError

    def as_z3(self):
        raise NotImplementedError


@dataclass(frozen=True)
class Then(Prop):
    if_: GenericExpr
    then: GenericExpr

    def assign(self, vars: Dict[str, GenericExpr]) -> Prop:
        return Then(if_=self.if_.assign(vars), then=self.then.assign(vars))

    def __str__(self) -> str:
        res = f"{self.if_} → "
        if isinstance(self.then, (Then, ForAll, Exists)):
            res += f"({self.then})"
        else:
            res += f"{self.then}"
        return res

    def as_z3(self):
        return z3.Implies(self.if_.as_z3(), self.then.as_z3())


@dataclass(frozen=True)
class ForAll(Prop):
    var: VarExpr
    domain: Union[Tuple[GenericExpr, GenericExpr], Type]
    prop: GenericExpr

    def assign(self, vars: Dict[str, GenericExpr]) -> Prop:
        if self.var in vars:
            vars = vars.copy()
            del vars[self.var.var]
        domain = self.domain
        if isinstance(domain, tuple):
            domain = (domain[0].assign(vars), domain[1].assign(vars))
        return ForAll(var=self.var, domain=domain, prop=self.prop.assign(vars))

    def __str__(self) -> str:
        domain = (
            self.domain.value
            if isinstance(self.domain, Type)
            else "({},{})".format(*self.domain)
        )
        return f"∀{self.var.var}∈{domain}.{self.prop}"

    def as_z3(self):
        if isinstance(self.domain, Type):
            return z3.ForAll([self.var.as_z3()], self.prop.as_z3())
        else:
            var = self.var.as_z3()
            return z3.ForAll(
                [var],
                z3.Implies(
                    z3.And(var >= self.domain[0].as_z3(), var < self.domain[1].as_z3()),
                    self.prop.as_z3(),
                ),
            )


@dataclass(frozen=True)
class Exists(Prop):
    var: VarExpr
    domain: Union[Tuple[GenericExpr, GenericExpr], Type]
    prop: GenericExpr

    def assign(self, vars: Dict[str, GenericExpr]) -> Prop:
        if self.var in vars:
            vars = vars.copy()
            del vars[self.var.var]
        domain = self.domain
        if isinstance(domain, tuple):
            domain = (domain[0].assign(vars), domain[1].assign(vars))
        return Exists(var=self.var, domain=domain, prop=self.prop.assign(vars))

    def __str__(self) -> str:
        domain = (
            self.domain.value
            if isinstance(self.domain, Type)
            else "({},{})".format(*self.domain)
        )
        return f"∃{self.var.var}∈{domain}.{self.prop}"

    def as_z3(self):
        if isinstance(self.domain, Type):
            return z3.Exists([self.var.as_z3()], self.prop.as_z3())
        else:
            var = self.var.as_z3()
            return z3.Exists(
                [var],
                z3.Implies(
                    z3.And(var >= self.domain[0].as_z3(), var < self.domain[1].as_z3()),
                    self.prop.as_z3(),
                ),
            )
