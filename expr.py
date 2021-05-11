import enum
import operator
from collections import defaultdict
from dataclasses import dataclass
from typing import Any, Callable, ClassVar, DefaultDict, Dict, List, Tuple, Union

import z3

from cast import AstNode, AstType


@enum.unique
class Type(enum.Enum):
    int = "int"
    float = "float"
    bool = "bool"
    array_int = "array_int"
    array_float = "array_float"
    array_bool = "array_bool"

    def as_z3(self):
        if self == Type.int:
            return z3.IntSort()
        elif self == Type.float:
            return z3.FloatDouble()
        elif self == Type.bool:
            return z3.BoolSort()
        elif self == Type.array_int:
            return z3.ArraySort(z3.IntSort(), z3.IntSort())
        elif self == Type.array_bool:
            return z3.ArraySort(z3.IntSort(), z3.BoolSort())
        elif self == Type.array_float:
            return z3.ArraySort(z3.IntSort(), z3.FloatDouble())
        else:
            assert False, f"unknown type: {self}"


@dataclass(frozen=True)
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
class Expr:
    def assign(self, vars: Dict[str, "Expr"]) -> "Expr":
        raise NotImplementedError

    def __str__(self) -> str:
        raise NotImplementedError

    def as_z3(self):
        raise NotImplementedError

    def get_type(self) -> Type:
        raise NotImplementedError

    @staticmethod
    def from_ast(ast: AstNode, env: Environment) -> "Expr":
        if ast.type in (AstType.relational_expression, AstType.equality_expression):
            lhs, op, rhs = ast.children
            assert op.text is not None
            return RelExpr(
                operator=op.text,
                lhs=Expr.from_ast(lhs, env),
                rhs=Expr.from_ast(rhs, env),
            )
        elif ast.type == AstType.IDENTIFIER:
            assert ast.text is not None
            if ast.text in ("true", "false"):
                return BoolValue(ast.text == "true")
            return Variable(env.rename(ast.text), env[ast.text])
        elif ast.type == AstType.logical_and_expression:
            return And((Expr.from_ast(ast[0], env), Expr.from_ast(ast[2], env)))
        elif ast.type == AstType.logical_or_expression:
            return Or((Expr.from_ast(ast[0], env), Expr.from_ast(ast[2], env)))
        elif ast.type == AstType.primary_expression:
            return Expr.from_ast(ast[1], env)
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
                            Expr.from_ast(domain[2][0], env),
                            Expr.from_ast(domain[2][2], env),
                        )
                    assert var is not None
                    env.open_scope()
                    ty = domain if isinstance(domain, Type) else Type.int
                    env[var] = ty
                    # TODO: is there a better way to exclude quantified variables
                    del env.vars[env.rename(var)]
                    prop = Expr.from_ast(args[2], env)
                    var_name = env.rename(var)
                    env.close_scope()
                    if quantifier == "forall":
                        if isinstance(domain, tuple):
                            return ForAllRange(
                                var=Variable(var_name, ty), range=domain, prop=prop
                            )
                        else:
                            return ForAll(vars=[Variable(var_name, ty)], prop=prop)
                    elif quantifier == "exists":
                        return Exists(
                            var=Variable(var_name, ty), domain=domain, prop=prop
                        )
                    else:
                        assert False, f"unknown quantifier {quantifier}"
                elif ast[0].text == "then":
                    args = ast[2]
                    if args[0].type == AstType.argument_expression_list:
                        return IfThenElse(
                            Expr.from_ast(args[0][0], env),
                            Expr.from_ast(args[0][2], env),
                            Expr.from_ast(args[2], env),
                        )
                    else:
                        return Then(
                            if_=Expr.from_ast(args[0], env),
                            then=Expr.from_ast(args[2], env),
                        )
                    # TODO? add an optional `else_` to `Then`
                else:
                    assert False, f"unknown function {ast[0].text}"

            assert ast[1].type == AstType.bracket_left
            return ArraySelect(
                array=Expr.from_ast(ast[0], env), index=Expr.from_ast(ast[2], env),
            )
        elif ast.type == AstType.CONSTANT:
            assert ast.text is not None
            if ast.text in ("true", "false",):
                return BoolValue(ast.text == "true")
            elif ast.text.isnumeric():
                return IntValue(int(ast.text))
            else:
                return RealValue(float(ast.text))
        elif ast.type in (
            AstType.additive_expression,
            AstType.multiplicative_expression,
            AstType.shift_expression,
            AstType.and_expression,
            AstType.exclusive_or_expression,
            AstType.inclusive_or_expression,
        ):
            assert ast[1].text is not None
            return BinaryExpr(
                operator=ast[1].text,
                lhs=Expr.from_ast(ast[0], env),
                rhs=Expr.from_ast(ast[2], env),
            )
        elif ast.type == AstType.unary_expression:
            op = ast[0].text
            assert op is not None
            if op == "!":
                return Not(Expr.from_ast(ast[1], env))
            else:
                return UnaryExpr(operator=op, operand=Expr.from_ast(ast[1], env))
        elif ast.type == AstType.conditional_expression:
            return IfThenElse(
                condition=Expr.from_ast(ast[0], env),
                value_true=Expr.from_ast(ast[2], env),
                value_false=Expr.from_ast(ast[4], env),
            )
        elif ast.type == AstType.cast_expression:
            ty = Type(ast[1].text)
            expr = Expr.from_ast(ast[3], env)
            if ty == Type.int:
                return AsInt(expr)
            elif ty == Type.float:
                return AsReal(expr)
            else:
                assert False, f"can't cast expr to type {ty}"
        else:
            assert False, f"unknown type {ast.type.value}"


@dataclass(frozen=True)
class RelExpr(Expr):
    operator: str  # == != < <= > >=
    lhs: Expr
    rhs: Expr

    SYM2OPERATOR: ClassVar[Dict[str, Callable[[Any, Any], Any]]] = {
        "==": operator.eq,
        "!=": operator.ne,
        "<": operator.lt,
        "<=": operator.le,
        ">": operator.gt,
        ">=": operator.ge,
    }
    SYM2PRETTY: ClassVar[Dict[str, str]] = {"<=": "≤", ">=": "≥", "==": "=", "!=": "≠"}

    def assign(self, vars: Dict[str, Expr]) -> "RelExpr":
        return RelExpr(
            operator=self.operator, lhs=self.lhs.assign(vars), rhs=self.rhs.assign(vars)
        )

    def __str__(self) -> str:
        op = self.SYM2PRETTY.get(self.operator, self.operator)
        return f"{self.lhs} {op} {self.rhs}"

    def as_z3(self) -> z3.ExprRef:
        return self.SYM2OPERATOR[self.operator](self.lhs.as_z3(), self.rhs.as_z3())

    def get_type(self) -> Type:
        return Type.bool


@dataclass(frozen=True)
class And(Expr):
    args: Tuple[Expr, ...]

    def assign(self, vars: Dict[str, Expr]) -> "And":
        return And(args=tuple(a.assign(vars) for a in self.args))

    def __str__(self) -> str:
        return " ∧ ".join(
            f"{p}" if isinstance(p, (And, Not, Variable, BoolValue)) else f"({p})"
            for p in self.args
        )

    def as_z3(self):
        return z3.And(*(a.as_z3() for a in self.args))

    def get_type(self) -> Type:
        return Type.bool


@dataclass(frozen=True)
class Or(Expr):
    args: Tuple[Expr, ...]

    def assign(self, vars: Dict[str, Expr]) -> "Or":
        return Or(tuple(a.assign(vars) for a in self.args))

    def __str__(self) -> str:
        return " ∨ ".join(
            f"{p}" if isinstance(p, (And, Or, Not, Variable, BoolValue)) else f"({p})"
            for p in self.args
        )

    def as_z3(self):
        return z3.Or(*(a.as_z3() for a in self.args))

    def get_type(self) -> Type:
        return Type.bool


@dataclass(frozen=True)
class Not(Expr):
    operand: Expr

    def assign(self, vars: Dict[str, Expr]) -> "Not":
        return Not(operand=self.operand.assign(vars))

    def __str__(self) -> str:
        return f"¬({self.operand})"

    def as_z3(self):
        return z3.Not(self.operand.as_z3())

    def get_type(self) -> Type:
        return Type.bool


@dataclass(frozen=True)
class Variable(Expr):
    var: str
    type_: Type

    def assign(self, vars: Dict[str, Expr]) -> Expr:
        return vars.get(self.var, self)

    def __str__(self) -> str:
        return self.var

    def as_z3(self) -> z3.ExprRef:
        return z3.Const(self.var, self.type_.as_z3())

    def get_type(self) -> Type:
        return self.type_


@dataclass(frozen=True)
class BinaryExpr(Expr):
    operator: str  # + - * / % << >> ^ & |
    lhs: Expr
    rhs: Expr

    SYM2OPERATOR: ClassVar[Dict[str, Callable[[Any, Any], Any]]] = {
        "+": operator.add,
        "-": operator.sub,
        "/": operator.truediv,  # NOTE: truediv for z3 integer expressions performs integer division (floordiv isn't defined)
        "%": operator.mod,
        "*": operator.mul,
        # "^": operator.xor,
        # "&": operator.and_,
        # "|": operator.or_,
        # ">>": operator.rshift,
        # "<<": operator.lshift,
    }

    def assign(self, vars: Dict[str, Expr]) -> "BinaryExpr":
        return BinaryExpr(
            operator=self.operator, rhs=self.rhs.assign(vars), lhs=self.lhs.assign(vars)
        )

    def __str__(self) -> str:
        if self.operator in "*/%":
            return (
                (
                    f"({self.lhs})"
                    if isinstance(self.lhs, BinaryExpr) and self.lhs.operator in "+-"
                    else f"{self.lhs}"
                )
                + " "
                + self.operator
                + " "
                + (
                    f"({self.rhs})"
                    if isinstance(self.rhs, BinaryExpr)
                    and self.rhs.operator != self.operator
                    else f"{self.rhs}"
                )
            )
        elif self.operator in "+-":
            return f"{self.lhs} {self.operator} {self.rhs}"
        else:
            assert False

    def as_z3(self) -> z3.ExprRef:
        return self.SYM2OPERATOR[self.operator](self.lhs.as_z3(), self.rhs.as_z3())

    def get_type(self) -> Type:
        return self.lhs.get_type()


@dataclass(frozen=True)
class UnaryExpr(Expr):
    operator: str  # + - ~
    operand: Expr

    SYM2OPERATOR: ClassVar[Dict[str, Callable[[Any], Any]]] = {
        "+": operator.pos,
        "-": operator.neg,
        # "~": operator.inv,
    }

    def assign(self, vars: Dict[str, Expr]) -> "UnaryExpr":
        return UnaryExpr(operator=self.operator, operand=self.operand.assign(vars))

    def __str__(self) -> str:
        return self.operator + (
            f"({self.operand})"
            if isinstance(self.operand, BinaryExpr)
            else f"{self.operand}"
        )

    def as_z3(self) -> z3.ExprRef:
        return self.SYM2OPERATOR[self.operator](self.operand.as_z3())

    def get_type(self) -> Type:
        return self.operand.get_type()


@dataclass(frozen=True)
class AsInt(Expr):
    expr: Expr

    def assign(self, vars: Dict[str, Expr]) -> "AsInt":
        return AsInt(self.expr.assign(vars))

    def __str__(self) -> str:
        return f"int({self.expr})"

    def as_z3(self):
        return z3.ToInt(self.expr.as_z3())

    def get_type(self) -> Type:
        return Type.int


@dataclass(frozen=True)
class AsReal(Expr):
    expr: Expr

    def assign(self, vars: Dict[str, Expr]) -> "AsReal":
        return AsReal(self.expr.assign(vars))

    def __str__(self) -> str:
        return f"real({self.expr})"

    def as_z3(self):
        return z3.ToReal(self.expr.as_z3())

    def get_type(self) -> Type:
        return Type.float


@dataclass(frozen=True)
class IntValue(Expr):
    number: int

    def assign(self, vars: Dict[str, Expr]) -> "IntValue":
        return self

    def __str__(self) -> str:
        return f"{self.number}"

    def as_z3(self) -> z3.ExprRef:
        return z3.IntVal(int(self.number))

    def get_type(self) -> Type:
        return Type.int


@dataclass(frozen=True)
class RealValue(Expr):
    number: float

    def assign(self, vars: Dict[str, Expr]) -> "RealValue":
        return self

    def __str__(self) -> str:
        return f"{self.number}"

    def as_z3(self) -> z3.ExprRef:
        return z3.FPVal(self.number)

    def get_type(self) -> Type:
        return Type.float


@dataclass(frozen=True)
class BoolValue(Expr):
    value: bool

    def assign(self, vars: Dict[str, Expr]) -> "BoolValue":
        return self

    def __str__(self) -> str:
        return f"{self.value}"

    def as_z3(self) -> z3.ExprRef:
        return z3.BoolVal(self.value)

    def get_type(self) -> Type:
        return Type.bool


@dataclass(frozen=True)
class IfThenElse(Expr):
    condition: Expr
    value_true: Expr
    value_false: Expr

    def assign(self, vars: Dict[str, Expr]) -> "IfThenElse":
        return IfThenElse(
            condition=self.condition.assign(vars),
            value_true=self.value_true.assign(vars),
            value_false=self.value_false.assign(vars),
        )

    def __str__(self) -> str:
        return f"({self.condition}?{{{self.value_true}}}:{{{self.value_false}}})"

    def as_z3(self):
        return z3.If(
            self.condition.as_z3(), self.value_true.as_z3(), self.value_false.as_z3()
        )

    def get_type(self) -> Type:
        return Type.bool


@dataclass(frozen=True)
class ArrayStore(Expr):
    array: Expr
    index: Expr
    value: Expr

    def assign(self, vars: Dict[str, Expr]) -> "ArrayStore":
        return ArrayStore(
            array=self.array.assign(vars),
            index=self.index.assign(vars),
            value=self.value.assign(vars),
        )

    def __str__(self) -> str:
        return f"Store({self.array}, {self.index}, {self.value})"

    def as_z3(self) -> z3.ExprRef:
        return z3.Store(self.array.as_z3(), self.index.as_z3(), self.value.as_z3())

    def get_type(self) -> Type:
        ty = self.array.get_type()
        if ty == Type.array_int:
            return Type.int
        elif ty == Type.array_float:
            return Type.float
        elif ty == Type.array_bool:
            return Type.bool
        else:
            assert False


@dataclass(frozen=True)
class ArraySelect(Expr):
    array: Expr
    index: Expr

    def assign(self, vars: Dict[str, Expr]) -> "ArraySelect":
        return ArraySelect(array=self.array.assign(vars), index=self.index.assign(vars))

    def __str__(self) -> str:
        return f"{self.array}[{self.index}]"

    def as_z3(self) -> z3.ExprRef:
        return z3.Select(self.array.as_z3(), self.index.as_z3())

    def get_type(self) -> Type:
        ty = self.array.get_type()
        if ty == Type.array_int:
            return Type.int
        elif ty == Type.array_float:
            return Type.float
        elif ty == Type.array_bool:
            return Type.bool
        else:
            assert False


@dataclass(frozen=True)
class Prop(Expr):
    pass


@dataclass(frozen=True)
class Then(Prop):
    if_: Expr
    then: Expr

    def assign(self, vars: Dict[str, Expr]) -> Prop:
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
    vars: List[Variable]
    prop: Expr

    def assign(self, vars: Dict[str, Expr]) -> Prop:
        for var in self.vars:
            assert var.var not in vars
        return ForAll(vars=self.vars, prop=self.prop.assign(vars))

    def __str__(self) -> str:
        return (
            "∀"
            + ",".join(f"{var.var}∈{var.type_.value}" for var in self.vars)
            + f".{self.prop}"
        )

    def as_z3(self):
        return z3.ForAll([var.as_z3() for var in self.vars], self.prop.as_z3())


@dataclass(frozen=True)
class ForAllRange(Prop):
    var: Variable
    range: Tuple[Expr, Expr]
    prop: Expr

    def assign(self, vars: Dict[str, Expr]) -> "ForAllRange":
        if self.var in vars:
            vars = vars.copy()
            del vars[self.var.var]
        return ForAllRange(
            var=self.var,
            range=(self.range[0].assign(vars), self.range[1].assign(vars)),
            prop=self.prop.assign(vars),
        )

    def __str__(self) -> str:
        return f"∀{self.var.var}∈({self.range[0]},{self.range[1]}).{self.prop}"

    def as_z3(self):
        var = self.var.as_z3()
        return z3.ForAll(
            [var],
            z3.Implies(
                z3.And(var >= self.range[0].as_z3(), var < self.range[1].as_z3()),
                self.prop.as_z3(),
            ),
        )


@dataclass(frozen=True)
class Exists(Prop):
    var: Variable
    domain: Union[Tuple[Expr, Expr], Type]
    prop: Expr

    def assign(self, vars: Dict[str, Expr]) -> Prop:
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
                z3.And(
                    z3.And(var >= self.domain[0].as_z3(), var < self.domain[1].as_z3()),
                    self.prop.as_z3(),
                ),
            )


@dataclass(frozen=True)
class Predicate(Prop):
    name: str
    arguments: List[Expr]
    sorts: List

    def assign(self, vars: Dict[str, Expr]) -> Prop:
        return Predicate(
            name=self.name,
            arguments=[a.assign(vars) for a in self.arguments],
            sorts=self.sorts,
        )

    def __str__(self) -> str:
        args = ",".join(str(a) for a in self.arguments)
        return f"{self.name}({args})"

    def as_z3(self):
        return z3.Function(self.name, *self.sorts, z3.BoolSort())(
            *(a.as_z3() for a in self.arguments)
        )

