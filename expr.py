from collections import defaultdict
from dataclasses import dataclass
from typing import Callable, DefaultDict, Dict, List, Set, ClassVar
import operator
from cast import AstType, AstNode
import z3


@dataclass
class Environment:
    scopes: List[Dict[str, str]]
    vars: Dict[str, str]
    names_count: DefaultDict[str, int]
    renamer: List[Dict[str, str]]

    @staticmethod
    def empty():
        return Environment(
            scopes=[{}], vars={}, names_count=defaultdict(lambda: 0), renamer=[{}],
        )

    def __getitem__(self, var: str) -> str:
        for scope in reversed(self.scopes):
            if var in scope:
                return scope[var]
        assert False, f"{var} is not in the environment"

    def __setitem__(self, var: str, type_: str) -> None:
        self.scopes[-1][var] = type_
        if self.names_count[var] > 0:
            self.renamer[-1][var] = f"{var}${self.names_count[var]}"
        self.names_count[var] += 1
        self.vars[self.rename(var)] = type_

    def rename(self, var: str) -> str:
        return self.renamer[-1].get(var, var)

    def open_scope(self) -> None:
        self.scopes.append({})
        self.renamer.append({})

    def close_scope(self) -> None:
        self.scopes.pop()
        self.renamer.pop()

    def make_var_expr(self, var: str) -> "VarExpr":
        return VarExpr(self.rename(var), self[var])


@dataclass(frozen=True)
class GenericExpr:
    def assign(self, vars: Dict[str, "Expr"]) -> "GenericExpr":
        raise NotImplementedError

    def vars(self) -> Set[str]:
        raise NotImplementedError

    def __str__(self) -> str:
        raise NotImplementedError

    def as_z3(self, env: Dict[str, str]):
        raise NotImplementedError

    @staticmethod
    def from_ast(ast: AstNode, env: Environment) -> "GenericExpr":
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
            return env.make_var_expr(ast.text)
        elif ast.type in (
            AstType.logical_and_expression,
            AstType.logical_or_expression,
        ):
            operator = ast[1].text
            assert operator is not None
            return BinBoolExpr(
                operator=operator,
                lhs=BoolExpr.from_ast(ast[0], env),
                rhs=BoolExpr.from_ast(ast[2], env),
            )
        elif ast.type == AstType.primary_expression:
            return GenericExpr.from_ast(ast[1], env)
        elif ast.type == AstType.postfix_expression:
            assert ast[1].type == AstType.bracket_left
            return ArrayItemExpr(
                array=Expr.from_ast(ast[0], env), index=Expr.from_ast(ast[2], env)
            )
        elif ast.type == AstType.CONSTANT:
            assert ast.text is not None
            return NumericExpr(int(ast.text))
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
                lhs=Expr.from_ast(ast[0], env),
                rhs=Expr.from_ast(ast[2], env),
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
    def assign(self, vars: Dict[str, "Expr"]) -> "BoolExpr":
        raise NotImplementedError

    @staticmethod
    def from_ast(ast: AstNode, env: Environment) -> "BoolExpr":
        expr = GenericExpr.from_ast(ast, env)
        assert isinstance(expr, BoolExpr)
        return expr


@dataclass(frozen=True)
class RelExpr(BoolExpr):
    operator: str  # == != < <= > >=
    lhs: "Expr"
    rhs: "Expr"

    def assign(self, vars: Dict[str, "Expr"]) -> "RelExpr":
        return RelExpr(
            operator=self.operator, lhs=self.lhs.assign(vars), rhs=self.rhs.assign(vars)
        )

    def vars(self) -> Set[str]:
        return self.lhs.vars() | self.rhs.vars()

    def __str__(self) -> str:
        op = {"<=": "≤", ">=": "≥", "==": "=", "!=": "≠"}.get(
            self.operator, self.operator
        )
        return f"{self.lhs} {op} {self.rhs}"


@dataclass(frozen=True)
class BinBoolExpr(BoolExpr):
    operator: str  # && ||
    lhs: BoolExpr
    rhs: BoolExpr

    def assign(self, vars: Dict[str, "Expr"]) -> "BinBoolExpr":
        return BinBoolExpr(
            operator=self.operator, rhs=self.rhs.assign(vars), lhs=self.lhs.assign(vars)
        )

    def vars(self) -> Set[str]:
        return self.lhs.vars() | self.rhs.vars()

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


@dataclass(frozen=True)
class NotBoolExpr(BoolExpr):
    operand: BoolExpr

    def assign(self, vars: Dict[str, "Expr"]) -> "NotBoolExpr":
        return NotBoolExpr(operand=self.operand.assign(vars))

    def vars(self) -> Set[str]:
        return self.operand.vars()

    def __str__(self) -> str:
        return f"¬({self.operand})"


@dataclass(frozen=True)
class Expr(GenericExpr):
    def assign(self, vars: Dict[str, "Expr"]) -> "Expr":
        raise NotImplementedError

    @staticmethod
    def from_ast(ast: AstNode, env: Environment) -> "Expr":
        expr = GenericExpr.from_ast(ast, env)
        assert isinstance(expr, Expr)
        return expr


@dataclass(frozen=True)
class VarExpr(Expr):
    var: str
    type_: str

    def assign(self, vars: Dict[str, Expr]) -> Expr:
        return vars.get(self.var, self)

    def vars(self) -> Set[str]:
        return {self.var}

    def __str__(self) -> str:
        return self.var

    def as_z3(self, env: Dict[str, str]):
        # TODO: add more types
        if self.type_ == "int":
            return z3.Int(self.var)
        elif self.type_ == "array-int":
            return z3.Array(self.var, z3.IntSort(), z3.IntSort())
        else:
            assert False, f"unknown type: {self.type_}"


@dataclass(frozen=True)
class BinExpr(Expr):
    operator: str  # + - * / % << >> ^ & |
    lhs: Expr
    rhs: Expr

    SYM2OPERATOR: ClassVar[Dict[str, Callable[[int, int], int]]] = {
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

    def assign(self, vars: Dict[str, "Expr"]) -> "BinExpr":
        return BinExpr(
            operator=self.operator, rhs=self.rhs.assign(vars), lhs=self.lhs.assign(vars)
        )

    def vars(self) -> Set[str]:
        return self.lhs.vars() | self.rhs.vars()

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

    def as_z3(self, env: Dict[str, str]):
        return self.SYM2OPERATOR[self.operator](
            self.lhs.as_z3(env), self.rhs.as_z3(env)
        )


@dataclass(frozen=True)
class UnaryExpr(Expr):
    operator: str  # + - ~
    operand: Expr

    SYM2OPERATOR: ClassVar[Dict[str, Callable[[int], int]]] = {
        "+": operator.pos,
        "-": operator.neg,
        # "~": operator.inv,
    }

    def assign(self, vars: Dict[str, "Expr"]) -> "UnaryExpr":
        return UnaryExpr(operator=self.operator, operand=self.operand.assign(vars))

    def vars(self) -> Set[str]:
        return self.operand.vars()

    def __str__(self) -> str:
        return self.operator + (
            f"({self.operand})"
            if isinstance(self.operand, BinExpr)
            else f"{self.operand}"
        )

    def as_z3(self, env: Dict[str, str]):
        return self.SYM2OPERATOR[self.operator](self.operand.as_z3(env))


@dataclass(frozen=True)
class NumericExpr(Expr):
    number: int

    def assign(self, vars: Dict[str, "Expr"]) -> "NumericExpr":
        return self

    def vars(self) -> Set[str]:
        return set()

    def __str__(self) -> str:
        return f"{self.number}"

    def as_z3(self, env: Dict[str, str]):
        return self.number


@dataclass(frozen=True)
class ChangeArrayExpr(Expr):
    array: Expr
    index: Expr
    value: Expr

    def assign(self, vars: Dict[str, "Expr"]) -> "ChangeArrayExpr":
        return ChangeArrayExpr(
            array=self.array.assign(vars),
            index=self.index.assign(vars),
            value=self.value.assign(vars),
        )

    def vars(self) -> Set[str]:
        return self.array.vars() | self.index.vars() | self.value.vars()

    def __str__(self) -> str:
        return f"Store({self.array}, {self.index}, {self.value})"


@dataclass(frozen=True)
class ArrayItemExpr(Expr):
    array: Expr
    index: Expr

    def assign(self, vars: Dict[str, "Expr"]) -> "ArrayItemExpr":
        return ArrayItemExpr(
            array=self.array.assign(vars), index=self.index.assign(vars)
        )

    def vars(self) -> Set[str]:
        return self.array.vars() | self.index.vars()

    def __str__(self) -> str:
        return f"{self.array}[{self.index}]"

    def as_z3(self, env: Dict[str, str]):
        return z3.Select(self.array.as_z3(env), self.index.as_z3(env))
