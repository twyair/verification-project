from dataclasses import dataclass
from typing import Dict


@dataclass(frozen=True)
class BoolExpr:
    def assign(self, vars: Dict[str, "Expr"]) -> "BoolExpr":
        raise NotImplementedError


@dataclass(frozen=True)
class RelExpr(BoolExpr):
    operator: str  # == != < <= > >=
    lhs: "Expr"
    rhs: "Expr"

    def assign(self, vars: Dict[str, "Expr"]) -> "RelExpr":
        return RelExpr(
            operator=self.operator, lhs=self.lhs.assign(vars), rhs=self.rhs.assign(vars)
        )

    def __str__(self) -> str:
        return f"{self.lhs} {self.operator} {self.rhs}"


@dataclass(frozen=True)
class BinBoolExpr(BoolExpr):
    operator: str  # && ||
    lhs: BoolExpr
    rhs: BoolExpr

    def assign(self, vars: Dict[str, "Expr"]) -> "BinBoolExpr":
        return BinBoolExpr(
            operator=self.operator, rhs=self.rhs.assign(vars), lhs=self.lhs.assign(vars)
        )

    def __str__(self) -> str:
        if self.operator == "&&":
            return " && ".join(
                f"{p}"
                if isinstance(p, BinBoolExpr)
                and p.operator == "&&"
                or isinstance(p, NotBoolExpr)
                else f"({p})"
                for p in [self.lhs, self.rhs]
            )
        elif self.operator == "||":
            return " || ".join(
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

    def __str__(self) -> str:
        return f"!({self.operand})"


@dataclass(frozen=True)
class Expr:
    def assign(self, vars: Dict[str, "Expr"]) -> "Expr":
        raise NotImplementedError


@dataclass(frozen=True)
class VarExpr(Expr):
    var: str

    def assign(self, vars: Dict[str, Expr]) -> Expr:
        return vars.get(self.var, self)

    def __str__(self) -> str:
        return self.var


@dataclass(frozen=True)
class BinExpr(Expr):
    operator: str  # + - * / %
    lhs: Expr
    rhs: Expr

    def assign(self, vars: Dict[str, "Expr"]) -> "BinExpr":
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


@dataclass(frozen=True)
class UnaryExpr(Expr):
    operator: str  # + -
    operand: Expr

    def assign(self, vars: Dict[str, "Expr"]) -> "UnaryExpr":
        return UnaryExpr(operator=self.operator, operand=self.operand.assign(vars))

    def __str__(self) -> str:
        return self.operator + (
            f"({self.operand})"
            if isinstance(self.operand, BinExpr)
            else f"{self.operand}"
        )


@dataclass(frozen=True)
class NumericExpr(Expr):
    number: int

    def assign(self, vars: Dict[str, "Expr"]) -> "NumericExpr":
        return self

    def __str__(self) -> str:
        return f"{self.number}"


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

    def __str__(self) -> str:
        return f"{self.array}[{self.index}]"
