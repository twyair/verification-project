from dataclasses import dataclass
from typing import Dict, FrozenSet, Set, Tuple, Union
from expr import BinBoolExpr, BoolExpr, RelExpr, Expr
from cast import AstNode, AstType


@dataclass
class Prop:
    @staticmethod
    def from_ast(ast: AstNode) -> "Prop":
        if ast.type in (AstType.relational_expression, AstType.equality_expression):
            lhs, op, rhs = ast.children
            assert op.text is not None
            return RelProp(
                RelExpr(
                    operator=op.text, lhs=Expr.from_ast(lhs), rhs=Expr.from_ast(rhs),
                )
            )
        elif ast.type in (
            AstType.logical_and_expression,
            AstType.logical_or_expression,
        ):
            lhs = Prop.from_ast(ast[0])
            rhs = Prop.from_ast(ast[2])
            if ast.type == AstType.logical_and_expression:
                return And(lhs, rhs)
            else:
                return Or(lhs, rhs)
        elif ast.type == AstType.unary_expression:
            assert ast[0].text == "!"
            return Not(Prop.from_ast(ast[1]))
        elif ast.type == AstType.primary_expression:
            return Prop.from_ast(ast[1])
        elif ast.type == AstType.postfix_expression:
            assert (
                ast[1].type == AstType.paren_left
                and ast[0].type == AstType.IDENTIFIER
            )
            if ast[0].text == "forall":
                args = ast[2]
                var = args[0][0].text
                domain = args[0][2]
                # FIXME: currently it assumes that the domain is like `range(_,_)`
                start = Expr.from_ast(domain[2][0])
                end = Expr.from_ast(domain[2][2])
                assert var is not None
                return ForAll(
                    var=var, domain=(start, end), prop=Prop.from_ast(args[2]),
                )
            else:
                raise NotImplementedError
        else:
            raise NotImplementedError

    @staticmethod
    def from_expr(expr: BoolExpr) -> "Prop":
        if isinstance(expr, BinBoolExpr):
            if expr.operator == "&&":
                return And(Prop.from_expr(expr.lhs), Prop.from_expr(expr.rhs))
            else:
                return Or(Prop.from_expr(expr.lhs), Prop.from_expr(expr.rhs))
        elif isinstance(expr, RelExpr):
            return RelProp(expr)
        else:
            assert False

    def assign(self, vars: Dict[str, Expr]) -> "Prop":
        raise NotImplementedError

    def free_vars(self, bound_vars: FrozenSet[str]) -> Set[str]:
        raise NotImplementedError

    def __str__(self) -> str:
        raise NotImplementedError


@dataclass
class Then(Prop):
    if_: Prop
    then: Prop

    def assign(self, vars: Dict[str, Expr]) -> Prop:
        return Then(if_=self.if_.assign(vars), then=self.then.assign(vars))

    def free_vars(self, bound_vars: FrozenSet[str]) -> Set[str]:
        return self.if_.free_vars(bound_vars) | self.then.free_vars(bound_vars)

    def __str__(self) -> str:
        res = f"{self.if_} → "
        if isinstance(self.then, (Then, ForAll, Exists)):
            res += f"({self.then})"
        else:
            res += f"{self.then}"
        return res


@dataclass
class ForAll(Prop):
    var: str
    domain: Union[Tuple[Expr, Expr], str]
    prop: Prop

    def assign(self, vars: Dict[str, Expr]) -> Prop:
        if self.var in vars:
            vars = vars.copy()
            del vars[self.var]
        return ForAll(var=self.var, domain=self.domain, prop=self.prop.assign(vars))

    def free_vars(self, bound_vars: FrozenSet[str]) -> Set[str]:
        bound_vars |= {self.var}
        return self.prop.free_vars(bound_vars) | ((
            (self.domain[0].vars() | self.domain[1].vars()) - bound_vars
        ) if not isinstance(self.domain, str) else set())

    def __str__(self) -> str:
        return (f"∀{self.var}∈"
            + (self.domain if isinstance(self.domain, str) else "({},{})".format(*self.domain))
            + f".{self.prop}"
        )


@dataclass
class Exists(Prop):
    var: str
    domain: str
    prop: Prop

    def assign(self, vars: Dict[str, Expr]) -> Prop:
        if self.var in vars:
            vars = vars.copy()
            del vars[self.var]
        return Exists(var=self.var, domain=self.domain, prop=self.prop.assign(vars))

    def free_vars(self, bound_vars: FrozenSet[str]) -> Set[str]:
        return self.prop.free_vars(bound_vars | {self.var})

    def __str__(self) -> str:
        return f"∃{self.var}∈{self.domain}. {self.prop}"


@dataclass
class And(Prop):
    lhs: Prop
    rhs: Prop

    def assign(self, vars: Dict[str, Expr]) -> Prop:
        return And(lhs=self.lhs.assign(vars), rhs=self.rhs.assign(vars))

    def free_vars(self, bound_vars: FrozenSet[str]) -> Set[str]:
        return self.lhs.free_vars(bound_vars) | self.rhs.free_vars(bound_vars)

    def __str__(self) -> str:
        return " ∧ ".join(
            f"{x}" if isinstance(x, (And, Not)) else f"({x})"
            for x in [self.lhs, self.rhs]
        )


@dataclass
class Or(Prop):
    lhs: Prop
    rhs: Prop

    def assign(self, vars: Dict[str, Expr]) -> Prop:
        return Or(lhs=self.lhs.assign(vars), rhs=self.rhs.assign(vars))

    def free_vars(self, bound_vars: FrozenSet[str]) -> Set[str]:
        return self.lhs.free_vars(bound_vars) | self.rhs.free_vars(bound_vars)

    def __str__(self) -> str:
        return " ∨ ".join(
            f"({x})" if isinstance(x, (RelProp, ForAll, Exists)) else f"{x}"
            for x in [self.lhs, self.rhs]
        )


@dataclass
class Not(Prop):
    prop: Prop

    def assign(self, vars: Dict[str, Expr]) -> Prop:
        return Not(self.prop.assign(vars))

    def free_vars(self, bound_vars: FrozenSet[str]) -> Set[str]:
        return self.prop.free_vars(bound_vars)

    def __str__(self) -> str:
        return f"¬({self.prop})"


@dataclass
class RelProp(Prop):
    expr: RelExpr

    def assign(self, vars: Dict[str, Expr]) -> Prop:
        return RelProp(self.expr.assign(vars))

    def free_vars(self, bound_vars: FrozenSet[str]) -> Set[str]:
        return self.expr.vars() - bound_vars

    def __str__(self) -> str:
        return f"{self.expr}"
