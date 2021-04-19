from typing import Dict, Iterator, List, Tuple, cast
from cast import AstNode
from dataclasses import dataclass
from expr import (
    BoolExpr,
    BinBoolExpr,
    NotBoolExpr,
    Expr,
    BinExpr,
    UnaryExpr,
    VarExpr,
    RelExpr,
)


R = List[BoolExpr]
T = Dict[str, Expr]


@dataclass
class CfgNode:
    def generate_rt(self, r: R, t: T) -> Iterator[Tuple[R, T]]:
        raise NotImplementedError


@dataclass
class StartNode(CfgNode):
    next_node: CfgNode

    def generate_rt(self, r: R, t: T) -> Iterator[Tuple[R, T]]:
        yield from self.next_node.generate_rt(r, t)


@dataclass
class EndNode(CfgNode):
    def generate_rt(self, r: R, t: T) -> Iterator[Tuple[R, T]]:
        yield (r, t)


@dataclass
class CondNode(CfgNode):
    condition: BoolExpr
    true_br: CfgNode
    false_br: CfgNode

    def generate_rt(self, r: R, t: T) -> Iterator[Tuple[R, T]]:
        condition = self.condition.assign(t)
        yield from self.true_br.generate_rt(r + [condition], t)
        yield from self.false_br.generate_rt(r + [cast(BoolExpr, NotBoolExpr(condition))], t)


@dataclass
class AssignmentNode(CfgNode):
    expression: Expr
    var: VarExpr
    next_node: CfgNode

    def generate_rt(self, r: R, t: T) -> Iterator[Tuple[R, T]]:
        t_next = t.copy()
        t_next[self.var.var] = self.expression.assign(t)
        yield from self.next_node.generate_rt(r, t_next)


def create_cfg(ast: AstNode) -> CfgNode:
    pass
