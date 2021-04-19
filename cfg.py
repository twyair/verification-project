from typing import Dict, Iterator, List, Tuple, Union, cast
from cast import AstNode, AstType
from dataclasses import dataclass
from expr import (
    ArrayItemExpr,
    BoolExpr,
    BinBoolExpr,
    ChangeArrayExpr,
    NotBoolExpr,
    Expr,
    BinExpr,
    NumericExpr,
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
        yield from self.false_br.generate_rt(
            r + [cast(BoolExpr, NotBoolExpr(condition))], t
        )


@dataclass
class AssignmentNode(CfgNode):
    expression: Expr
    var: VarExpr
    next_node: CfgNode

    def generate_rt(self, r: R, t: T) -> Iterator[Tuple[R, T]]:
        t_next = t.copy()
        t_next[self.var.var] = self.expression.assign(t)
        yield from self.next_node.generate_rt(r, t_next)


def make_expr(ast: AstNode) -> Union[Expr, BoolExpr]:
    if ast.type in (AstType.relational_expression, AstType.equality_expression):
        lhs, op, rhs = ast.children
        assert op.text is not None
        return RelExpr(
            operator=op.text,
            lhs=cast(Expr, make_expr(lhs)),
            rhs=cast(Expr, make_expr(rhs)),
        )
    elif ast.type == AstType.IDENTIFIER:
        assert ast.text is not None
        return VarExpr(var=ast.text)
    elif ast.type == AstType.logical_and_expression:
        return BinBoolExpr(
            operator="&&",
            lhs=make_expr(ast.children[0]),
            rhs=make_expr(ast.children[2]),
        )
    elif ast.type == AstType.logical_or_expression:
        return BinBoolExpr(
            operator="||",
            lhs=make_expr(ast.children[0]),
            rhs=make_expr(ast.children[2]),
        )
    elif ast.type == AstType.primary_expression:
        return make_expr(ast.children[1])
    elif ast.type == AstType.postfix_expression:
        assert ast.children[1].type == AstType.bracket_left
        return ArrayItemExpr(
            array=make_expr(ast.children[0]), index=make_expr(ast.children[2])
        )
    elif ast.type == AstType.CONSTANT:
        assert ast.text is not None
        return NumericExpr(int(ast.text))
    elif ast.type == AstType.additive_expression:
        return BinExpr(
            operator="+",
            lhs=make_expr(ast.children[0]),
            rhs=make_expr(ast.children[2])
        )
    else:
        assert False, f"unknown type {ast.type.value}"


def stmnt_create_cfg(ast: AstNode, next_node: CfgNode) -> CfgNode:
    if ast.type == AstType.semicolon:
        return next_node
    elif ast.type == AstType.selection_statement:
        assert ast.children[0].type == AstType.IF
        condition = make_expr(ast.children[2])
        return CondNode(
            condition=condition,
            true_br=stmnt_create_cfg(ast.children[4], next_node),
            false_br=stmnt_create_cfg(ast.children[6], next_node)
            if len(ast.children) == 7
            else next_node,
        )
    elif ast.type == AstType.compound_statement:
        statements = ast.children[1].children
        last = next_node
        for s in reversed(statements):
            last = stmnt_create_cfg(s, last)
        return last
    elif ast.type == AstType.jump_statement:
        assert ast.children[0].type == AstType.RETURN
        if len(ast.children) == 3:
            return AssignmentNode(
                expression=make_expr(ast.children[1]),
                var=VarExpr("ret"),
                next_node=EndNode(),
            )
        else:
            return EndNode()
    elif ast.type == AstType.declaration:
        # TODO: what about "int x, y;"
        if len(ast.children) == 3:
            return next_node
        var = ast.children[1].children[0].text
        assert var is not None
        value = make_expr(ast.children[1].children[2])
        assert isinstance(value, Expr)
        return AssignmentNode(expression=value, var=VarExpr(var), next_node=next_node)
    elif ast.type == AstType.expression_statement:
        assignment = ast.children[0]
        if assignment.type != AstType.assignment_expression:
            return next_node
        value = make_expr(assignment.children[2])
        assert isinstance(value, Expr)

        var = assignment.children[0]
        if var.type != AstType.IDENTIFIER:
            # TODO: what about "(x) = 5"
            rvalue = make_expr(var)
            assert isinstance(rvalue, ArrayItemExpr)
            # TODO: what about 2d+ arrays?
            assert isinstance(rvalue.array, VarExpr)
            return AssignmentNode(
                var=rvalue.array,
                expression=ChangeArrayExpr(
                    array=rvalue.array, index=rvalue.index, value=value
                ),
                next_node=next_node,
            )

        var = var.text
        assert var is not None

        return AssignmentNode(expression=value, var=VarExpr(var), next_node=next_node)
    else:
        assert False


def create_cfg(ast: AstNode) -> CfgNode:
    assert ast.type == AstType.function_definition

    body = ast.children[-1]
    assert body.type == AstType.compound_statement

    return StartNode(stmnt_create_cfg(body, EndNode()))

