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


def make_generic_expr(ast: AstNode) -> Union[Expr, BoolExpr]:
    if ast.type in (AstType.relational_expression, AstType.equality_expression):
        lhs, op, rhs = ast.children
        assert op.text is not None
        return RelExpr(
            operator=op.text,
            lhs=make_expr(lhs),
            rhs=make_expr(rhs),
        )
    elif ast.type == AstType.IDENTIFIER:
        assert ast.text is not None
        return VarExpr(var=ast.text)
    elif ast.type in (AstType.logical_and_expression, AstType.logical_or_expression):
        operator = ast[1].text
        assert operator is not None
        return BinBoolExpr(
            operator=operator,
            lhs=make_bool_expr(ast[0]),
            rhs=make_bool_expr(ast[2]),
        )
    elif ast.type == AstType.primary_expression:
        return make_generic_expr(ast[1])
    elif ast.type == AstType.postfix_expression:
        assert ast[1].type == AstType.bracket_left
        return ArrayItemExpr(
            array=make_expr(ast[0]), index=make_expr(ast[2])
        )
    elif ast.type == AstType.CONSTANT:
        assert ast.text is not None
        return NumericExpr(int(ast.text))
    elif ast.type == AstType.additive_expression:
        return BinExpr(
            operator="+",
            lhs=make_expr(ast[0]),
            rhs=make_expr(ast[2])
        )
    else:
        assert False, f"unknown type {ast.type.value}"


def make_expr(ast: AstNode) -> Expr:
    expr = make_generic_expr(ast)
    assert isinstance(expr, Expr)
    return expr


def make_bool_expr(ast: AstNode) -> BoolExpr:
    expr = make_generic_expr(ast)
    assert isinstance(expr, BoolExpr)
    return expr


def stmnt_create_cfg(ast: AstNode, next_node: CfgNode) -> CfgNode:
    if ast.type == AstType.semicolon:
        return next_node
    elif ast.type == AstType.selection_statement:
        assert ast[0].type == AstType.IF
        return CondNode(
            condition=make_bool_expr(ast[2]),
            true_br=stmnt_create_cfg(ast[4], next_node),
            false_br=stmnt_create_cfg(ast[6], next_node)
            if len(ast.children) == 7
            else next_node,
        )
    elif ast.type == AstType.compound_statement:
        statements = ast[1].children
        last = next_node
        for s in reversed(statements):
            last = stmnt_create_cfg(s, last)
        return last
    elif ast.type == AstType.jump_statement:
        assert ast[0].type == AstType.RETURN
        if len(ast.children) == 3:
            return AssignmentNode(
                expression=make_expr(ast[1]),
                var=VarExpr("ret"),
                next_node=EndNode(),
            )
        else:
            return EndNode()
    elif ast.type == AstType.declaration:
        # TODO: what about "int x, y;"
        if ast[1].type != AstType.init_declarator:
            return next_node
        var = ast[1][0].text
        assert var is not None
        return AssignmentNode(expression=make_expr(ast[1][2]), var=VarExpr(var), next_node=next_node)
    elif ast.type == AstType.expression_statement:
        assignment = ast[0]
        if assignment.type != AstType.assignment_expression:
            return next_node
        value = make_expr(assignment[2])

        var = assignment[0]
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

    body = ast[-1]
    assert body.type == AstType.compound_statement

    return StartNode(stmnt_create_cfg(body, EndNode()))

