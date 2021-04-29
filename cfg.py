from functools import reduce
from typing import Dict, FrozenSet, Iterator, List, Optional
from cast import AstNode, AstType
from dataclasses import dataclass
import dataclasses
from expr import (
    ArrayItemExpr,
    BinExpr,
    BoolExpr,
    ChangeArrayExpr,
    Expr,
    VarExpr,
)
from prop import And, Not, Prop, Then


R = List[Prop]
T = Dict[str, Expr]


@dataclass
class BasicPath:
    reachability: R
    transformation: T
    assertion_start: Optional[Prop]
    assertion_end: Optional[Prop]

    @staticmethod
    def empty() -> "BasicPath":
        return BasicPath([], {}, None, None)

    def copy(self) -> "BasicPath":
        return BasicPath(
            self.reachability.copy(),
            self.transformation.copy(),
            self.assertion_start,
            self.assertion_end,
        )

    def condition(self, cond: Prop) -> "BasicPath":
        cp = self.copy()
        cp.reachability.append(cond.assign(self.transformation))
        return cp

    def transform(self, var: str, expr: Expr) -> "BasicPath":
        cp = self.copy()
        cp.transformation[var] = expr.assign(self.transformation)
        return cp

    def assert_start(self, prop: Prop) -> "BasicPath":
        return dataclasses.replace(self, assertion_start=prop)

    def assert_end(self, prop: Prop) -> "BasicPath":
        return dataclasses.replace(self, assertion_end=prop.assign(self.transformation))

    def get_proof_rule(self) -> Prop:
        assert self.assertion_end is not None
        # FIXME: handle the case when `reachability` is empty
        if self.assertion_start is not None:
            return Then(
                reduce(
                    lambda acc, x: And(acc, x), self.reachability, self.assertion_start
                ),
                self.assertion_end,
            )
        else:
            return Then(
                reduce(lambda acc, x: And(acc, x), self.reachability),
                self.assertion_end,
            )


@dataclass
class CfgNode:
    def generate_paths(
        self, path: BasicPath, visited: FrozenSet[int]
    ) -> Iterator[BasicPath]:
        raise NotImplementedError


@dataclass
class StartNode(CfgNode):
    requires: Optional[Prop]
    next_node: CfgNode

    def generate_paths(
        self, path: BasicPath, visited: FrozenSet[int]
    ) -> Iterator[BasicPath]:
        yield from self.next_node.generate_paths(
            path if self.requires is None else path.assert_start(self.requires),
            visited,
        )


@dataclass
class EndNode(CfgNode):
    assertion: Optional[Prop]

    def generate_paths(
        self, path: BasicPath, visited: FrozenSet[int]
    ) -> Iterator[BasicPath]:
        if self.assertion is not None:
            yield path.assert_end(self.assertion)


@dataclass
class CondNode(CfgNode):
    condition: BoolExpr
    true_br: CfgNode
    false_br: CfgNode

    def generate_paths(
        self, path: BasicPath, visited: FrozenSet[int]
    ) -> Iterator[BasicPath]:
        condition = Prop.from_expr(self.condition)
        yield from self.true_br.generate_paths(path.condition(condition), visited)
        yield from self.false_br.generate_paths(path.condition(Not(condition)), visited)


@dataclass
class AssignmentNode(CfgNode):
    expression: Expr
    var: VarExpr
    next_node: CfgNode

    def generate_paths(
        self, path: BasicPath, visited: FrozenSet[int]
    ) -> Iterator[BasicPath]:
        yield from self.next_node.generate_paths(
            path.transform(self.var.var, self.expression), visited
        )


@dataclass
class AssertNode(CfgNode):
    assertion: Prop
    next_node: CfgNode

    def generate_paths(
        self, path: BasicPath, visited: FrozenSet[int]
    ) -> Iterator[BasicPath]:
        yield path.assert_end(self.assertion)
        if id(self) in visited:
            return
        yield from self.next_node.generate_paths(
            BasicPath.empty().assert_start(self.assertion), visited | {id(self)}
        )


def statement_create_cfg(
    ast: AstNode,
    next_node: CfgNode,
    end_node: EndNode,
    loop_start: Optional[CfgNode],
    loop_end: Optional[CfgNode],
) -> CfgNode:
    if ast.type == AstType.semicolon:
        return next_node
    elif ast.type == AstType.selection_statement:
        # TODO: handle switch
        assert ast[0].type == AstType.IF
        return CondNode(
            condition=BoolExpr.from_ast(ast[2]),
            true_br=statement_create_cfg(
                ast[4], next_node, end_node, loop_start, loop_end
            ),
            false_br=statement_create_cfg(
                ast[6], next_node, end_node, loop_start, loop_end
            )
            if len(ast.children) == 7
            else next_node,
        )
    elif ast.type == AstType.compound_statement:
        statements = ast[1].children
        last = next_node
        for s in reversed(statements):
            last = statement_create_cfg(s, last, end_node, loop_start, loop_end)
        return last
    elif ast.type == AstType.jump_statement:
        # TODO: handle goto
        if ast[0].type == AstType.BREAK:
            assert loop_end is not None
            return loop_end
        elif ast[0].type == AstType.CONTINUE:
            assert loop_start is not None
            return loop_start
        elif ast[0].type == AstType.RETURN:
            if len(ast.children) == 3:
                return AssignmentNode(
                    expression=Expr.from_ast(ast[1]),
                    var=VarExpr("ret"),
                    next_node=end_node,
                )
            else:
                return end_node
        else:
            assert False
    elif ast.type == AstType.declaration:
        # TODO: what about "int x, y;"
        if ast[1].type != AstType.init_declarator:
            return next_node
        var = ast[1][0].text
        assert var is not None
        return AssignmentNode(
            expression=Expr.from_ast(ast[1][2]), var=VarExpr(var), next_node=next_node
        )
    elif ast.type == AstType.expression_statement:
        # TODO: handle ++i, --i, i++, i--
        if ast[0].type == AstType.postfix_expression:
            assert (
                ast[0][1].type == AstType.paren_left
                and ast[0][0].type == AstType.IDENTIFIER
            )
            if ast[0][0].text == "assert":
                return AssertNode(
                    assertion=Prop.from_ast(ast[0][2]), next_node=next_node
                )
            else:
                assert ast[0][0].text in ("ensures", "requires")
                return next_node

        if ast[0].type != AstType.assignment_expression:
            # FIXME
            return next_node

        value = Expr.from_ast(ast[0][2])
        operator = ast[0][1].text
        assert operator is not None
        left = Expr.from_ast(ast[0][0])

        # TODO? handle chained assignments?

        # handle other assignment operators: *= /= %= += -= >>= <<= &= |= ^=
        if operator != "=":
            operator = operator[:-1]
            value = BinExpr(operator=operator, lhs=left, rhs=value)

        if isinstance(left, VarExpr):
            return AssignmentNode(expression=value, var=left, next_node=next_node)
        elif isinstance(left, ArrayItemExpr):
            # TODO? what about 2d+ arrays?
            assert isinstance(left.array, VarExpr)
            return AssignmentNode(
                var=left.array,
                expression=ChangeArrayExpr(
                    array=left.array, index=left.index, value=value
                ),
                next_node=next_node,
            )
        else:
            assert False

    elif ast.type == AstType.iteration_statement:
        if ast[0].type == AstType.WHILE:
            while_node = CondNode(BoolExpr.from_ast(ast[2]), None, next_node)
            while_node.true_br = statement_create_cfg(
                ast[4], while_node, end_node, loop_start=while_node, loop_end=next_node
            )
            return while_node
        elif ast[0].type == AstType.DO:
            cond = CondNode(BoolExpr.from_ast(ast[4]), None, next_node)
            cond.true_br = statement_create_cfg(
                ast[1], cond, end_node, loop_start=cond, loop_end=next_node
            )
            return cond.true_br
        elif ast[0].type == AstType.FOR:
            # TODO: handle other cases e.g. `for(;;);`
            # for (decl; cond; inc) body
            cond = CondNode(BoolExpr.from_ast(ast[3][0]), None, next_node)
            decl = statement_create_cfg(ast[2], cond, end_node, None, None)
            inc = statement_create_cfg(
                AstNode(None, AstType.expression_statement, ast[4].range, [ast[4]]),
                cond,
                end_node,
                None,
                None,
            )
            cond.true_br = statement_create_cfg(
                ast[6], inc, end_node, loop_start=cond, loop_end=next_node
            )
            return decl
        else:
            assert False
    else:
        assert False


def create_cfg(
    ast: AstNode, requires: Optional[Prop], ensures: Optional[Prop]
) -> CfgNode:
    assert ast.type == AstType.function_definition

    body = ast[-1]
    assert body.type == AstType.compound_statement

    end_node = EndNode(ensures)
    return StartNode(
        requires, statement_create_cfg(body, end_node, end_node, None, None)
    )

