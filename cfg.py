from functools import reduce
from itertools import chain
from typing import Dict, Iterator, List, Optional, Set
from dataclasses import dataclass
import dataclasses

from cast import AstNode, AstType
from expr import (
    ArraySelect,
    And,
    BinaryExpr,
    BoolValue,
    ArrayStore,
    Environment,
    Expr,
    Type,
    Variable,
    Prop,
    Then,
    Not,
    Predicate,
)


@dataclass(frozen=True)
class BasicPath:
    reachability: List[Expr]
    transformation: Dict[str, Expr]
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

    def condition(self, cond: Expr) -> "BasicPath":
        cp = self.copy()
        cp.reachability.append(cond.assign(self.transformation))
        return cp

    def transform(self, var: str, expr: Expr) -> "BasicPath":
        cp = self.copy()
        cp.transformation[var] = expr.assign(self.transformation)
        return cp

    def assert_start(self, prop: Expr) -> "BasicPath":
        return dataclasses.replace(self, assertion_start=prop)

    def assert_end(self, prop: Expr) -> "BasicPath":
        return dataclasses.replace(self, assertion_end=prop.assign(self.transformation))

    def get_proof_rule(self) -> Prop:
        assert self.assertion_end is not None
        # FIXME: handle the case when `reachability` is empty
        if self.assertion_start is not None:
            return Then(
                reduce(
                    lambda acc, x: And(acc, x), self.reachability, self.assertion_start,
                ),
                self.assertion_end,
            )
        else:
            return Then(
                reduce(lambda acc, x: And(acc, x), self.reachability, BoolValue(True),),
                self.assertion_end,
            )


@dataclass
class CfgNode:
    def generate_paths(
        self, path: BasicPath, visited_asserts: Set[int],
    ) -> Iterator[BasicPath]:
        raise NotImplementedError

    def replace(self, dummy: "DummyNode", node: "CfgNode", visited: Set[int]):
        raise NotImplementedError


@dataclass
class DummyNode(CfgNode):
    """
    used as a placeholder for when you can't provide a child node `y` when creating node `x` as `y` requires `x` to be created
    see for example how CFGs are created for loops
    """

    def replace(
        self, dummy: "DummyNode", node: "CfgNode", visited: Set[int],
    ):
        return


@dataclass
class StartNode(CfgNode):
    requires: Optional[Expr]
    next_node: CfgNode

    def generate_paths(
        self, path: BasicPath, visited_asserts: Set[int],
    ) -> Iterator[BasicPath]:
        yield from self.next_node.generate_paths(
            path if self.requires is None else path.assert_start(self.requires),
            visited_asserts,
        )

    def replace(self, dummy: DummyNode, node: CfgNode, visited: Set[int]):
        if id(self) in visited:
            return self
        if dummy is self.next_node:
            self.next_node = node
        self.next_node.replace(dummy, node, visited)


@dataclass
class EndNode(CfgNode):
    assertion: Optional[Expr]

    def generate_paths(
        self, path: BasicPath, visited_asserts: Set[int],
    ) -> Iterator[BasicPath]:
        if self.assertion is not None and id(self) not in visited_asserts:
            visited_asserts.add(id(self))
            yield path.assert_end(self.assertion)

    def replace(self, dummy: DummyNode, node: CfgNode, visited: Set[int]):
        pass


@dataclass
class CondNode(CfgNode):
    condition: Expr
    true_br: CfgNode
    false_br: CfgNode

    def generate_paths(
        self, path: BasicPath, visited_asserts: Set[int],
    ) -> Iterator[BasicPath]:
        condition = self.condition
        yield from self.true_br.generate_paths(
            path.condition(condition), visited_asserts
        )
        yield from self.false_br.generate_paths(
            path.condition(Not(condition)), visited_asserts
        )

    def replace(self, dummy: DummyNode, node: "CfgNode", visited: Set[int]):
        if id(self) in visited:
            return self
        if dummy is self.true_br:
            self.true_br = node
        self.true_br.replace(dummy, node, visited=visited | {id(self)})
        if dummy is self.false_br:
            self.false_br = node
        self.false_br.replace(dummy, node, visited=visited | {id(self)})


@dataclass
class AssignmentNode(CfgNode):
    expression: Expr
    var: Variable
    next_node: CfgNode

    def generate_paths(
        self, path: BasicPath, visited_asserts: Set[int],
    ) -> Iterator[BasicPath]:
        yield from self.next_node.generate_paths(
            path.transform(self.var.var, self.expression), visited_asserts
        )

    def replace(self, dummy: DummyNode, node: "CfgNode", visited: Set[int]):
        if id(self) in visited:
            return self
        if dummy is self.next_node:
            self.next_node = node
        self.next_node.replace(dummy, node, visited)


@dataclass
class AssertNode(CfgNode):
    assertion: Expr
    next_node: CfgNode

    def generate_paths(
        self, path: BasicPath, visited_asserts: Set[int],
    ) -> Iterator[BasicPath]:
        yield path.assert_end(self.assertion)
        if id(self) in visited_asserts:
            return
        visited_asserts.add(id(self))
        yield from self.next_node.generate_paths(
            BasicPath.empty().assert_start(self.assertion), visited_asserts,
        )

    def replace(self, dummy: DummyNode, node: "CfgNode", visited: Set[int]):
        if id(self) in visited:
            return self
        if dummy is self.next_node:
            self.next_node = node
        self.next_node.replace(dummy, node, visited)


@dataclass
class CutpointNode(CfgNode):
    predicate: Predicate
    next_node: CfgNode

    def generate_paths(
        self, path: BasicPath, visited_asserts: Set[int],
    ) -> Iterator[BasicPath]:
        yield path.assert_end(self.predicate)
        if id(self) in visited_asserts:
            return
        visited_asserts.add(id(self))
        yield from self.next_node.generate_paths(
            BasicPath.empty().assert_start(self.predicate), visited_asserts,
        )


def statement_create_cfg(
    ast: AstNode,
    next_node: CfgNode,
    end_node: EndNode,
    loop_start: Optional[CfgNode],
    loop_end: Optional[CfgNode],
    env: Environment,
    remembers: List[List[Expr]],
) -> CfgNode:
    if ast.type == AstType.semicolon:
        return next_node
    elif ast.type == AstType.selection_statement:
        # TODO: handle switch
        assert ast[0].type == AstType.IF
        return CondNode(
            condition=Expr.from_ast(ast[2], env),
            true_br=statement_create_cfg(
                ast[4], next_node, end_node, loop_start, loop_end, env, remembers
            ),
            false_br=statement_create_cfg(
                ast[6], next_node, end_node, loop_start, loop_end, env, remembers
            )
            if len(ast.children) == 7
            else next_node,
        )
    elif ast.type == AstType.compound_statement:
        env.open_scope()
        remembers.append([])
        statements: List[CfgNode] = []
        dummies: List[DummyNode] = []
        for s in ast[1].children:
            dummy = DummyNode()
            statement = statement_create_cfg(
                s, dummy, end_node, loop_start, loop_end, env, remembers
            )
            if statement is not dummy:
                dummies.append(dummy)
                statements.append(statement)
        statements.append(next_node)
        for s, s_next, d in zip(statements, statements[1:], dummies):
            s.replace(d, s_next, set())
        remembers.pop()
        env.close_scope()
        return statements[0]
    elif ast.type == AstType.jump_statement:
        # TODO? handle goto
        if ast[0].type == AstType.BREAK:
            assert loop_end is not None
            return loop_end
        elif ast[0].type == AstType.CONTINUE:
            assert loop_start is not None
            return loop_start
        elif ast[0].type == AstType.RETURN:
            if len(ast.children) == 3:
                return AssignmentNode(
                    expression=Expr.from_ast(ast[1], env),
                    var=Variable("ret", env["ret"]),
                    next_node=end_node,
                )
            else:
                return end_node
        else:
            assert False
    elif ast.type == AstType.declaration:
        # TODO: what about "int x, y;"
        type_ = ast[0].text
        # TODO: what about array types?
        assert type_ is not None
        type_ = Type(type_)
        if ast[1].type != AstType.init_declarator:
            var = ast[1].text
            assert var is not None
            env[var] = type_
            return next_node
        var = ast[1][0].text
        assert var is not None
        value = Expr.from_ast(ast[1][2], env)
        env[var] = type_
        return AssignmentNode(
            expression=value, var=Variable(env.rename(var), type_), next_node=next_node
        )
    elif ast.type == AstType.expression_statement:
        # TODO: handle ++i, --i, i++, i--
        if ast[0].type == AstType.postfix_expression:
            assert (
                ast[0][1].type == AstType.paren_left
                and ast[0][0].type == AstType.IDENTIFIER
            )
            if ast[0][0].text == "assert":
                assertion = Expr.from_ast(ast[0][2], env)
                assertion = reduce(
                    lambda acc, x: And(acc, x),
                    chain.from_iterable(remembers),
                    assertion,
                )
                return AssertNode(assertion=assertion, next_node=next_node,)
            elif ast[0][0].text == "ensures":
                assert end_node.assertion is None
                end_node.assertion = Expr.from_ast(ast[0][2], env)
                return next_node
            elif ast[0][0].text == "requires":
                return next_node
            elif ast[0][0].text == "freeze":
                args = ast[0][2]
                right = Expr.from_ast(args[2], env)
                assert isinstance(right, Variable)
                assert args[0].type == AstType.IDENTIFIER
                assert args[0].text is not None
                env[args[0].text] = right.type_
                var = Expr.from_ast(args[0], env)
                assert isinstance(var, Variable)
                return AssignmentNode(right, var, next_node)
            elif ast[0][0].text == "remember":
                remembers[-1].append(Expr.from_ast(ast[0][2], env))
                return next_node
            else:
                assert False, f"unknown function {ast[0][0].text}"

        if ast[0].type != AstType.assignment_expression:
            # FIXME
            return next_node

        value = Expr.from_ast(ast[0][2], env)
        operator = ast[0][1].text
        assert operator is not None
        left = Expr.from_ast(ast[0][0], env)

        # TODO? handle chained assignments?

        # handle other assignment operators: *= /= %= += -= >>= <<= &= |= ^=
        if operator != "=":
            operator = operator[:-1]
            value = BinaryExpr(operator=operator, lhs=left, rhs=value)

        if isinstance(left, Variable):
            return AssignmentNode(expression=value, var=left, next_node=next_node)
        elif isinstance(left, ArraySelect):
            # TODO? what about 2d+ arrays?
            assert isinstance(left.array, Variable)
            return AssignmentNode(
                var=left.array,
                expression=ArrayStore(array=left.array, index=left.index, value=value),
                next_node=next_node,
            )
        else:
            assert False
    elif ast.type == AstType.iteration_statement:
        if ast[0].type == AstType.WHILE:
            env.open_scope()
            remembers.append([])
            while_node = CondNode(Expr.from_ast(ast[2], env), DummyNode(), next_node)
            while_node.true_br = statement_create_cfg(
                ast[4],
                while_node,
                end_node,
                loop_start=while_node,
                loop_end=next_node,
                env=env,
                remembers=remembers,
            )
            remembers.pop()
            env.close_scope()
            return while_node
        elif ast[0].type == AstType.DO:
            env.open_scope()
            remembers.append([])
            cond = CondNode(Expr.from_ast(ast[4], env), DummyNode(), next_node)
            cond.true_br = statement_create_cfg(
                ast[1],
                cond,
                end_node,
                loop_start=cond,
                loop_end=next_node,
                env=env,
                remembers=remembers,
            )
            remembers.pop()
            env.close_scope()
            return cond.true_br
        elif ast[0].type == AstType.FOR:
            # TODO: handle other cases e.g. `for(;;);`
            # for (decl; cond; inc) body
            env.open_scope()
            remembers.append([])
            decl = statement_create_cfg(
                ast[2], DummyNode(), end_node, None, None, env, remembers
            )
            cond = CondNode(Expr.from_ast(ast[3][0], env), DummyNode(), next_node)
            assert isinstance(decl, AssignmentNode)
            decl.next_node = cond
            inc = statement_create_cfg(
                AstNode(None, AstType.expression_statement, ast[4].range, [ast[4]]),
                cond,
                end_node,
                None,
                None,
                env,
                remembers,
            )
            cond.true_br = statement_create_cfg(
                ast[6],
                inc,
                end_node,
                loop_start=cond,
                loop_end=next_node,
                env=env,
                remembers=remembers,
            )
            remembers.pop()
            env.close_scope()
            return decl
        else:
            assert False
    else:
        assert False


def create_cfg(ast: AstNode, requires: Optional[Expr], env: Environment) -> CfgNode:
    assert ast.type == AstType.function_definition

    body = ast[-1]
    assert body.type == AstType.compound_statement

    end_node = EndNode(None)
    return StartNode(
        requires, statement_create_cfg(body, end_node, end_node, None, None, env, [])
    )

