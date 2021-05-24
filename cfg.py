from __future__ import annotations
from itertools import chain
from typing import Iterator, Optional, cast
from dataclasses import dataclass
import dataclasses

from cast import AstNode, AstRange, AstType
from expr import (
    ArraySelect,
    And,
    ArrayType,
    AtomicType,
    BinaryExpr,
    BoolValue,
    ArrayStore,
    Environment,
    Expr,
    IntValue,
    RelExpr,
    Variable,
    Then,
    Not,
    Predicate,
)


@dataclass(frozen=True)
class BasicPath:
    reachability: list[Expr]
    transformation: dict[str, Expr]
    assertion_start: Optional[Expr]
    assertion_end: Optional[Expr]
    nodes: list[CfgNode]

    @staticmethod
    def empty() -> BasicPath:
        return BasicPath([], {}, None, None, [])

    def copy(self) -> BasicPath:
        return BasicPath(
            self.reachability.copy(),
            self.transformation.copy(),
            self.assertion_start,
            self.assertion_end,
            self.nodes.copy(),
        )

    def condition(self, cond: Expr) -> BasicPath:
        cp = self.copy()
        cp.reachability.append(cond.assign(self.transformation))
        return cp

    def transform(self, var: str, expr: Expr) -> BasicPath:
        cp = self.copy()
        cp.transformation[var] = expr.assign(self.transformation)
        return cp

    def assert_start(self, prop: Expr) -> BasicPath:
        return dataclasses.replace(self, assertion_start=prop)

    def assert_end(self, prop: Expr) -> BasicPath:
        return dataclasses.replace(self, assertion_end=prop.assign(self.transformation))

    def get_proof_rule(self) -> Expr:
        assert self.assertion_end is not None
        # FIXME: handle the case when `reachability` is empty
        if self.assertion_start is not None:
            return Then(
                And(tuple(self.reachability) + (self.assertion_start,)),
                self.assertion_end,
            )
        else:
            return (
                Then(
                    And(tuple(self.reachability))
                    if len(self.reachability) >= 2
                    else self.reachability[0],
                    self.assertion_end,
                )
                if self.reachability
                else self.assertion_end
            )

    def append(self, node: CfgNode) -> BasicPath:
        cp = self.copy()
        cp.nodes.append(node)
        return cp

    def get_code_range(self) -> list[AstRange]:
        ranges: list[AstRange] = sorted(
            n.code_location for n in self.nodes if n.code_location is not None
        )
        if not ranges:
            return []
        fin = []
        prev = ranges[0]
        for r in ranges[1:]:
            if prev is None:
                prev = r
            elif r.start_line < prev.end_line or (
                r.start_line == prev.end_line and r.start_column <= prev.end_column
            ):
                if r.end_line > prev.end_line or (
                    r.end_line == prev.end_line and r.end_column > prev.end_column
                ):
                    prev = AstRange(
                        start_line=prev.start_line,
                        start_column=prev.start_column,
                        end_line=r.end_line,
                        end_column=r.end_column,
                    )
            else:
                fin.append(prev)
                prev = r
        if prev is not None:
            fin.append(prev)
        return fin


@dataclass
class CfgNode:
    code_location: Optional[AstRange]

    def generate_paths(
        self, path: BasicPath, visited_asserts: set[int],
    ) -> Iterator[BasicPath]:
        raise NotImplementedError

    def replace(self, dummy: DummyNode, node: CfgNode, visited: set[int]):
        raise NotImplementedError


@dataclass
class DummyNode(CfgNode):
    """
    used as a placeholder for when you can't provide a child node `y` when creating node `x` as `y` requires `x` to be created
    see for example how CFGs are created for loops
    """

    def replace(
        self, dummy: DummyNode, node: CfgNode, visited: set[int],
    ):
        return


@dataclass
class StartNode(CfgNode):
    requires: Optional[Expr]
    next_node: CfgNode

    def generate_paths(
        self, path: BasicPath, visited_asserts: set[int],
    ) -> Iterator[BasicPath]:
        yield from self.next_node.generate_paths(
            (
                path if self.requires is None else path.assert_start(self.requires)
            ).append(self),
            visited_asserts,
        )

    def replace(self, dummy: DummyNode, node: CfgNode, visited: set[int]):
        if id(self) in visited:
            return self
        if dummy is self.next_node:
            self.next_node = node
        self.next_node.replace(dummy, node, visited)


@dataclass
class EndNode(CfgNode):
    assertion: Optional[Expr]

    def generate_paths(
        self, path: BasicPath, visited_asserts: set[int],
    ) -> Iterator[BasicPath]:
        if self.assertion is not None and id(self) not in visited_asserts:
            visited_asserts.add(id(self))
            yield path.assert_end(self.assertion).append(self)

    def replace(self, dummy: DummyNode, node: CfgNode, visited: set[int]):
        pass


@dataclass
class CondNode(CfgNode):
    condition: Expr
    true_br: CfgNode
    false_br: CfgNode

    def generate_paths(
        self, path: BasicPath, visited_asserts: set[int],
    ) -> Iterator[BasicPath]:
        condition = self.condition
        yield from self.true_br.generate_paths(
            path.condition(condition).append(self), visited_asserts
        )
        yield from self.false_br.generate_paths(
            path.condition(Not(condition)).append(self), visited_asserts
        )

    def replace(self, dummy: DummyNode, node: CfgNode, visited: set[int]):
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
        self, path: BasicPath, visited_asserts: set[int],
    ) -> Iterator[BasicPath]:
        yield from self.next_node.generate_paths(
            path.transform(self.var.var, self.expression).append(self), visited_asserts
        )

    def replace(self, dummy: DummyNode, node: CfgNode, visited: set[int]):
        if id(self) in visited:
            return self
        if dummy is self.next_node:
            self.next_node = node
        self.next_node.replace(dummy, node, visited)


@dataclass
class AssumeNode(CfgNode):
    expression: Expr
    next_node: CfgNode

    def generate_paths(
        self, path: BasicPath, visited_asserts: set[int],
    ) -> Iterator[BasicPath]:
        yield from self.next_node.generate_paths(
            path.condition(self.expression).append(self), visited_asserts
        )

    def replace(self, dummy: DummyNode, node: CfgNode, visited: set[int]):
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
        self, path: BasicPath, visited_asserts: set[int],
    ) -> Iterator[BasicPath]:
        yield path.assert_end(self.assertion).append(self)
        if id(self) in visited_asserts:
            return
        visited_asserts.add(id(self))
        yield from self.next_node.generate_paths(
            BasicPath.empty().assert_start(self.assertion).append(self),
            visited_asserts,
        )

    def replace(self, dummy: DummyNode, node: CfgNode, visited: set[int]):
        if id(self) in visited:
            return self
        if dummy is self.next_node:
            self.next_node = node
        self.next_node.replace(dummy, node, visited)


@dataclass(frozen=True)
class StatementEnvironment:
    next_node: CfgNode
    start_node: StartNode
    end_node: EndNode
    loop_start: Optional[CfgNode]
    loop_end: Optional[CfgNode]
    env: Environment
    remembers: list[list[Expr]]
    labels: list[tuple[Optional[Expr], CfgNode]]

    @staticmethod
    def new(env: Environment) -> StatementEnvironment:
        end_node = EndNode(None, None)
        return StatementEnvironment(
            end_node,
            StartNode(None, None, DummyNode(None)),
            end_node,
            None,
            None,
            env,
            [],
            [],
        )

    def with_next(self, next_node: CfgNode) -> StatementEnvironment:
        return dataclasses.replace(self, next_node=next_node)

    def enter_loop(self, *, start: CfgNode, end: CfgNode) -> StatementEnvironment:
        return dataclasses.replace(self, loop_start=start, loop_end=end)

    def enter_switch(self, end: CfgNode) -> StatementEnvironment:
        return dataclasses.replace(self, loop_end=end, labels=[])

    def create_cfg(self, ast: AstNode) -> CfgNode:
        if ast.type == AstType.labeled_statement:
            if ast[0].type == AstType.DEFAULT:
                statement = self.create_cfg(ast[2])
                self.labels.append((None, statement))
                return statement
            else:
                assert ast[0].type == AstType.CASE
                value = Expr.from_ast(ast[1], self.env)
                statement = self.create_cfg(ast[3])
                self.labels.append((value, statement))
                return statement
        elif ast.type == AstType.semicolon:
            return self.next_node
        elif ast.type == AstType.selection_statement:
            if ast[0].type == AstType.IF:
                return CondNode(
                    code_location=ast[2].range,
                    condition=Expr.from_ast(ast[2], self.env),
                    true_br=self.create_cfg(ast[4]),
                    false_br=self.create_cfg(ast[6])
                    if len(ast.children) == 7
                    else self.next_node,
                )
            elif ast[0].type == AstType.SWITCH:
                switch_value = Expr.from_ast(ast[2], self.env)
                statement_env = self.enter_switch(self.next_node)
                statement = statement_env.create_cfg(ast[4])
                conds: list[CondNode] = []
                default = self.next_node
                for case_value, statement in statement_env.labels:
                    if case_value is None:
                        default = statement
                        continue
                    dummy = DummyNode(None)
                    conds.append(
                        CondNode(
                            None,
                            RelExpr("==", switch_value, case_value),
                            statement,
                            dummy,
                        )
                    )
                for cond, next_ in zip(
                    conds, cast("list[CfgNode]", conds[1:]) + [default]
                ):
                    cond.false_br = next_
                return conds[0] if conds else default
            else:
                assert False
        elif ast.type == AstType.compound_statement:
            self.open_scope()
            statements: list[CfgNode] = []
            dummies: list[DummyNode] = []
            for s in ast[1].children:
                dummy = DummyNode(None)
                statement = self.with_next(dummy).create_cfg(s)
                if statement is not dummy:
                    dummies.append(dummy)
                    statements.append(statement)
            statements.append(self.next_node)
            for s, s_next, d in zip(statements, statements[1:], dummies):
                s.replace(d, s_next, set())
            self.close_scope()
            return statements[0]
        elif ast.type == AstType.jump_statement:
            # TODO? handle goto
            if ast[0].type == AstType.BREAK:
                assert self.loop_end is not None
                return self.loop_end
            elif ast[0].type == AstType.CONTINUE:
                assert self.loop_start is not None
                return self.loop_start
            elif ast[0].type == AstType.RETURN:
                if len(ast.children) == 3:
                    return AssignmentNode(
                        ast.range,
                        expression=Expr.from_ast(ast[1], self.env),
                        var=Variable("ret", self.env["ret"]),
                        next_node=self.end_node,
                    )
                else:
                    return self.end_node
            else:
                assert False
        elif ast.type == AstType.declaration:
            # TODO: what about "int x, y;"
            type_ = ast[0].text
            assert type_ is not None

            if (
                ast[1].type == AstType.direct_declarator
                and ast[1][1].type == AstType.bracket_left
            ):
                var = ast[1][0].text
                assert var is not None
                self.env[var] = ArrayType(AtomicType(type_))
                return self.next_node

            type_ = AtomicType(type_)
            if ast[1].type == AstType.IDENTIFIER:
                var = ast[1].text
                assert var is not None
                self.env[var] = type_
                return self.next_node

            var = ast[1][0].text
            assert var is not None
            value = Expr.from_ast(ast[1][2], self.env)
            self.env[var] = type_
            return AssignmentNode(
                ast.range,
                expression=value,
                var=Variable(self.env.rename(var), type_),
                next_node=self.next_node,
            )
        elif ast.type == AstType.expression_statement:
            if (
                ast[0].type == AstType.postfix_expression
                and ast[0][1].type == AstType.paren_left
                and ast[0][0].type == AstType.IDENTIFIER
            ):
                fn = ast[0][0].text
                if fn == "assert":
                    assertion = Expr.from_ast(ast[0][2], self.env)
                    remembers = tuple(chain.from_iterable(self.remembers))
                    assertion = (
                        And(remembers + (assertion,)) if remembers else assertion
                    )
                    return AssertNode(
                        ast.range, assertion=assertion, next_node=self.next_node,
                    )
                elif fn == "ensures":
                    assert self.end_node.assertion is None
                    self.end_node.assertion = Expr.from_ast(ast[0][2], self.env)
                    self.end_node.code_location = ast.range
                    return self.next_node
                elif fn == "requires":
                    assert self.start_node.requires is None
                    self.start_node.requires = Expr.from_ast(ast[0][2], self.env)
                    self.start_node.code_location = ast.range
                    return self.next_node
                elif fn == "freeze":
                    args = ast[0][2]
                    right = Expr.from_ast(args[2], self.env)
                    assert args[0].type == AstType.IDENTIFIER
                    assert args[0].text is not None
                    self.env[args[0].text] = right.get_type()
                    var = Expr.from_ast(args[0], self.env)
                    assert isinstance(var, Variable)
                    return AssignmentNode(ast.range, right, var, self.next_node)
                elif fn == "remember":
                    self.remembers[-1].append(Expr.from_ast(ast[0][2], self.env))
                    return self.next_node
                elif fn == "assume":
                    return AssumeNode(
                        ast.range, Expr.from_ast(ast[0][2], self.env), self.next_node
                    )
                else:
                    assert False, f"unknown function {fn}"

            if ast[0].type == AstType.postfix_expression and ast[0][1].type in (
                AstType.INC_OP,
                AstType.DEC_OP,
            ):
                left = Expr.from_ast(ast[0][0], self.env)
                operator = "+=" if ast[0][1].type == AstType.INC_OP else "-="
                value = IntValue(1)
            elif ast[0].type == AstType.unary_expression and ast[0][0].type in (
                AstType.INC_OP,
                AstType.DEC_OP,
            ):
                left = Expr.from_ast(ast[0][1], self.env)
                operator = "+=" if ast[0][0].type == AstType.INC_OP else "-="
                value = IntValue(1)
            elif ast[0].type != AstType.assignment_expression:
                # FIXME
                return self.next_node
            else:
                value = Expr.from_ast(ast[0][2], self.env)
                operator = ast[0][1].text
                assert operator is not None
                left = Expr.from_ast(ast[0][0], self.env)

            # TODO? handle chained assignments?

            # handle other assignment operators: *= /= %= += -= >>= <<= &= |= ^=
            if operator != "=":
                operator = operator[:-1]
                value = BinaryExpr(operator=operator, lhs=left, rhs=value)

            if isinstance(left, Variable):
                return AssignmentNode(
                    ast.range, expression=value, var=left, next_node=self.next_node
                )
            elif isinstance(left, ArraySelect):
                # TODO? what about 2d+ arrays?
                assert isinstance(left.array, Variable)
                return AssignmentNode(
                    ast.range,
                    var=left.array,
                    expression=ArrayStore(
                        array=left.array, index=left.index, value=value,
                    ),
                    next_node=self.next_node,
                )
            else:
                assert False
        elif ast.type == AstType.iteration_statement:
            if ast[0].type == AstType.WHILE:
                self.open_scope()
                while_node = CondNode(
                    ast[2].range,
                    Expr.from_ast(ast[2], self.env),
                    DummyNode(None),
                    self.next_node,
                )
                while_node.true_br = (
                    self.enter_loop(start=while_node, end=self.next_node)
                    .with_next(while_node)
                    .create_cfg(ast[4])
                )
                self.close_scope()
                return while_node
            elif ast[0].type == AstType.DO:
                self.open_scope()
                cond = CondNode(
                    ast[4].range,
                    Expr.from_ast(ast[4], self.env),
                    DummyNode(None),
                    self.next_node,
                )
                cond.true_br = (
                    self.enter_loop(start=cond, end=self.next_node)
                    .with_next(cond)
                    .create_cfg(ast[1])
                )
                self.close_scope()
                return cond.true_br
            elif ast[0].type == AstType.FOR:
                self.open_scope()
                if ast[2].type == AstType.declaration:
                    decl = self.with_next(DummyNode(None)).create_cfg(ast[2])
                    assert isinstance(decl, AssignmentNode)
                else:
                    assert ast[2].type == AstType.semicolon
                    decl = None
                if ast[3].type == AstType.expression_statement:
                    cond = CondNode(
                        ast[3].range,
                        Expr.from_ast(ast[3][0], self.env),
                        DummyNode(None),
                        self.next_node,
                    )
                else:
                    assert ast[3].type == AstType.semicolon
                    cond = CondNode(
                        ast[3].range, BoolValue(True), DummyNode(None), self.next_node,
                    )
                if decl is not None:
                    decl.next_node = cond
                if ast[4].type == AstType.paren_right:
                    inc = None
                else:
                    inc = self.with_next(cond).create_cfg(
                        AstNode(
                            None, AstType.expression_statement, ast[4].range, [ast[4]]
                        )
                    )
                cond.true_br = (
                    self.enter_loop(start=cond, end=self.next_node)
                    .with_next(inc or cond)
                    .create_cfg(ast[5] if inc is None else ast[6])
                )
                self.close_scope()
                return decl or cond
            else:
                assert False
        else:
            assert False

    def open_scope(self):
        self.env.open_scope()
        self.remembers.append([])

    def close_scope(self):
        self.remembers.pop()
        self.env.close_scope()


def create_cfg(ast: AstNode, requires: Optional[Expr], env: Environment) -> CfgNode:
    assert ast.type == AstType.function_definition

    body = ast[-1]
    assert body.type == AstType.compound_statement

    builder = StatementEnvironment.new(env)
    builder.start_node.next_node = builder.create_cfg(body)
    return builder.start_node

