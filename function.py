from __future__ import annotations
from collections import defaultdict
from dataclasses import dataclass
from typing import Iterator, Optional, cast

import z3
from pygraphviz.agraph import AGraph
import networkx as nx

from cast import AstNode, AstType
from cfg import (
    AssertNode,
    AssignmentNode,
    AssumeNode,
    BasicPath,
    CfgNode,
    CondNode,
    DummyNode,
    EndNode,
    StartNode,
    create_cfg,
    get_paths,
)
from expr import (
    And,
    ArrayType,
    AtomicType,
    Environment,
    ForAll,
    Expr,
    Predicate,
    Prop,
    Then,
    Variable,
)


@dataclass(frozen=True)
class CheckResult:
    def is_ok(self) -> bool:
        return False


@dataclass(frozen=True)
class Fail(CheckResult):
    pass


@dataclass(frozen=True)
class Unknown(Fail):
    code: int


@dataclass(frozen=True)
class Ok(CheckResult):
    def is_ok(self) -> bool:
        return True


@dataclass(frozen=True)
class HornInvariant:
    name: str
    mapping: list[tuple[Expr, Expr]]
    else_expr: Optional[Expr]

    def __str__(self) -> str:
        return (
            "["
            + ", ".join(f"{x} ⟼ {y}" for x, y in self.mapping)
            + (", else ⟼ " if self.mapping else "")
            + str(self.else_expr)
            + "]"
        )


@dataclass(frozen=True)
class HornOk(CheckResult):
    invariants: list[HornInvariant]

    def is_ok(self) -> bool:
        return True


@dataclass(frozen=True)
class HornFail(Fail):
    pass


@dataclass(frozen=True)
class CounterExample(Fail):
    model: z3.ModelRef


@dataclass(frozen=True)
class BaseFunction:
    filename: str
    name: str
    cfg: CfgNode
    params: list[Variable]
    vars: list[Variable]

    @classmethod
    def from_ast(cls, filename: str, ast: AstNode, **extras):
        declarator = next(
            c for c in ast.children if c.type == AstType.direct_declarator
        )
        fn_name = next(c for c in declarator if c.type == AstType.IDENTIFIER).text
        assert fn_name is not None
        assert ast.type == AstType.function_definition
        ret_type = ast[0].text
        assert ret_type is not None
        env = Environment.empty()
        if ret_type != "void":
            env["ret"] = AtomicType(ret_type)
        params = declarator[2]
        if params.type == AstType.parameter_list:
            for p in params.children:
                if p.type == AstType.parameter_declaration:
                    ty = p[0].text
                    assert ty is not None and ty in ("int", "float", "bool",)
                    ty = AtomicType(ty)
                    name = None
                    if p[1].type == AstType.IDENTIFIER:
                        name = p[1].text
                    elif (
                        p[1].type == AstType.direct_declarator
                        and p[1][0].type == AstType.IDENTIFIER
                        and p[1][1].text == "["
                    ):
                        name = p[1][0].text
                        ty = ArrayType(ty)
                    else:
                        assert False
                    assert name is not None
                    env[name] = ty
        params = env.get_vars()

        requires = None
        for s in ast[-1][1].children:
            if (
                s.type == AstType.expression_statement
                and s[0].type == AstType.postfix_expression
                and s[0][1].type == AstType.paren_left
                and s[0][0].type == AstType.IDENTIFIER
                and s[0][0].text == "requires"
            ):
                requires = Expr.from_ast(s[0][2], env)

        cfg = create_cfg(ast, requires, env)
        vars = env.get_vars()
        for p in params:
            del vars[p]
        vars = [Variable(v, t) for v, t in vars.items()]
        params = [Variable(v, t) for v, t in params.items()]
        return cls(filename, cfg=cfg, name=fn_name, vars=vars, params=params, **extras)

    def draw_cfg(self, no_content=False):
        filepath = f"cfg-img/{self.name}.svg"

        graph = AGraph(directed=True)
        ids = set()

        def add_node(
            id_: int,
            color: str,
            content: str,
            shape: str,
            label: str,
            style: Optional[str] = None,
            **kwargs,
        ):
            kwargs.update(color=color, shape=shape, penwidth="4")
            if style is not None:
                kwargs.update(style=style)
            if no_content:
                kwargs.update(label=label)
            else:
                kwargs.update(label=content, tooltip=label)
            graph.add_node(id_, **kwargs)

        def get_id(node: CfgNode) -> int:
            return id(node)

        def traverse(node: CfgNode):
            id_ = get_id(node)
            if id_ in ids:
                return
            ids.add(id_)
            if isinstance(node, StartNode):
                add_node(
                    id_,
                    color="green",
                    label="start",
                    shape="ellipse",
                    content=f"{node.requires}",
                )
                graph.add_edge(id_, get_id(node.next_node))
                traverse(node.next_node)
            elif isinstance(node, AssignmentNode):
                add_node(
                    id_,
                    color="blue",
                    label="assign",
                    shape="rectangle",
                    content=f"{node.var.var} := {node.expression}",
                )
                graph.add_edge(id_, get_id(node.next_node))
                traverse(node.next_node)
            elif isinstance(node, CondNode):
                add_node(
                    id_,
                    color="red",
                    label="condition",
                    shape="diamond",
                    content=f"{node.condition}",
                )
                graph.add_edge(id_, get_id(node.true_br), label="T")
                graph.add_edge(id_, get_id(node.false_br), label="F")
                traverse(node.true_br)
                traverse(node.false_br)
            elif isinstance(node, EndNode):
                add_node(
                    id_,
                    color="black",
                    label="halt",
                    shape="ellipse",
                    content=f"{node.assertion}",
                )
            elif isinstance(node, AssertNode):
                add_node(
                    id_,
                    color="purple",
                    label="assert",
                    shape="house",
                    content=f"{node.assertion}",
                )
                graph.add_edge(id_, get_id(node.next_node))
                traverse(node.next_node)
            elif isinstance(node, AssumeNode):
                add_node(
                    id_,
                    color="pink",
                    label="assume",
                    shape="oval",
                    content=f"{node.expression}",
                )
                graph.add_edge(id_, get_id(node.next_node))
                traverse(node.next_node)
            elif isinstance(node, DummyNode):
                add_node(
                    id_, color="yellow", label="dummy", shape="star", content="???"
                )
            else:
                assert False

        traverse(self.cfg)

        graph.draw(path=filepath, prog="dot")


@dataclass(frozen=True)
class Function(BaseFunction):
    def get_proof_rule(self) -> Expr:
        rule = And(tuple(path.get_proof_rule() for path in get_paths(self.cfg)),)
        if self.vars:
            return ForAll(self.vars, rule)
        else:
            return rule

    def get_failing_paths(self) -> Iterator[BasicPath]:
        for path in get_paths(self.cfg):
            prop = path.get_proof_rule()
            solver = z3.Solver()
            solver.add(z3.Not(prop.as_z3()))
            if solver.check().r != -1:
                yield path

    def get_failing_props(self) -> Iterator[Expr]:
        for path in self.get_failing_paths():
            yield path.get_proof_rule()

    def check(self) -> CheckResult:
        """
        checks whether the function's proof rule is satisfiable
        if it is, `check()` returns an `Ok`/`HornOk` object
        otherwise, `check()` returns a `CounterExample`/`Unknown`/`HornFail` object
        """

        solver = z3.Solver()
        solver.add(z3.Not(self.get_proof_rule().as_z3()))
        result = solver.check()
        if result.r == 1:
            return CounterExample(solver.model())
        elif result.r == -1:
            return Ok()
        else:
            return Unknown(result.r)

    def check_iter(self) -> CheckResult:
        if next(self.get_failing_paths(), None) is None:
            return Ok()
        else:
            return Fail()


@dataclass(frozen=True)
class HornFunction(BaseFunction):
    invariants: list[Predicate]
    cutpoints: list[AssertNode]
    partial_invariants: list[Expr]

    def get_proof_rule(self) -> list[Expr]:
        vars = self.params + self.vars
        return [
            cast(Expr, ForAll(vars, path.get_proof_rule()))
            for path in get_paths(self.cfg)
        ] + [
            cast(Expr, ForAll(vars, Then(inv, partial_inv)))
            for inv, partial_inv in zip(self.invariants, self.partial_invariants)
        ]

    def __make_solver(self) -> z3.Solver:
        solver = z3.SolverFor("HORN")
        solver.set("engine", "spacer")
        # allow quantified variables in pobs
        solver.set("spacer.ground_pobs", False)
        # enable quantified generalization
        solver.set("spacer.q3.use_qgen", True)
        for p in self.get_proof_rule():
            solver.add(p.as_z3())
        return solver

    def check(self) -> CheckResult:
        solver = self.__make_solver()
        result = solver.check()
        if result.r == 1:
            model = solver.model()
            invariants: list[HornInvariant] = []
            for invariant in self.invariants:
                d = next(d for d in model.decls() if d.name() == invariant.name)
                fn = model.get_interp(d)
                assert isinstance(fn, z3.FuncInterp)
                else_value = fn.else_value()
                mapping = fn.as_list()
                if else_value is not None:
                    mapping = mapping[:-1]
                invariants.append(
                    HornInvariant(
                        invariant.name,
                        [(Expr.from_z3(x), Expr.from_z3(y)) for x, y in mapping],
                        None
                        if else_value is None
                        else Expr.from_z3(else_value, invariant.vars),
                    )
                )
            return HornOk(invariants)
        elif result.r == -1:
            return HornFail()
        else:
            return Unknown(result.r)

    def set_cutpoints(self):
        graph = nx.DiGraph()
        id2node: dict[int, CfgNode] = {}

        def get_id(node: CfgNode) -> int:
            return id(node)

        vars = self.vars + self.params
        sorts = [v.type_.as_z3() for v in vars]

        def traverse(node: CfgNode):
            id_ = get_id(node)
            if id_ in id2node:
                return
            id2node[id_] = node
            if isinstance(node, AssertNode):
                invariant = Predicate(
                    name=f"P{len(self.invariants)}",
                    arguments=cast("list[Expr]", vars),
                    sorts=sorts,
                    vars=vars,
                )
                self.invariants.append(invariant)
                self.partial_invariants.append(node.assertion)
                node.assertion = invariant
                self.cutpoints.append(node)
                traverse(node.next_node)
            elif isinstance(node, (StartNode, AssignmentNode, AssumeNode)):
                graph.add_node(id_,)
                graph.add_edge(id_, get_id(node.next_node))
                traverse(node.next_node)
            elif isinstance(node, CondNode):
                graph.add_node(id_,)
                graph.add_edge(id_, get_id(node.true_br))
                graph.add_edge(id_, get_id(node.false_br))
                traverse(node.true_br)
                traverse(node.false_br)
            elif isinstance(node, EndNode):
                graph.add_node(id_,)
            elif isinstance(node, DummyNode):
                graph.add_node(id_)
            else:
                assert False

        traverse(self.cfg)

        cycles = list(nx.simple_cycles(graph))
        node2cycle: dict[int, set[int]] = defaultdict(set)
        for i, c in enumerate(cycles):
            for n in c:
                node2cycle[n].add(i)

        cutpoints: list[int] = []
        while node2cycle:
            point = max(node2cycle, key=lambda n: len(node2cycle[n]))
            cutpoints.append(point)
            for i in node2cycle[point]:
                for n in cycles[i]:
                    if n == point:
                        continue
                    node2cycle[n].remove(i)
                    if not node2cycle[n]:
                        del node2cycle[n]
            del node2cycle[point]

        for cp in cutpoints:
            node_cp = id2node[cp]

            invariant = Predicate(
                name=f"P{len(self.invariants)}",
                arguments=cast("list[Expr]", vars),
                sorts=sorts,
                vars=vars,
            )
            self.invariants.append(invariant)
            new_node = AssertNode(node_cp.code_location, invariant, node_cp)
            self.cutpoints.append(new_node)
            for n in graph.predecessors(cp):
                node = id2node[n]
                if isinstance(
                    node, (AssertNode, AssignmentNode, StartNode, AssumeNode),
                ):
                    node.next_node = new_node
                elif isinstance(node, CondNode):
                    if node.true_br is node_cp:
                        node.true_br = new_node
                    else:
                        node.false_br = new_node
                else:
                    assert False, f"unexpected node of type {type(node)}"

    @classmethod
    def from_ast(cls, filename: str, ast: AstNode) -> HornFunction:
        base = super().from_ast(
            filename, ast, invariants=[], cutpoints=[], partial_invariants=[]
        )
        assert isinstance(base, HornFunction)
        base.set_cutpoints()
        return base

