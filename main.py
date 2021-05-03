import json
import os
from dataclasses import dataclass
from functools import reduce
from typing import Dict, List, Optional

import z3
from pygraphviz.agraph import AGraph

from cast import AstNode, AstType, parse
from cfg import (
    AssertNode,
    AssignmentNode,
    BasicPath,
    CfgNode,
    CondNode,
    DummyNode,
    EndNode,
    StartNode,
    create_cfg,
)
from expr import And, Environment, ForAll, Expr, Prop, Type, Variable


@dataclass
class CheckResult:
    def is_sat(self) -> bool:
        return False


@dataclass
class Unknown(CheckResult):
    code: int


@dataclass
class Sat(CheckResult):
    def is_sat(self) -> bool:
        return True


@dataclass
class Unsat(CheckResult):
    model: z3.ModelRef


def get_first_child(node: AstNode, pred) -> AstNode:
    return next(c for c in node.children if pred(c))


def find_ensures(fn: AstNode, name: str) -> Optional[AstNode]:
    statements = fn[-1][1].children
    for s in statements:
        if (
            s.type == AstType.expression_statement
            and s[0].type == AstType.postfix_expression
            and s[0][1].type == AstType.paren_left
            and s[0][0].type == AstType.IDENTIFIER
            and s[0][0].text == name
        ):
            return s[0][2]
    return None


PATH = "benchmarks/{}.json"


def get_functions(filename: str) -> Dict[str, "Function"]:
    err = os.system(f'./comp-benchmark.sh "{filename}"')
    if err != 0:
        raise Exception(f"error code: {err}")

    with open(PATH.format(filename)) as f:
        ast = parse(json.load(f))

    assert ast.type == AstType.translation_unit

    return {
        f.name: f
        for f in (
            Function.from_ast(child)
            for child in ast.children
            if child.type == AstType.function_definition
        )
    }


@dataclass
class Function:
    name: str
    cfg: CfgNode
    params: Dict[str, Type]
    vars: Dict[str, Type]

    @staticmethod
    def from_ast(ast: AstNode) -> "Function":
        declarator = get_first_child(ast, lambda c: c.type == AstType.direct_declarator)
        fn_name = get_first_child(
            declarator, lambda c: c.type == AstType.IDENTIFIER,
        ).text
        assert fn_name is not None
        assert ast.type == AstType.function_definition
        ret_type = ast[0].text
        assert ret_type is not None
        env = Environment.empty()
        if ret_type != "void":
            env["ret"] = Type(ret_type)
        params = declarator[2]
        if params.type == AstType.parameter_list:
            for p in params.children:
                if p.type == AstType.parameter_declaration:
                    ty = p[0].text
                    assert ty is not None and ty in ("int", "float", "bool",)
                    name = None
                    if p[1].type == AstType.IDENTIFIER:
                        name = p[1].text
                    elif (
                        p[1].type == AstType.direct_declarator
                        and p[1][0].type == AstType.IDENTIFIER
                        and p[1][1].text == "["
                    ):
                        name = p[1][0].text
                        ty = "array_" + ty
                    assert name is not None
                    env[name] = Type(ty)
        params = env.get_vars()
        requires = find_ensures(ast, "requires")
        if requires is not None:
            requires = Prop.from_ast(requires, env)
        cfg = create_cfg(ast, requires, env)
        vars = env.get_vars()
        for p in params:
            del vars[p]
        return Function(cfg=cfg, name=fn_name, vars=vars, params=params)

    def get_proof_rule(self) -> Expr:
        def add_quantifiers(prop: Expr) -> Expr:
            return reduce(
                lambda acc, x: ForAll(Variable(*x), x[1], acc), self.vars.items(), prop
            )

        rule = reduce(
            lambda acc, x: And(acc, x),
            [
                path.get_proof_rule()
                for path in self.cfg.generate_paths(BasicPath.empty(), frozenset())
            ],
        )
        return add_quantifiers(rule)

    def get_proof_rule_as_string(self) -> str:
        return str(self.get_proof_rule())

    def get_failing_props(self) -> List[Prop]:
        props: List[Prop] = []
        for path in self.cfg.generate_paths(BasicPath.empty(), frozenset()):
            prop = path.get_proof_rule()
            solver = z3.Solver()
            solver.add(z3.Not(prop.as_z3()))
            if solver.check().r == 1:
                for x in props:
                    if x == prop:
                        break
                else:
                    props.append(prop)
        return props

    def check(self) -> CheckResult:
        """
        checks whether the function's proof rule is satisfiable
        if it is, `check()` returns a `Sat` object
        otherwise, `check()` returns an `Unsat`/`Unknown` object
        """
        solver = z3.Solver()
        solver.add(z3.Not(self.get_proof_rule().as_z3()))
        result = solver.check()
        if result.r == 1:
            return Unsat(solver.model())
        elif result.r == -1:
            return Sat()
        else:
            return Unknown(result.r)

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
                    shape="octagon",
                    content=f"{node.assertion}",
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
