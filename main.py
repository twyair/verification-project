from dataclasses import dataclass

from expr import Environment, VarExpr
import json
from typing import Dict, Optional
from functools import reduce

from cast import AstNode, parse, AstType
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
from prop import And, Prop, ForAll


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
    vars: Dict[str, str]

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
        env["ret"] = ret_type
        params = declarator[2]
        if params.type == AstType.parameter_list:
            for p in params.children:
                if p.type == AstType.parameter_declaration:
                    ty = p[0].text
                    assert ty is not None and ty in ("int",)  # TODO: add more types
                    name = None
                    if p[1].type == AstType.IDENTIFIER:
                        name = p[1].text
                    elif (
                        p[1].type == AstType.direct_declarator
                        and p[1][0].type == AstType.IDENTIFIER
                        and p[1][1].text == "["
                    ):
                        name = p[1][0].text
                        ty = "array-" + ty
                    assert name is not None
                    env[name] = ty
        requires = find_ensures(ast, "requires")
        if requires is not None:
            requires = Prop.from_ast(requires, env)
        ensures = find_ensures(ast, "ensures")
        if ensures is not None:
            ensures = Prop.from_ast(ensures, env)
        cfg = create_cfg(ast, requires, ensures, env)
        return Function(cfg=cfg, name=fn_name, vars=env.vars)

    def get_proof_rule(self) -> Prop:
        rule = reduce(
            lambda acc, x: And(acc, x),
            [
                path.get_proof_rule()
                for path in self.cfg.generate_paths(BasicPath.empty(), frozenset())
            ],
        )
        return reduce(
            lambda acc, x: ForAll(VarExpr(*x), x[1], acc), self.vars.items(), rule
        )

    def get_proof_rule_as_string(self) -> str:
        return str(self.get_proof_rule())

    def draw_cfg(self):
        from pygraphviz.agraph import AGraph

        # import matplotlib.pyplot as plt
        # import matplotlib.image as image

        filepath = f"cfg-img/{self.name}.svg"

        graph = AGraph(directed=True)
        ids = set()

        def get_id(node: CfgNode) -> int:
            return id(node)

        def traverse(node: CfgNode):
            id_ = get_id(node)
            if id_ in ids:
                return
            ids.add(id_)
            if isinstance(node, (StartNode,)):
                graph.add_node(id_, color="green", label="start")
                graph.add_edge(id_, get_id(node.next_node))
                traverse(node.next_node)
            elif isinstance(node, AssignmentNode):
                graph.add_node(id_, color="blue", label="assign")
                graph.add_edge(id_, get_id(node.next_node))
                traverse(node.next_node)
            elif isinstance(node, CondNode):
                graph.add_node(id_, color="red", label="condition")
                graph.add_edge(id_, get_id(node.true_br), label="T")
                graph.add_edge(id_, get_id(node.false_br), label="F")
                traverse(node.true_br)
                traverse(node.false_br)
            elif isinstance(node, EndNode):
                graph.add_node(id_, color="black", label="halt")
            elif isinstance(node, AssertNode):
                graph.add_node(id_, color="purple", label="assert")
                graph.add_edge(id_, get_id(node.next_node))
                traverse(node.next_node)
            elif isinstance(node, DummyNode):
                graph.add_node(id_, color="yellow", label="dummy")
            else:
                assert False

        traverse(self.cfg)

        graph.draw(path=filepath, prog="dot")

        # plt.imshow(image.imread(filepath))
        # plt.show()
