from dataclasses import dataclass
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
    EndNode,
    StartNode,
    create_cfg,
)
from prop import And, ForAll, Prop


def get_first_child(node: AstNode, pred) -> AstNode:
    return next(c for c in node.children if pred(c))


def find_ensures(fn: AstNode) -> Optional[AstNode]:
    statements = fn[-1][1].children
    for s in statements:
        if (
            s.type == AstType.expression_statement
            and s[0].type == AstType.postfix_expression
            and s[0][1].type == AstType.paren_left
            and s[0][0].type == AstType.IDENTIFIER
            and s[0][0].text == "ensures"
        ):
            return s[0][2]
    return None


PATH = "../Teaching.Verification.Project/benchmarks/c/json/{}.ast.json"


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

    @staticmethod
    def from_ast(ast: AstNode) -> "Function":
        name = get_first_child(
            get_first_child(ast, lambda c: c.type == AstType.direct_declarator),
            lambda c: c.type == AstType.IDENTIFIER,
        ).text
        assert name is not None
        ensures = find_ensures(ast)
        if ensures is not None:
            ensures = Prop.from_ast(ensures)
        return Function(cfg=create_cfg(ast, ensures), name=name)

    def get_proof_rule(self) -> Prop:
        rule = reduce(
            lambda acc, x: And(acc, x),
            [
                path.get_proof_rule()
                for path in self.cfg.generate_paths(BasicPath.empty(), frozenset())
            ],
        )
        free_vars = rule.free_vars(frozenset(["ret",]))
        # FIXME: set the domain of `ForAll`
        return reduce(lambda acc, x: ForAll(x, None, acc), free_vars, rule)

    def get_proof_rule_as_string(self) -> str:
        return str(self.get_proof_rule())

    def draw_cfg(self):
        import networkx as nx
        from networkx.drawing.nx_agraph import pygraphviz_layout
        import matplotlib.pyplot as plt

        graph = nx.DiGraph()
        id2node: Dict = {}
        edge_labels = {}
        node_colors = []
        # node_colors = {}

        def get_id(node: CfgNode) -> int:
            return id(node)

        def traverse(node: CfgNode):
            id_ = get_id(node)
            if id_ in id2node:
                return
            id2node[id_] = node
            if isinstance(node, (StartNode,)):
                # node_colors[id_] = "green"
                graph.add_edge(id_, get_id(node.next_node))
                traverse(node.next_node)
            elif isinstance(node, AssignmentNode):
                # node_colors[id_] = "blue"
                graph.add_edge(id_, get_id(node.next_node))
                traverse(node.next_node)
            elif isinstance(node, CondNode):
                # node_colors[id_] = "red"
                id_t, id_f = get_id(node.true_br), get_id(node.false_br)
                edge_labels[(id_, id_t)] = "T"
                edge_labels[(id_, id_f)] = "F"
                graph.add_edge(id_, id_t)
                graph.add_edge(id_, id_f)
                traverse(node.true_br)
                traverse(node.false_br)
            elif isinstance(node, EndNode):
                pass
                # node_colors[get_id(node)] = "black"
            elif isinstance(node, AssertNode):
                graph.add_edge(id_, get_id(node.next_node))
                traverse(node.next_node)
            else:
                assert False

        traverse(self.cfg)

        for node_id in graph:
            node = id2node[node_id]
            if isinstance(node, AssignmentNode):
                node_colors.append("blue")
            elif isinstance(node, CondNode):
                node_colors.append("red")
            elif isinstance(node, StartNode):
                node_colors.append("green")
            elif isinstance(node, EndNode):
                node_colors.append("black")
            elif isinstance(node, AssertNode):
                node_colors.append("purple")
            else:
                assert False

        pos = pygraphviz_layout(
            graph, prog="dot", root=get_id(self.cfg)
        )  # , args="-Granksep=2")

        nx.draw(
            graph, pos, node_shape="s", node_color=node_colors, node_size=400, width=4,
        )
        nx.draw_networkx_edge_labels(graph, pos, edge_labels)
        plt.show()
