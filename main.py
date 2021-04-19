from dataclasses import dataclass
import json
from typing import Dict, List, Tuple

from cast import AstNode, parse, AstType
from cfg import (
    AssignmentNode,
    CfgNode,
    CondNode,
    EndNode,
    StartNode,
    make_expr,
    create_cfg,
)
from expr import BinBoolExpr, BoolExpr
from functools import reduce


def get_first_child(node: AstNode, pred) -> AstNode:
    return next(c for c in node.children if pred(c))


def find_ensures(fn: AstNode) -> AstNode:
    statements = fn.children[-1].children[1].children
    for s in statements:
        if (
            s.type == AstType.expression_statement
            and s.children[0].type == AstType.postfix_expression
            and s.children[0].children[1].type == AstType.paren_left
            and s.children[0].children[0].type == AstType.IDENTIFIER
            and s.children[0].children[0].text in ("ensures", "assert")
        ):
            return s.children[0].children[2]
    assert False


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
    cfg: CfgNode
    q2: BoolExpr
    name: str

    @staticmethod
    def from_ast(ast: AstNode) -> "Function":
        name = get_first_child(
            get_first_child(ast, lambda c: c.type == AstType.direct_declarator),
            lambda c: c.type == AstType.IDENTIFIER,
        ).text
        assert name is not None
        ensures = make_expr(find_ensures(ast))
        assert isinstance(ensures, BoolExpr)
        return Function(q2=ensures, cfg=create_cfg(ast), name=name)

    def get_proof_rule(self) -> List[Tuple[BoolExpr, BoolExpr]]:
        rts = list(self.cfg.generate_rt([], {}))
        return [
            (reduce(lambda acc, x: BinBoolExpr("&&", acc, x), r), self.q2.assign(t))
            for r, t in rts
        ]

    def get_proof_rule_as_string(self) -> str:
        return "\n".join(
            f"{r[0]} → {r[1]}".replace("<=", "≤")
            .replace(">=", "≥")
            .replace("==", "=")
            .replace("!=", "≠")
            .replace("&&", "∧")
            .replace("||", "∨")
            .replace("!", "¬")
            for r in self.get_proof_rule()
        )

    def draw_cfg(self):
        import networkx as nx
        from networkx.drawing.nx_pydot import graphviz_layout
        import matplotlib.pyplot as plt

        G = nx.DiGraph()

        id2node = {}

        def get_id(node: CfgNode) -> int:
            if isinstance(node, EndNode):
                return 0
            else:
                return id(node)

        def traverse(node: CfgNode):
            id2node[get_id(node)] = node
            if isinstance(node, (StartNode, AssignmentNode)):
                G.add_edge(get_id(node), get_id(node.next_node))
                traverse(node.next_node)
            elif isinstance(node, CondNode):
                G.add_edge(get_id(node), get_id(node.true_br))
                G.add_edge(get_id(node), get_id(node.false_br))
                traverse(node.true_br)
                traverse(node.false_br)

        traverse(self.cfg)

        edge_colors = []
        for u, v in G.edges:
            nu = id2node[u]
            nv = id2node[v]
            if isinstance(nu, CondNode):
                if nu.true_br is nv:
                    edge_colors.append("blue")
                else:
                    edge_colors.append("red")
            else:
                edge_colors.append("black")

        node_colors = []
        for node_id in G:
            if isinstance(id2node[node_id], AssignmentNode):
                node_colors.append("blue")
            elif isinstance(id2node[node_id], CondNode):
                node_colors.append("red")
            elif isinstance(id2node[node_id], StartNode):
                node_colors.append("green")
            else:
                node_colors.append("black")

        nx.draw(
            G,
            graphviz_layout(G, prog="dot"),
            node_shape="s",
            node_color=node_colors,
            node_size=400,
            width=4,
            edge_color=edge_colors,
        )
        plt.show()
