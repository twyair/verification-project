import json
from typing import Iterator, List, Tuple
from cast import AstNode, parse, AstType
from cfg import AssignmentNode, CfgNode, CondNode, StartNode, make_expr, create_cfg
from expr import BinBoolExpr, BoolExpr
from functools import reduce
import networkx as nx
import matplotlib.pyplot as plt

def get_first_child(node: AstNode, pred) -> AstNode:
    return next(c for c in node.children if pred(c))

def find_ensures(fn: AstNode) -> AstNode:
    statements = fn.children[-1].children[1].children
    for s in statements:
        if s.type == AstType.expression_statement and s.children[0].type == AstType.postfix_expression and s.children[0].children[1].type == AstType.paren_left and s.children[0].children[0].type == AstType.IDENTIFIER and s.children[0].children[0].text in ("ensures", "assert"):
            return s.children[0].children[2]
    assert False

def get_functions(ast: AstNode) -> Iterator[Tuple[str, Tuple[BoolExpr, AstNode]]]:
    assert ast.type == AstType.translation_unit

    for child in ast.children:
        if child.type == AstType.function_definition:
            name = get_first_child(get_first_child(child, lambda c: c.type == AstType.direct_declarator), lambda c: c.type == AstType.IDENTIFIER).text
            assert name is not None
            ensures = find_ensures(child)
            yield name, (make_expr(ensures), child)

PATH = "../Teaching.Verification.Project/benchmarks/c/json/array.ii.ast.json"

with open(PATH) as f:
    ast = parse(json.load(f))

functions = dict(get_functions(ast))


def get_proof_rule(fn: AstNode, q2: BoolExpr) -> List[Tuple[BoolExpr, BoolExpr]]:
    cfg = create_cfg(fn)
    rts = list(cfg.generate_rt([], {}))
    return [
        (reduce(lambda acc, x: BinBoolExpr("&&", acc, x), r), q2.assign(t)) for r, t in rts
    ]

def proof_rule_as_string(rule: Tuple[BoolExpr, BoolExpr]) -> str:
    return f"{rule[0]} → {rule[1]}"

def cfg_as_graph(cfg: CfgNode):
    G = nx.DiGraph()
    labels = {}
    def traverse(node: CfgNode):
        labels[id(node)] = str(type(node))
        if isinstance(node, (StartNode, AssignmentNode)):
            G.add_edge(id(node), id(node.next_node))
            traverse(node.next_node)
        elif isinstance(node, CondNode):
            G.add_edge(id(node), id(node.true_br))
            G.add_edge(id(node), id(node.false_br))
            traverse(node.true_br)
            traverse(node.false_br)
    traverse(cfg)
    nx.draw(G)
    plt.draw()
    plt.show()