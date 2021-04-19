import json
from typing import Iterator, Tuple
from cast import AstNode, parse, AstType

def get_first_child(node: AstNode, pred) -> AstNode:
    return next(c for c in node.children if pred(c))

def get_functions(ast: AstNode) -> Iterator[Tuple[str, AstNode]]:
    assert ast.type == AstType.translation_unit

    for child in ast.children:
        if child.type == AstType.function_definition:
            name = get_first_child(get_first_child(child, lambda c: c.type == AstType.direct_declarator), lambda c: c.type == AstType.IDENTIFIER).text
            assert name is not None
            yield name, child

PATH = "../Teaching.Verification.Project/benchmarks/c/json/max3.c.ast.json"

with open(PATH) as f:
    ast = parse(json.load(f))

functions = dict(get_functions(ast))