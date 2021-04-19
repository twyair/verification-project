import json
from typing import List
from cast import AstNode, parse

def get_functions(ast: AstNode) -> List[AstNode]:
    pass

PATH = "../Teaching.Verification.Project/benchmarks/c/json/max3.c.ast.json"

with open(PATH) as f:
    ast = parse(json.load(f))

functions = get_functions(ast)