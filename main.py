import json
import os
from typing import Dict

from cast import parse, AstType
from function import Function


PATH = "benchmarks/{}.json"


def get_functions(filename: str, horn: bool = False) -> Dict[str, "Function"]:
    err = os.system(f'./comp-benchmark.sh "{filename}"')
    if err != 0:
        raise Exception(f"error code: {err}")

    with open(PATH.format(filename)) as f:
        ast = parse(json.load(f))

    assert ast.type == AstType.translation_unit

    return {
        f.name: f
        for f in (
            Function.from_ast(child, horn=horn)
            for child in ast.children
            if child.type == AstType.function_definition
        )
    }
