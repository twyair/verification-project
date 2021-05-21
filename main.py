from __future__ import annotations
import json
import os

from cast import parse, AstType
from function import BaseFunction, Function, HornFunction


PATH = "benchmarks/{}.json"


def get_functions(filename: str, horn: bool = False) -> dict[str, BaseFunction]:
    err = os.system(f'./comp-benchmark.sh "{filename}"')
    if err != 0:
        raise Exception(f"error code: {err}")

    with open(PATH.format(filename)) as f:
        ast = parse(json.load(f))

    assert ast.type == AstType.translation_unit

    return {
        f.name: f
        for f in (
            (HornFunction if horn else Function).from_ast(filename, child)
            for child in ast.children
            if child.type == AstType.function_definition
        )
    }
