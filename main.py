from __future__ import annotations
import json
import os

from cast import parse, AstType
from function import BaseFunction, Function, HornFunction


def compile_functions(filename: str, horn: bool = False) -> dict[str, BaseFunction]:
    err = os.system(f'./comp-benchmark.sh "{filename}"')
    if err != 0:
        raise Exception(f"error code: {err}")
    return get_functions(f"benchmarks/{filename}.json")


def get_functions(path: str, horn: bool = False) -> dict[str, BaseFunction]:
    with open(path) as f:
        ast = parse(json.load(f))

    assert ast.type == AstType.translation_unit

    return {
        f.name: f
        for f in (
            (HornFunction if horn else Function).from_ast(path, child)
            for child in ast.children
            if child.type == AstType.function_definition
        )
    }
