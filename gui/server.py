from __future__ import annotations
from cast import AstRange
import itertools
from html import escape
import os
from function import Function, HornFunction, HornOk
from cfg import BasicPath, StartNode
from flask import Flask, render_template
import z3
from main import get_functions
from expr import And, Not

app = Flask(__name__)


@app.route("/")
def index() -> str:
    files = [f[:-2] for f in os.listdir("benchmarks") if f.endswith(".c")]
    return "\n".join(f"<p><a href='{f}/index.html'>{f}</a></p>" for f in files)


@app.route("/<filename>/index.html")
def view_file(filename: str) -> str:
    with open(f"benchmarks/{filename}.c") as src:
        src = src.read()
    fns = get_functions(filename)
    return render_template("view_file.html.jinja", functions=list(fns), program=src)


def get_ranges(path: BasicPath) -> list[AstRange]:
    return [n.code_location for n in path.nodes if n.code_location is not None]


def range_to_class(r: AstRange) -> str:
    return f"range_{r.start_line}_{r.start_column}_{r.end_line}_{r.end_column}"


@app.route("/<filename>/<func>/verify.html")
def verify_func(filename: str, func: str) -> str:
    fns = get_functions(filename)
    f = fns[func]
    assert isinstance(f, Function)

    with open(f"benchmarks/{filename}.c") as src:
        src = src.read()

    ranges = sorted(
        set(
            itertools.chain.from_iterable(
                get_ranges(p) for p in f.cfg.generate_paths(BasicPath.empty(), set())
            )
        )
    )

    lines = src.splitlines()
    fin_src = ""
    line_number = 0  # 0-based
    column_number = 0  # 0-based

    def copy_until_line(
        fin_src: str, line_number: int, column_number: int, lim: int
    ) -> tuple[str, int, int]:
        while line_number < lim:
            fin_src += escape(lines[line_number][column_number:] + "\n")
            column_number = 0
            line_number += 1
        return fin_src, line_number, column_number

    for r in ranges:
        fin_src, line_number, column_number = copy_until_line(
            fin_src, line_number, column_number, r.start_line - 1
        )
        fin_src += escape(lines[line_number][column_number : r.start_column - 1])
        column_number = r.start_column - 1
        fin_src += "<span class={}>".format(range_to_class(r))
        fin_src, line_number, column_number = copy_until_line(
            fin_src, line_number, column_number, r.end_line - 1
        )
        fin_src += escape(lines[line_number][column_number : r.end_column - 1])
        column_number = r.end_column - 1
        fin_src += "</span>"
    fin_src, line_number, column_number = copy_until_line(
        fin_src, line_number, column_number, len(lines)
    )

    paths = list(f.get_failing_paths())
    props = enumerate(str(p.get_proof_rule()) for p in paths)
    models = []
    for path in paths:
        s = z3.Solver()
        s.add(Not(path.get_proof_rule()).as_z3())
        s.check()
        models.append(s.model())

    return render_template(
        "code.html.jinja",
        program=fin_src,
        ok=not paths,
        props=props,
        paths=enumerate(
            {
                "reachability": str(And(tuple(path.reachability))),
                "transformation": [
                    f"{var} := {val}" for var, val in path.transformation.items()
                ],
                "model": [
                    f"{var.name()} := {model.get_interp(var)}" for var in model.decls()
                ],
                "classes": [range_to_class(r) for r in get_ranges(path)],
            }
            for path, model in zip(paths, models)
        ),
        path_classes=str(
            {
                index: [range_to_class(r) for r in get_ranges(path)]
                for index, path in enumerate(paths)
            }
        ),
        curr_line=ranges[0].start_line - 2,
        total_lines=len(lines),
    )


@app.route("/<filename>/<func>/horn.html")
def horn(filename: str, func: str) -> str:
    fns = get_functions(filename, horn=True)
    f = fns[func]
    assert isinstance(f, HornFunction)

    min_range = min(
        itertools.chain.from_iterable(
            get_ranges(p) for p in f.cfg.generate_paths(BasicPath.empty(), set())
        )
    )

    with open(f"benchmarks/{filename}.c") as src:
        src = src.read()

    result = f.check()

    return render_template(
        "horn.html.jinja",
        program=src,
        ok=result.is_ok(),
        invariants=[
            {"index": i, "name": inv.name, "expr": str(inv)}
            for i, inv in enumerate(result.invariants)
        ]
        if isinstance(result, HornOk)
        else None,
        curr_line=min_range.start_line - 2,
        total_lines=src.count("\n"),
    )

