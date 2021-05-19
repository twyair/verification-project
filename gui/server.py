from __future__ import annotations
import itertools
from html import escape
from function import Function
from cfg import BasicPath, StartNode
from flask import Flask, render_template
import z3
from main import get_functions
from expr import And, Not

app = Flask(__name__)


@app.route("/")
def hello_world():
    return "<p>Hello, World!</p>"


def get_ranges(path):
    return [n.code_location for n in path.nodes if n.code_location is not None]


def range_to_class(r) -> str:
    return f"range_{r.start_line}_{r.start_column}_{r.end_line}_{r.end_column}"


@app.route("/<filename>/<func>")
def _(filename: str, func: str):
    fns = get_functions(filename)
    f = fns[func]

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
        s.add(Not(None, path.get_proof_rule()).as_z3())
        s.check()
        models.append(s.model())

    assert isinstance(f.cfg, StartNode)
    first_line = (f.cfg.code_location or f.cfg.next_node.code_location).start_line - 5

    return render_template(
        "code.html",
        program=fin_src,
        ok=not paths,
        props=props,
        paths=enumerate(
            {
                "reachability": str(And(None, tuple(path.reachability))),
                "transformation": [
                    f"{var} := {val}" for var, val in path.transformation.items()
                ],
                "model": [
                    f"{var.name()} := {model.get_interp(var)}" for var in model.decls()
                ],
            }
            for path, model in zip(paths, models)
        ),
        path_classes=str(
            {
                str(index): [range_to_class(r) for r in get_ranges(path)]
                for index, path in enumerate(paths)
            }
        ),
        curr_line=ranges[0].start_line - 2,
        total_lines=len(lines),
    )
