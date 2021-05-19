from cfg import StartNode
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
        program=f.get_code_as_html(),
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
        curr_line=first_line,  # FIXME
        total_lines=501,  # FIXME
    )
