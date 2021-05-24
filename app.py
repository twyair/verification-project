from __future__ import annotations

import json
import subprocess
from html import escape
from dataclasses import asdict
from typing import Any

import z3
from flask import Flask, request

from cast import AstRange
from cfg import BasicPath
from expr import And, Not
from function import Function
from main import get_functions

app = Flask(__name__)
app.config["SEND_FILE_MAX_AGE_DEFAULT"] = 0


@app.route("/")
def index():
    return open("index.html").read()


@app.route("/benchmarks")
def list_benchmarks():
    return json.dumps(["list your", "benchmakrs", "here"])


def get_ranges(path: BasicPath) -> list[AstRange]:
    return [n.code_location for n in path.nodes if n.code_location is not None]


@app.route("/verify", methods=["POST"])
def verify():
    req: dict[str, Any] = request.get_json()
    assert req is not None
    with open("tmp/code.c", "w") as f:
        f.write(req["code"])
    res = subprocess.run(["./comp-benchmark.sh", "code"])
    if res.returncode != 0:
        return {"ok": False, "returncode": res.returncode, "stderr": res.stderr}

    fns = get_functions("tmp/code.json")
    subprocess.run(["rm"] + ["tmp/code." + s for s in ["c", "c1", "ii", "json"]])
    assert len(fns) == 1
    f = next(iter(fns.values()))
    assert isinstance(f, Function)

    paths = list(f.get_failing_paths())
    models = []
    for path in paths:
        s = z3.Solver()
        s.add(Not(path.get_proof_rule()).as_z3())
        assert s.check().r == 1
        models.append(s.model())

    paths_ = [
        {
            "index": index,
            "reachability": escape(str(And(tuple(path.reachability))))
            if path.reachability
            else "True",
            "transformation": [
                escape(f"{var} := {val}") for var, val in path.transformation.items()
            ],
            "model": [
                escape(f"{var.name()} := {model.get_interp(var)}")
                for var in model.decls()
            ],
            "ranges": [asdict(r) for r in get_ranges(path)],
            "prop": escape(str(path.get_proof_rule())),
        }
        for index, (path, model) in enumerate(zip(paths, models))
    ]

    return {"ok": True, "body": paths_, "verified": not paths_}
