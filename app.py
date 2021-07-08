from __future__ import annotations

import json
import subprocess
from html import escape
from dataclasses import asdict
from typing import Any, cast
import os

import z3
from flask import Flask, request

from cast import AstRange
from cfg import BasicPath
from expr import And, Not
from function import BaseFunction, Function, HornFunction, HornOk
from main import get_functions

app = Flask(__name__)
app.config["SEND_FILE_MAX_AGE_DEFAULT"] = 0


@app.route("/")
def index():
    return open("index.html").read()


@app.route("/benchmarks")
def list_benchmarks():
    return json.dumps([f for f in os.listdir("benchmarks") if f.endswith(".c")])


@app.route("/get_source", methods=["GET"])
def get_source():
    filename = request.args.get("filename")
    with open(f"benchmarks/{filename}") as f:
        code = f.read()
    return {"code": code}


def get_ranges(path: BasicPath) -> list[AstRange]:
    return [n.code_location for n in path.nodes if n.code_location is not None]


def get_function(horn: bool) -> BaseFunction | dict[str, Any]:
    req: dict[str, Any] = request.get_json()
    assert req is not None
    with open("tmp/code.c", "w") as f:
        f.write(req["code"])
    res = subprocess.run(["./comp-benchmark.sh", "code"])
    if res.returncode != 0:
        return {"ok": False, "returncode": res.returncode, "err": res.stderr}

    fns = get_functions("tmp/code.json", horn=horn)
    subprocess.run(["rm"] + ["tmp/code." + s for s in ["c", "c1", "ii", "json"]])
    assert len(fns) == 1
    return next(iter(fns.values()))


@app.route("/verify", methods=["POST"])
def verify():
    f = get_function(horn=False)
    if isinstance(f, dict):
        return f
    assert isinstance(f, Function)

    try:
        paths = list(f.get_failing_paths())
    except Exception as e:
        return dict(ok=False, err=str(e))
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


@app.route("/horn", methods=["POST"])
def horn():
    f = get_function(horn=True)
    if isinstance(f, dict):
        return f
    assert isinstance(f, HornFunction)

    result = f.check()
    if isinstance(result, HornOk):

        ranges = [cast(AstRange, cp.code_location) for cp in f.cutpoints]
        assert all(r is not None for r in ranges)

        invariants = [
            dict(
                index=i,
                name=escape(inv.name),
                expr=escape(str(inv)),
                range=asdict(rng),
            )
            for i, (inv, rng) in enumerate(zip(result.invariants, ranges))
        ]

        return dict(ok=True, verified=True, invariants=invariants)
    else:
        return dict(ok=True, verified=False)
