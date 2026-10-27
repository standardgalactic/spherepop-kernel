#!/usr/bin/env python3
"""Random differential test between the Go and Python implementations.

For N random (term, configuration, strategy) triples it
  1. has the Go CLI reduce the term and write a trace, and has the Python
     verifier check it;
  2. has the Python reducer write a trace, and has the Go CLI check it;
  3. compares the two traces step for step (they must be identical, since
     a strategy is a function).
Any disagreement is printed and the exit status is 1.

    python3 crosscheck.py [N] [SEED] [path/to/spherepop]
"""
import json
import os
import random
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "tools", "verify-py"))
sys.path.insert(0, HERE)
import spherepop_verify as V  # noqa: E402
import gen_corpus as G  # noqa: E402

sys.setrecursionlimit(100000)
N = int(sys.argv[1]) if len(sys.argv) > 1 else 300
SEED = int(sys.argv[2]) if len(sys.argv) > 2 else 1
GO = sys.argv[3] if len(sys.argv) > 3 else None
rng = random.Random(SEED)
tmp = tempfile.mkdtemp()
if GO is None:
    GO = os.path.join(tmp, "spherepop")
    subprocess.check_call(["go", "build", "-o", GO, "./cmd/spherepop"], cwd=os.path.join(HERE, ".."))

leaves = ["a", "b", "c", "x", "S", "K", "I", "B", "C", "W", "S", "K"]


def rterm(depth):
    r = rng.random()
    if depth <= 0 or r < 0.2:
        return rng.choice(leaves)
    if r < 0.55:
        return "%s (%s)" % (rterm(depth - 1), rterm(depth - 1))
    if r < 0.68:
        return "sc_%s (%s)" % (rng.choice("pq"), rterm(depth - 1))
    if r < 0.85:
        return "<%s>_%s" % (rterm(depth - 1), rng.choice("pq"))
    return "%s %s" % (rterm(depth - 1), rterm(depth - 1))


bad = 0
stats = {}
for n in range(N):
    spec = {
        "root": [x for x in G.ALL if rng.random() < 0.8],
        "perm": {"p": [x for x in G.ALL if rng.random() < 0.6], "q": [x for x in G.ALL if rng.random() < 0.4]},
        "gated": [],
        "absorb": rng.choice(V.ABSORB_MODES),
        "sc": rng.choice(V.SCOPE_MODES),
    }
    src = rterm(rng.choice([3, 4, 5]))
    try:
        V.parse_term(src)
    except V.Syntax:
        continue
    strat = rng.choice(V.STRATEGIES)
    fuel = rng.choice([5, 20, 60])
    perms = [a for l, p in spec["perm"].items() for a in ["--perm", "%s=%s" % (l, ",".join(p))]]
    gf = os.path.join(tmp, "go.json")
    # The Go CLI has no flag for the gated set, so only the default is compared there.
    spec["gated"] = ["W", "K", "C"]  # the Go CLI has no flag for the gated set
    root_arg = ",".join(spec["root"]) if spec["root"] else ""
    cmd = [GO, "reduce", src, "--root", root_arg, "--absorb", spec["absorb"], "--sc", spec["sc"],
           "--strategy", strat, "--fuel", str(fuel), "--out", gf] + [
        a for l in ("p", "q") for a in ["--perm", "%s=%s" % (l, ",".join(spec["perm"][l]))]]
    r = subprocess.run(cmd, capture_output=True, text=True)
    if not os.path.exists(gf):
        print("go reduce failed", cmd, r.stderr)
        bad += 1
        continue
    # 1. Go trace, Python check.
    gdoc = json.load(open(gf))
    os.remove(gf)
    spec_go = gdoc["config"]
    path = os.path.join(tmp, "g.json")
    json.dump(gdoc, open(path, "w"))
    try:
        V.check_trace(V.strict_load(open(path).read(), V.TRACE_SHAPE, "format"), True)
    except V.Reject as e:
        print("PYTHON REJECTS GO TRACE", src, spec_go, strat, e.cls, e.msg)
        bad += 1
    # 2. Python trace, Go check.
    pdoc = G.mk_trace(src, spec_go, strat, fuel)
    pp = os.path.join(tmp, "p.json")
    json.dump(pdoc, open(pp, "w"), indent=2)
    c = subprocess.run([GO, "check", pp, "--strategy"], capture_output=True, text=True)
    if c.returncode != 0:
        print("GO REJECTS PYTHON TRACE", src, spec_go, strat, c.stdout.strip(), c.stderr.strip())
        bad += 1
    for st in pdoc["steps"]:
        stats[st["rule"]] = stats.get(st["rule"], 0) + 1
    # 3. Identical traces.
    if [(s["rule"], s["path"], s["after"]) for s in gdoc["steps"]] != [(s["rule"], s["path"], s["after"]) for s in pdoc["steps"]] \
            or gdoc["head"] != pdoc["head"] or gdoc["final"] != pdoc["final"] or gdoc["exhausted"] != pdoc["exhausted"]:
        print("TRACES DIFFER", src, spec_go, strat)
        bad += 1
# 4. Scheduler logs with suspensions, both directions, on label-free terms.
def yterm(d):
    r = rng.random()
    if d <= 0 or r < 0.2:
        return rng.choice(["a", "b", "x", "S", "K", "I", "B", "C", "W", "yield", "yield"])
    return "%s (%s)" % (yterm(d - 1), yterm(d - 1))


SPEC = {"root": ["W", "K", "C", "S"], "gated": ["W", "K", "C"], "absorb": "s", "sc": "settled"}
sched_cases, resumed_runs = max(1, N // 10), 0
for n in range(sched_cases):
    ents = {"e%d" % j: (rng.choice(["", "yield ", "I (yield ", "yield (yield "]) + yterm(rng.choice([2, 3, 4]))) for j in range(rng.choice([1, 2, 3]))}
    for k in ents:  # close the parentheses opened by the prefixes
        ents[k] += ")" * (ents[k].count("(") - ents[k].count(")"))
    strat, budget, ticks = rng.choice(V.STRATEGIES), rng.choice([1, 2, 5]), rng.choice([3, 6])
    workers = rng.choice([1, 2, 4, 0])  # 0 is one worker per processor
    args = [GO, "sim", "--strategy", strat, "--budget", str(budget), "--ticks", str(ticks),
            "--workers", str(workers), "--out", os.path.join(tmp, "sg.json")] + [a for k, v in ents.items() for a in ("--entity", "%s=%s" % (k, v))]
    subprocess.run(args, capture_output=True, text=True)
    gdoc = json.load(open(os.path.join(tmp, "sg.json")))
    try:
        V.check_sched(V.strict_load(open(os.path.join(tmp, "sg.json")).read(), V.SCHED_SHAPE, "log-rejected"))
    except V.Reject as e:
        print("PYTHON REJECTS GO SCHED LOG", ents, strat, budget, e.msg)
        bad += 1
    pdoc = G.mk_sched(SPEC, strat, budget, ents, ticks)
    pp = os.path.join(tmp, "ps.json")
    json.dump(pdoc, open(pp, "w"), indent=2)
    c = subprocess.run([GO, "checklog", pp], capture_output=True, text=True)
    if c.returncode != 0:
        print("GO REJECTS PYTHON SCHED LOG", ents, strat, budget, c.stdout.strip())
        bad += 1
    if gdoc["events"] != json.loads(json.dumps(pdoc["events"])) or gdoc["final"] != pdoc["final"]:
        print("SCHED LOGS DIFFER", ents, strat, budget)
        bad += 1
    resumed_runs += any(e.get("resumed") for e in pdoc["events"])
print("scheduler logs:", sched_cases, "that resumed at least once:", resumed_runs)
print("cases:", N, "disagreements:", bad, "steps by rule:", dict(sorted(stats.items())))
sys.exit(1 if bad else 0)
