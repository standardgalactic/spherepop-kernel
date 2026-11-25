"""Differential harness: random scenarios run through the Python and Rust kernels; transcripts must match."""
import importlib.util, json, os, random, subprocess, sys, hashlib

HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location("spk", os.path.join(HERE, "spherepop_kernel.py"))
spk = importlib.util.module_from_spec(spec); spec.loader.exec_module(spk)
RUST = os.path.join(HERE, "..", "kernel-rs", "target", "release", "spherepop-kernel")
FIX = os.path.join(HERE, "..", "fixture", "parser_example_fixture.json")
UNITS = ["u1", "u2", "u3", "u4", "u5"]

def hx(n): return hashlib.sha256(str(n).encode()).hexdigest()

def scenario(rng, genesis, n_steps):
    k = spk.Kernel(genesis); steps = []
    for i in range(n_steps):
        r = rng.random
        principal = rng.choices(["maintainer-A", "proposer-M", "ghost"], [8, 1, 1])[0]
        parent = k.head if r() < 0.85 else rng.choice(k.digests)
        art = hx(("art", rng.random()))
        ev_list, cited = [], []
        for _ in range(rng.choice([0, 1, 1, 1, 2])):
            h = k.head if r() < 0.7 else (rng.choice(k.digests) if r() < 0.8 else hx("unknown"))
            w = {"h": h, "t": art if r() < 0.9 else hx("other"), "sigma": k.spec if r() < 0.95 else "other@1",
                 "v": "v", "eta": "e", "F": sorted(rng.sample(UNITS, rng.randint(0, 3))),
                 "r": {"result": "pass"} if r() < 0.85 else {"result": "fail", "certificate": "cx"}}
            ev_list.append(w); cited.append(spk.evidence_digest(w))
        if cited and r() < 0.1: cited[0] = hx("wrong")
        delta = {"added": [], "removed": []}
        if k.obligations and r() < 0.3:
            delta["removed"] = rng.sample(sorted(k.obligations), rng.randint(1, min(2, len(k.obligations))))
        if r() < 0.35:
            delta["added"] = [{"id": "n%d" % i, "upper": rng.randint(1, 30)}]
        if k.obligations and r() < 0.15:      # equal-burden swap: boundary case of the budget rule
            oid = rng.choice(sorted(k.obligations))
            delta = {"removed": [oid], "added": [{"id": "sw%d" % i, "upper": k.obligations[oid]}]}
        ev = {"kind": rng.choice(["COLLAPSE", "REPAIR"]), "parent": parent,
              "payload": {"artifact": art, "touches": sorted(rng.sample(UNITS, rng.randint(0, 3))),
                          "maintenance_delta": delta},
              "evidence": cited, "authorization": {"principal": principal}}
        if ev["kind"] == "REPAIR" and r() < 0.8:
            ev["payload"]["repairs"] = rng.choice(k.digests) if r() < 0.9 else hx("nowhere")
        steps.append({"event": ev, "evidence": ev_list})
        k.commit(ev, ev_list)
    return steps

def transcript_py(sc, path):
    json.dump(sc, open(path, "w"))
    k = spk.Kernel(sc["genesis"]); out = []
    for st in sc["steps"]:
        out.append(json.dumps(spk.summarize(k, k.commit(st["event"], st["evidence"])), sort_keys=True, separators=(',', ':')))
    return out

def main(n_scen, n_steps, seed):
    genesis0 = json.load(open(FIX))["events"][0]
    rng = random.Random(seed); pops = refusals = 0; kinds = {}
    for s in range(n_scen):
        genesis = json.loads(json.dumps(genesis0))
        genesis["payload"]["obligations"] = [{"id": "g%d" % j, "upper": rng.randint(5, 50)} for j in range(rng.randint(1, 5))]
        sc = {"genesis": genesis, "steps": scenario(rng, genesis, n_steps)}
        path = "/tmp/diff_scen.json"
        py = transcript_py(sc, path)
        rs = subprocess.run([RUST, "--script", path], capture_output=True, text=True, check=True).stdout.splitlines()
        if py != rs:
            i = next(j for j, (a, b) in enumerate(zip(py, rs)) if a != b) if len(py) == len(rs) else min(len(py), len(rs))
            print("DIVERGENCE in scenario", s, "step", i); print(" py:", py[i] if i < len(py) else None); print(" rs:", rs[i] if i < len(rs) else None)
            json.dump(sc, open("/tmp/diverging_scenario.json", "w")); return 1
        for line in py:
            o = json.loads(line)
            if o["op"] == "COLLAPSE": pops += 1
            else:
                refusals += 1
                for t in o["types"]: kinds[t] = kinds.get(t, 0) + 1
    print("scenarios", n_scen, "steps", n_scen * n_steps, "commits", pops, "refusals", refusals)
    print("finding types seen:", dict(sorted(kinds.items())))
    print("no divergence")
    return 0

if __name__ == "__main__":
    sys.exit(main(int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])))
