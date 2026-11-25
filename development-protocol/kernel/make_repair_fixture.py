import importlib.util, json, os, hashlib
HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location("spk", os.path.join(HERE, "spherepop_kernel.py"))
spk = importlib.util.module_from_spec(spec); spec.loader.exec_module(spk)
genesis = json.load(open(os.path.join(HERE, "..", "fixture", "parser_example_fixture.json")))["events"][0]
k = spk.Kernel(genesis); steps = []; expected = []
def hx(s): return hashlib.sha256(s.encode()).hexdigest()
def step(kind, art, repairs=None):
    w = {"h": k.head, "t": hx(art), "sigma": k.spec, "v": "v", "eta": "e", "F": ["parser/tokenizer"], "r": {"result": "pass"}}
    p = {"artifact": hx(art), "touches": ["parser/tokenizer"], "maintenance_delta": {"added": [], "removed": []}}
    if repairs: p["repairs"] = repairs
    e = {"kind": kind, "parent": k.head, "payload": p, "evidence": [spk.evidence_digest(w)], "authorization": {"principal": "maintainer-A"}}
    steps.append({"event": e, "evidence": [w]})
    expected.append(json.dumps(spk.summarize(k, k.commit(e, [w])), sort_keys=True, separators=(',', ':')))
step("REPAIR", "repair-nowhere", hx("no such event"))   # must be refused: target does not exist
step("COLLAPSE", "ordinary-change")                           # creates a target
step("REPAIR", "repair-of-change", k.head)              # accepted: names an existing event
json.dump({"purpose": "A repair event must name an existing event of H; otherwise it is refused as unestablished and H is unchanged.",
           "genesis": genesis, "steps": steps, "expected_transcript": expected}, open(os.path.join(HERE, "..", "fixture", "repair_target_fixture.json"), "w"), indent=1, sort_keys=True)
print("\n".join(expected))
