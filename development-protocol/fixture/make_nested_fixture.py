import hashlib, json, os
def canon(o): return json.dumps(o, sort_keys=True, separators=(',',':'), ensure_ascii=True).encode()
def sha(b): return hashlib.sha256(b).hexdigest()
def chain(prev, ev): return sha(prev.encode()+b"\n"+canon(ev))

# Reference semantics: state maps unit -> sorted list of exported names.
def apply(state, tau):
    st = {u: list(v) for u, v in state.items()}
    st.setdefault(tau["unit"], []).append(tau["add_export"])
    return {u: sorted(v) for u, v in st.items()}
def unique_exports(state):
    names = [n for v in state.values() for n in v]
    return len(names) == len(set(names))
def certify_local(base, tau):
    # local procedure: sees only the sphere's own view of the base state
    return unique_exports(apply(base, tau))

genesis = {"kind":"GENESIS","parent":"root","payload":{"specification":"exports@1.0",
  "invariants":["unique-exports"],"boundary_obligations":["unique-exports"],
  "initial_state":{"A":["lex"],"B":["emit"]},"capabilities":{"maintainer-A":["COLLAPSE"],"proposer-M":["PROPOSE","VERIFY_RUN"]},
  "profile":"sp-dev-0.1"},"evidence":[],"authorization":"trust-root"}
d1 = chain("root", genesis)
base = genesis["payload"]["initial_state"]

tau1 = {"unit":"A","add_export":"parse"}
tau2 = {"unit":"B","add_export":"parse"}
def art(t): return sha(canon(t))
ev = {}
for name,t in (("s1",tau1),("s2",tau2)):
    ok = certify_local(base, t)
    ev[name] = {"h":d1,"t":art(t),"sigma":"exports@1.0","procedure":"local-unique-exports@1","F":[t["unit"]],
                "r":{"result":"pass" if ok else "fail"}}
    assert ok
composed = apply(apply(base,tau1),tau2)
parent_ok = unique_exports(composed)
assert not parent_ok
tc = {"compose":[tau1,tau2]}
parent_cert = {"h":d1,"t":art(tc),"sigma":"exports@1.0","procedure":"boundary-unique-exports@1","F":["A","B"],
               "r":{"result":"fail","violated_obligation":"unique-exports","certificate":{"name":"parse","units":["A","B"]}}}
receipt = {"operation":"REFUSE","tau":art(tc),"findings":[{"type":"CONTRADICTED","obligation":"unique-exports","certificate":parent_cert["r"]["certificate"]}],
           "primary":"CONTRADICTED","local_certificates_preserved":[sha(canon(ev["s1"])),sha(canon(ev["s2"]))],
           "head_before":d1,"head_after":d1}
fx = {"profile":"sp-dev-0.1","purpose":"Noncompositionality of local certification: two subordinate spheres pass locally, composition violates a parent boundary obligation.",
 "genesis":genesis,"head":d1,"subordinate":{"s1":{"tau":tau1,"evidence":ev["s1"],"disposition":"ACCEPTABLE_LOCALLY"},
 "s2":{"tau":tau2,"evidence":ev["s2"],"disposition":"ACCEPTABLE_LOCALLY"}},
 "parent":{"composed":tc,"boundary_evidence":parent_cert,"receipt":receipt},
 "expected":{"commit":False,"head_unchanged":True,"disposition":"CONTRADICTED","violated_obligation":"unique-exports"}}
json.dump(fx, open(os.path.join(os.path.dirname(os.path.abspath(__file__)),"nested_sphere_fixture.json"),"w"), indent=1, sort_keys=True)
print("head", d1[:12], "local ok:", True, True, "composed ok:", parent_ok)
