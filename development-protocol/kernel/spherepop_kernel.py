"""Minimal reference kernel for the Spherepop Development Protocol, profile sp-dev-0.1.

Standard library only. It reads the fixtures but shares no code with the scripts
that generated them, so reproducing their digests is an independent check.

Structures: H (authoritative history), L (ledger of receipts). Journals are the
caller's concern in this minimal kernel; only commitment and refusal are modelled.
"""
import hashlib, json, sys

def canon(o):
    return json.dumps(o, sort_keys=True, separators=(',', ':'), ensure_ascii=True).encode()

def sha(b):
    return hashlib.sha256(b).hexdigest()

def chain(prev, ev):
    return sha(prev.encode() + b"\n" + canon(ev))

def evidence_digest(w):
    return sha(canon(w))

class Kernel:
    def __init__(self, genesis):
        assert genesis["kind"] == "GENESIS"
        self.events = [genesis]
        self.digests = [chain("root", genesis)]
        g = genesis["payload"]
        self.spec = g["specification"]
        self.caps = g["capabilities"]
        self.budget = g.get("budget", {"maintenance": 100}).get("maintenance", 100)
        self.obligations = {o["id"]: o["upper"] for o in g.get("obligations", [])}
        self.ledger = []          # L: receipts, never part of H
        self.repairs = []

    # ---- queries ----
    @property
    def head(self):
        return self.digests[-1]

    def burden(self):
        return sum(self.obligations.values())

    def verify_chain(self, events=None, digests=None):
        events = events or self.events
        digests = digests or self.digests
        prev = "root"
        for e, d in zip(events, digests):
            if e["parent"] != prev or chain(prev, e) != d:
                return False
            prev = d
        return True

    # ---- evidence applicability (Section on evidence) ----
    def applicable(self, w, cand_digest):
        if w["t"] != cand_digest:
            return False, "UNESTABLISHED", "evidence bound to a different candidate"
        if w["sigma"] != self.spec:
            return False, "STALE", "specification version differs"
        if w["h"] not in self.digests:
            return False, "STALE", "base is not a prefix of the head"
        i = self.digests.index(w["h"])
        footprint = set(w["F"])
        for e in self.events[i + 1:]:
            hit = footprint & set(e["payload"].get("touches", []))
            if hit:
                return False, "STALE", {"intersecting_event": chain_of(self, e), "elements": sorted(hit)}
        return True, None, None

    # ---- commitment: one atomic check-and-append against the head ----
    def commit(self, event, evidence):
        findings = []
        cand = event["payload"]["artifact"]
        # authorization is judged against the registries of H (pre-transition)
        auth = event.get("authorization", {})
        if "COLLAPSE" not in self.caps.get(auth.get("principal"), []):
            findings.append({"type": "UNAUTHORIZED", "principal": auth.get("principal")})
        if event["parent"] != self.head:
            findings.append({"type": "STALE", "detail": "expected parent is not the head",
                             "expected": event["parent"], "actual": self.head})
        if event["kind"] == "REPAIR" and event["payload"].get("repairs") not in self.digests:
            findings.append({"type": "UNESTABLISHED", "detail": "repair does not name an existing event"})
        # evidence must be exactly the evidence the event cites
        if sorted(event["evidence"]) != sorted(evidence_digest(w) for w in evidence):
            findings.append({"type": "UNESTABLISHED", "detail": "cited evidence differs from supplied evidence"})
        if not evidence:
            findings.append({"type": "UNESTABLISHED", "detail": "no evidence supplied"})
        for w in evidence:
            ok, kind, detail = self.applicable(w, cand)
            if not ok:
                findings.append({"type": kind, "detail": detail})
            elif w["r"]["result"] != "pass":
                findings.append({"type": "CONTRADICTED", "certificate": w["r"].get("certificate")})
        # budget: two-regime rule over declared upper bounds
        delta = event["payload"].get("maintenance_delta", {})
        new = dict(self.obligations)
        for o in delta.get("removed", []):
            new.pop(o, None)
        for o in delta.get("added", []):
            new[o["id"]] = o["upper"]
        before, after = self.burden(), sum(new.values())
        ok_budget = (after <= self.budget) if before <= self.budget else (after < before)
        if not ok_budget:
            findings.append({"type": "CONTRADICTED", "detail": "budget rule", "before": before, "after": after})
        if findings:
            primary = findings[0]["type"]
            receipt = {"operation": "REFUSE", "tau": cand, "findings": findings, "primary": primary,
                       "head_before": self.head, "head_after": self.head}
            self.ledger.append(receipt)
            return receipt
        self.events.append(event)
        self.digests.append(chain(self.digests[-1], event))
        self.obligations = new
        if event["kind"] == "REPAIR":
            self.repairs.append(event["payload"]["repairs"])
        receipt = {"operation": "COLLAPSE", "tau": cand, "findings": [{"type": "ACCEPTABLE"}],
                   "expected_parent": event["parent"], "actual_parent": event["parent"],
                   "committed": self.head}
        self.ledger.append(receipt)
        return receipt

def chain_of(k, e):
    return k.digests[k.events.index(e)]

# ---- nested composition (reference semantics for the exports example) ----
def apply_export(state, tau):
    st = {u: list(v) for u, v in state.items()}
    st.setdefault(tau["unit"], []).append(tau["add_export"])
    return {u: sorted(v) for u, v in st.items()}

def duplicates(state):
    seen, dup = {}, {}
    for u, names in state.items():
        for n in names:
            seen.setdefault(n, []).append(u)
    return {n: us for n, us in seen.items() if len(us) > 1}

def nested_commit(kernel, base_state, taus):
    local = []
    for t in taus:                       # local certification sees only the sphere's own view
        local.append(not duplicates(apply_export(base_state, t)))
    state = base_state
    for t in taus:
        state = apply_export(state, t)
    dup = duplicates(state)
    findings = []
    if dup:
        n, us = sorted(dup.items())[0]
        findings.append({"type": "CONTRADICTED", "obligation": "unique-exports",
                         "certificate": {"name": n, "units": sorted(us)}})
    return {"local_ok": local, "findings": findings, "head_before": kernel.head, "head_after": kernel.head}

# ---- conformance run against the fixtures ----
def run(fx1_path, fx2_path):
    results = []
    def check(name, cond):
        results.append((name, bool(cond)))

    f = json.load(open(fx1_path))
    k = Kernel(f["events"][0])
    check("genesis digest d1", k.head == f["digests"][0])
    ev = f["evidence"]
    # refused proposal: tau1 with failing evidence
    t1 = dict(f["events"][2]); t1 = {**t1, "payload": {**t1["payload"], "artifact": ev["w1"]["t"]},
                                      "evidence": [f["evidence_digests"]["w1"]], "parent": k.head}
    r1 = k.commit(t1, [ev["w1"]])
    check("tau1 CONTRADICTED", r1["primary"] == "CONTRADICTED" and k.head == f["digests"][0])
    check("refusal leaves H unchanged", len(k.events) == 1)
    # unrelated commit e2
    r = k.commit(f["events"][1], [ev["wx"]])
    check("e2 committed, d2 reproduced", r["operation"] == "COLLAPSE" and k.head == f["digests"][1])
    # stale: tau2 with w2 (base d1), parent d2
    t2 = {**f["events"][2], "parent": k.head, "payload": {**f["events"][2]["payload"], "artifact": ev["w2"]["t"]},
          "evidence": [f["evidence_digests"]["w2"]]}
    r2 = k.commit(t2, [ev["w2"]])
    check("tau2 STALE with intersecting event", any(x["type"] == "STALE" and isinstance(x["detail"], dict)
          and x["detail"]["intersecting_event"] == f["digests"][1] for x in r2["findings"]))
    check("stale refusal leaves head d2", k.head == f["digests"][1])
    # evidence for a different candidate (patch changed after testing)
    forged = {**f["events"][2], "payload": {**f["events"][2]["payload"], "artifact": "0" * 64}}
    r3 = k.commit(forged, [ev["w3"]])
    check("modified candidate: evidence not applicable", any(x["type"] == "UNESTABLISHED" for x in r3["findings"]))
    # unauthorized principal
    unauth = {**f["events"][2], "authorization": {**f["events"][2]["authorization"], "principal": "proposer-M"}}
    r4 = k.commit(unauth, [ev["w3"]])
    check("unauthorized principal refused", any(x["type"] == "UNAUTHORIZED" for x in r4["findings"]))
    # recomputed commit e3 and repair e4
    r5 = k.commit(f["events"][2], [ev["w3"]])
    check("e3 committed, d3 reproduced", r5["operation"] == "COLLAPSE" and k.head == f["digests"][2])
    check("burden 70 to 40", k.burden() == 40)
    r6 = k.commit(f["events"][3], [ev["w4"]])
    check("repair e4 committed, d4 reproduced", r6["operation"] == "COLLAPSE" and k.head == f["digests"][3])
    check("history chain verifies", k.verify_chain())
    check("earlier digests unchanged by repair", k.digests[:3] == f["digests"][:3])
    # tamper detection
    bad = [dict(e) for e in k.events]; bad[1] = {**bad[1], "payload": {**bad[1]["payload"], "touches": []}}
    check("tampered history detected", not k.verify_chain(bad, k.digests))
    # CAS: replay of an already-committed event fails against the new head
    r7 = k.commit(f["events"][2], [ev["w3"]])
    check("stale parent refused (atomic head check)", r7["operation"] == "REFUSE")
    # budget two-regime rule
    k2 = Kernel(f["events"][0]); k2.obligations = {"a": 80, "b": 60}          # over budget, 140 vs 100
    over_up = {"kind": "COLLAPSE", "parent": k2.head, "payload": {"artifact": "x", "maintenance_delta": {"added": [{"id": "n", "upper": 5}], "removed": []}},
               "evidence": [], "authorization": {"principal": "maintainer-A"}}
    check("obligation-adding refused while over budget", k2.commit(over_up, [])["operation"] == "REFUSE")
    def mk(delta):
        w = {"h": k2.head, "t": "x", "sigma": k2.spec, "v": "v", "eta": "e", "F": [], "r": {"result": "pass"}}
        e = {"kind": "COLLAPSE", "parent": k2.head, "payload": {"artifact": "x", "maintenance_delta": delta},
             "evidence": [evidence_digest(w)], "authorization": {"principal": "maintainer-A"}}
        return e, [w]
    e, w = mk({"added": [], "removed": ["b"]})
    check("strictly reducing partial repair allowed while over budget", k2.commit(e, w)["operation"] == "COLLAPSE" and k2.burden() == 80)

    # nested sphere fixture
    g = json.load(open(fx2_path))
    kn = Kernel(g["genesis"])
    check("nested genesis head reproduced", kn.head == g["head"])
    out = nested_commit(kn, g["genesis"]["payload"]["initial_state"], [g["subordinate"]["s1"]["tau"], g["subordinate"]["s2"]["tau"]])
    check("both local certifications pass", out["local_ok"] == [True, True])
    check("composition refused with boundary finding", out["findings"] and out["findings"][0]["type"] == "CONTRADICTED"
          and out["findings"][0]["obligation"] == g["expected"]["violated_obligation"])
    check("certificate matches fixture", out["findings"][0]["certificate"] == g["parent"]["receipt"]["findings"][0]["certificate"])
    check("head unchanged", out["head_before"] == out["head_after"] == g["head"])
    return results

def summarize(k, receipt):
    return {"op": receipt["operation"], "primary": receipt.get("primary", "ACCEPTABLE"),
            "types": [x["type"] for x in receipt["findings"]], "head": k.head,
            "burden": k.burden(), "length": len(k.events)}

def run_script(path):
    sc = json.load(open(path))
    k = Kernel(sc["genesis"])
    for st in sc["steps"]:
        print(json.dumps(summarize(k, k.commit(st["event"], st["evidence"])), sort_keys=True, separators=(',', ':')))

if __name__ == "__main__" and sys.argv[1] == "--script":
    run_script(sys.argv[2]); sys.exit(0)

if __name__ == "__main__":
    res = run(sys.argv[1], sys.argv[2])
    for n, ok in res:
        print(("PASS " if ok else "FAIL ") + n)
    sys.exit(0 if all(ok for _, ok in res) else 1)
