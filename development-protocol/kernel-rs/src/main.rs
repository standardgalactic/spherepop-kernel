//! Minimal reference kernel for the Spherepop Development Protocol, profile sp-dev-0.1.
//! Independent of the Python kernel: same fixtures, separate code and separate libraries.
//! serde_json maps are ordered by key, so compact serialization of a Value is the
//! canonical encoding for the ASCII-and-integer events used by the fixtures.

use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use std::collections::BTreeMap;
use std::fs;

fn canon(v: &Value) -> Vec<u8> {
    serde_json::to_vec(v).unwrap()
}
fn sha(b: &[u8]) -> String {
    format!("{:x}", Sha256::digest(b))
}
fn chain(prev: &str, ev: &Value) -> String {
    let mut b = prev.as_bytes().to_vec();
    b.push(b'\n');
    b.extend(canon(ev));
    sha(&b)
}
fn evidence_digest(w: &Value) -> String {
    sha(&canon(w))
}
fn strs(v: &Value) -> Vec<String> {
    v.as_array()
        .map(|a| a.iter().filter_map(|x| x.as_str().map(String::from)).collect())
        .unwrap_or_default()
}
fn s(v: &Value) -> String {
    v.as_str().unwrap_or("").to_string()
}

struct Kernel {
    events: Vec<Value>,
    digests: Vec<String>,
    spec: String,
    caps: Value,
    budget: i64,
    obligations: BTreeMap<String, i64>,
    ledger: Vec<Value>,
}

impl Kernel {
    fn new(genesis: &Value) -> Kernel {
        assert_eq!(genesis["kind"], "GENESIS");
        let g = &genesis["payload"];
        let mut obligations = BTreeMap::new();
        if let Some(a) = g["obligations"].as_array() {
            for o in a {
                obligations.insert(s(&o["id"]), o["upper"].as_i64().unwrap());
            }
        }
        Kernel {
            events: vec![genesis.clone()],
            digests: vec![chain("root", genesis)],
            spec: s(&g["specification"]),
            caps: g["capabilities"].clone(),
            budget: g["budget"]["maintenance"].as_i64().unwrap_or(100),
            obligations,
            ledger: vec![],
        }
    }
    fn head(&self) -> String {
        self.digests.last().unwrap().clone()
    }
    fn burden(&self) -> i64 {
        self.obligations.values().sum()
    }
    fn verify_chain(events: &[Value], digests: &[String]) -> bool {
        let mut prev = "root".to_string();
        for (e, d) in events.iter().zip(digests) {
            if s(&e["parent"]) != prev || &chain(&prev, e) != d {
                return false;
            }
            prev = d.clone();
        }
        events.len() == digests.len()
    }

    /// Evidence applicability: candidate binding, specification version, prefix and footprint.
    fn applicable(&self, w: &Value, cand: &str) -> Result<(), (String, Value)> {
        if s(&w["t"]) != cand {
            return Err(("UNESTABLISHED".into(), json!("evidence bound to a different candidate")));
        }
        if s(&w["sigma"]) != self.spec {
            return Err(("STALE".into(), json!("specification version differs")));
        }
        let h = s(&w["h"]);
        let i = match self.digests.iter().position(|d| *d == h) {
            Some(i) => i,
            None => return Err(("STALE".into(), json!("base is not a prefix of the head"))),
        };
        let footprint = strs(&w["F"]);
        for (j, e) in self.events.iter().enumerate().skip(i + 1) {
            let touched = strs(&e["payload"]["touches"]);
            let mut hit: Vec<String> = footprint.iter().filter(|f| touched.contains(f)).cloned().collect();
            if !hit.is_empty() {
                hit.sort();
                return Err((
                    "STALE".into(),
                    json!({"intersecting_event": self.digests[j], "elements": hit}),
                ));
            }
        }
        Ok(())
    }

    /// One atomic check-and-append against the head. Refusals extend the ledger only.
    fn commit(&mut self, event: &Value, evidence: &[Value]) -> Value {
        let mut findings: Vec<Value> = vec![];
        let cand = s(&event["payload"]["artifact"]);
        let principal = s(&event["authorization"]["principal"]);
        let may_pop = strs(&self.caps[&principal]).contains(&"COLLAPSE".to_string());
        if !may_pop {
            findings.push(json!({"type": "UNAUTHORIZED", "principal": principal}));
        }
        if s(&event["parent"]) != self.head() {
            findings.push(json!({"type": "STALE", "detail": "expected parent is not the head",
                                 "expected": event["parent"], "actual": self.head()}));
        }
        if event["kind"] == "REPAIR" && !self.digests.contains(&s(&event["payload"]["repairs"])) {
            findings.push(json!({"type": "UNESTABLISHED", "detail": "repair does not name an existing event"}));
        }
        let mut cited = strs(&event["evidence"]);
        let mut supplied: Vec<String> = evidence.iter().map(evidence_digest).collect();
        cited.sort();
        supplied.sort();
        if cited != supplied {
            findings.push(json!({"type": "UNESTABLISHED", "detail": "cited evidence differs from supplied evidence"}));
        }
        if evidence.is_empty() {
            findings.push(json!({"type": "UNESTABLISHED", "detail": "no evidence supplied"}));
        }
        for w in evidence {
            match self.applicable(w, &cand) {
                Err((kind, detail)) => findings.push(json!({"type": kind, "detail": detail})),
                Ok(()) => {
                    if w["r"]["result"] != "pass" {
                        findings.push(json!({"type": "CONTRADICTED", "certificate": w["r"]["certificate"]}));
                    }
                }
            }
        }
        // two-regime budget rule over declared upper bounds
        let delta = &event["payload"]["maintenance_delta"];
        let mut new = self.obligations.clone();
        for o in strs(&delta["removed"]) {
            new.remove(&o);
        }
        if let Some(a) = delta["added"].as_array() {
            for o in a {
                new.insert(s(&o["id"]), o["upper"].as_i64().unwrap());
            }
        }
        let before = self.burden();
        let after: i64 = new.values().sum();
        let ok_budget = if before <= self.budget { after <= self.budget } else { after < before };
        if !ok_budget {
            findings.push(json!({"type": "CONTRADICTED", "detail": "budget rule", "before": before, "after": after}));
        }
        if !findings.is_empty() {
            let primary = findings[0]["type"].clone();
            let receipt = json!({"operation": "REFUSE", "tau": cand, "findings": findings, "primary": primary,
                                 "head_before": self.head(), "head_after": self.head()});
            self.ledger.push(receipt.clone());
            return receipt;
        }
        let d = chain(self.digests.last().unwrap(), event);
        self.events.push(event.clone());
        self.digests.push(d);
        self.obligations = new;
        let receipt = json!({"operation": "COLLAPSE", "tau": cand, "findings": [{"type": "ACCEPTABLE"}],
                             "expected_parent": event["parent"], "actual_parent": event["parent"],
                             "committed": self.head()});
        self.ledger.push(receipt.clone());
        receipt
    }
}

// ---- nested composition: reference semantics for the exports example ----
type State = BTreeMap<String, Vec<String>>;
fn state_of(v: &Value) -> State {
    v.as_object().unwrap().iter().map(|(u, n)| (u.clone(), strs(n))).collect()
}
fn apply_export(st: &State, tau: &Value) -> State {
    let mut st = st.clone();
    let e = st.entry(s(&tau["unit"])).or_default();
    e.push(s(&tau["add_export"]));
    e.sort();
    st
}
fn duplicates(st: &State) -> BTreeMap<String, Vec<String>> {
    let mut seen: BTreeMap<String, Vec<String>> = BTreeMap::new();
    for (u, names) in st {
        for n in names {
            seen.entry(n.clone()).or_default().push(u.clone());
        }
    }
    seen.retain(|_, us| us.len() > 1);
    seen
}

fn run_script(path: &str) {
    let sc: Value = serde_json::from_str(&fs::read_to_string(path).unwrap()).unwrap();
    let mut k = Kernel::new(&sc["genesis"]);
    for st in sc["steps"].as_array().unwrap() {
        let evidence: Vec<Value> = st["evidence"].as_array().unwrap().clone();
        let r = k.commit(&st["event"], &evidence);
        let types: Vec<Value> = r["findings"].as_array().unwrap().iter().map(|x| x["type"].clone()).collect();
        let primary = if r["operation"] == "COLLAPSE" { json!("ACCEPTABLE") } else { r["primary"].clone() };
        let out = json!({"op": r["operation"], "primary": primary, "types": types, "head": k.head(),
                         "burden": k.burden(), "length": k.events.len()});
        println!("{}", serde_json::to_string(&out).unwrap());
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args[1] == "--script" {
        run_script(&args[2]);
        return;
    }
    let f: Value = serde_json::from_str(&fs::read_to_string(&args[1]).unwrap()).unwrap();
    let g: Value = serde_json::from_str(&fs::read_to_string(&args[2]).unwrap()).unwrap();
    let mut results: Vec<(&str, bool)> = vec![];
    let mut check = |name: &'static str, c: bool| results.push((name, c));

    let d: Vec<String> = f["digests"].as_array().unwrap().iter().map(|x| s(x)).collect();
    let ev = &f["evidence"];
    let evd = &f["evidence_digests"];
    let mut k = Kernel::new(&f["events"][0]);
    check("genesis digest d1", k.head() == d[0]);

    let mut t1 = f["events"][2].clone();
    t1["payload"]["artifact"] = ev["w1"]["t"].clone();
    t1["evidence"] = json!([evd["w1"]]);
    t1["parent"] = json!(k.head());
    let r1 = k.commit(&t1, &[ev["w1"].clone()]);
    check("tau1 CONTRADICTED", r1["primary"] == "CONTRADICTED" && k.head() == d[0]);
    check("refusal leaves H unchanged", k.events.len() == 1);

    let r = k.commit(&f["events"][1], &[ev["wx"].clone()]);
    check("e2 committed, d2 reproduced", r["operation"] == "COLLAPSE" && k.head() == d[1]);

    let mut t2 = f["events"][2].clone();
    t2["parent"] = json!(k.head());
    t2["payload"]["artifact"] = ev["w2"]["t"].clone();
    t2["evidence"] = json!([evd["w2"]]);
    let r2 = k.commit(&t2, &[ev["w2"].clone()]);
    let stale = r2["findings"].as_array().unwrap().iter().any(|x| {
        x["type"] == "STALE" && x["detail"]["intersecting_event"] == json!(d[1])
    });
    check("tau2 STALE with intersecting event", stale);
    check("stale refusal leaves head d2", k.head() == d[1]);

    let mut forged = f["events"][2].clone();
    forged["payload"]["artifact"] = json!("0".repeat(64));
    let r3 = k.commit(&forged, &[ev["w3"].clone()]);
    check("modified candidate: evidence not applicable",
          r3["findings"].as_array().unwrap().iter().any(|x| x["type"] == "UNESTABLISHED"));

    let mut unauth = f["events"][2].clone();
    unauth["authorization"]["principal"] = json!("proposer-M");
    let r4 = k.commit(&unauth, &[ev["w3"].clone()]);
    check("unauthorized principal refused",
          r4["findings"].as_array().unwrap().iter().any(|x| x["type"] == "UNAUTHORIZED"));

    let r5 = k.commit(&f["events"][2], &[ev["w3"].clone()]);
    check("e3 committed, d3 reproduced", r5["operation"] == "COLLAPSE" && k.head() == d[2]);
    check("burden 70 to 40", k.burden() == 40);
    let r6 = k.commit(&f["events"][3], &[ev["w4"].clone()]);
    check("repair e4 committed, d4 reproduced", r6["operation"] == "COLLAPSE" && k.head() == d[3]);
    check("history chain verifies", Kernel::verify_chain(&k.events, &k.digests));
    check("earlier digests unchanged by repair", k.digests[..3] == d[..3]);

    let mut bad = k.events.clone();
    bad[1]["payload"]["touches"] = json!([]);
    check("tampered history detected", !Kernel::verify_chain(&bad, &k.digests));

    let r7 = k.commit(&f["events"][2], &[ev["w3"].clone()]);
    check("stale parent refused (atomic head check)", r7["operation"] == "REFUSE");

    let mut k2 = Kernel::new(&f["events"][0]);
    k2.obligations = [("a".to_string(), 80), ("b".to_string(), 60)].into_iter().collect();
    let over_up = json!({"kind": "COLLAPSE", "parent": k2.head(),
        "payload": {"artifact": "x", "maintenance_delta": {"added": [{"id": "n", "upper": 5}], "removed": []}},
        "evidence": [], "authorization": {"principal": "maintainer-A"}});
    check("obligation-adding refused while over budget", k2.commit(&over_up, &[])["operation"] == "REFUSE");
    let w = json!({"h": k2.head(), "t": "x", "sigma": k2.spec, "v": "v", "eta": "e", "F": [], "r": {"result": "pass"}});
    let e = json!({"kind": "COLLAPSE", "parent": k2.head(),
        "payload": {"artifact": "x", "maintenance_delta": {"added": [], "removed": ["b"]}},
        "evidence": [evidence_digest(&w)], "authorization": {"principal": "maintainer-A"}});
    let rr = k2.commit(&e, &[w]);
    check("strictly reducing partial repair allowed while over budget", rr["operation"] == "COLLAPSE" && k2.burden() == 80);

    // nested sphere fixture
    let kn = Kernel::new(&g["genesis"]);
    check("nested genesis head reproduced", s(&json!(kn.head())) == s(&g["head"]));
    let base = state_of(&g["genesis"]["payload"]["initial_state"]);
    let taus = [g["subordinate"]["s1"]["tau"].clone(), g["subordinate"]["s2"]["tau"].clone()];
    let local: Vec<bool> = taus.iter().map(|t| duplicates(&apply_export(&base, t)).is_empty()).collect();
    check("both local certifications pass", local == vec![true, true]);
    let composed = taus.iter().fold(base.clone(), |st, t| apply_export(&st, t));
    let dup = duplicates(&composed);
    let (name, units) = dup.iter().next().map(|(n, u)| (n.clone(), u.clone())).unwrap_or_default();
    check("composition refused with boundary finding", !dup.is_empty() && g["expected"]["violated_obligation"] == "unique-exports");
    let expect = &g["parent"]["receipt"]["findings"][0]["certificate"];
    check("certificate matches fixture", *expect == json!({"name": name, "units": units}));
    check("head unchanged", kn.head() == s(&g["head"]));

    let mut ok_all = true;
    for (n, ok) in &results {
        println!("{} {}", if *ok { "PASS" } else { "FAIL" }, n);
        ok_all &= *ok;
    }
    std::process::exit(if ok_all { 0 } else { 1 });
}
