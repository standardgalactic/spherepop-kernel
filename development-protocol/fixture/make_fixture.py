import hashlib, json, os
def canon(o): return json.dumps(o, sort_keys=True, separators=(',',':'), ensure_ascii=True).encode()
def sha(b): return hashlib.sha256(b).hexdigest()
def chain(prev, ev): return sha(prev.encode()+b"\n"+canon(ev))
def art(s): return sha(s.encode())

V = art("verifier:grammar-conformance@1.4")
ENV = "env:toolchain-2026.11"
gamma = {"maintainer-A":["COLLAPSE","AMEND"],"proposer-M":["PROPOSE","VERIFY_RUN"]}
inv = ["grammar-preservation"]
budget = {"maintenance":100}
reg = {"gamma":sha(canon(gamma)),"inv":sha(canon(inv)),"budget":sha(canon(budget))}

e1 = {"kind":"GENESIS","parent":"root","payload":{"specification":"parser@1.0","invariants":inv,
      "capabilities":gamma,"budget":budget,
      "obligations":[{"id":"o1","artifact":"libA","upper":15},{"id":"o2","artifact":"libB","upper":15},{"id":"o3","artifact":"core","upper":40}],
      "profile":"sp-dev-0.1"},"evidence":[],"authorization":"trust-root"}
d1 = chain("root", e1)

t1 = art("tau1:remove-libA-libB-rewrite-tokenizer")
w1 = {"h":d1,"t":t1,"sigma":"parser@1.0","v":V,"eta":ENV,"F":["parser/tokenizer","parser/lexer-table","libA","libB"],
      "r":{"result":"fail","certificate":"input:\"/* x\" accepted by tau1, rejected by grammar"}}
w1d = sha(canon(w1))
k1 = sha(canon({"t":t1,"sigma":"parser@1.0","head":d1,"profile":"sp-dev-0.1","procedures":[V],"principal":"proposer-M",**reg}))
rec1 = {"disposition":"CONTRADICTED","tau":t1,"evidence":[w1d],"kappa":k1,"head":d1}

t2 = art("tau2:remove-libA-libB-preserve-grammar")
w2 = {"h":d1,"t":t2,"sigma":"parser@1.0","v":V,"eta":ENV,"F":["parser/tokenizer","parser/lexer-table","libA","libB"],
      "r":{"result":"pass","certificate":"corpus:parser-corpus@7 all accepted/rejected as specified"}}
w2d = sha(canon(w2))

tx = art("tx:lexer-table-v2")
wx = {"h":d1,"t":tx,"sigma":"parser@1.0","v":V,"eta":ENV,"F":["parser/lexer-table"],"r":{"result":"pass","certificate":"corpus:parser-corpus@7"}}
wxd = sha(canon(wx))
e2 = {"kind":"COLLAPSE","parent":d1,"payload":{"artifact":tx,"touches":["parser/lexer-table"],"maintenance_delta":{"added":[],"removed":[]}},
      "evidence":[wxd],"authorization":{"principal":"maintainer-A","policy":"merge-policy@2","expected_parent":d1}}
d2 = chain(d1, e2)

k2 = sha(canon({"t":t2,"sigma":"parser@1.0","head":d2,"profile":"sp-dev-0.1","procedures":[V],"principal":"proposer-M",**reg}))
rec2 = {"disposition":"STALE","tau":t2,"evidence":[w2d],"kappa":k2,"head":d2,"intersecting_event":d2}

t2p = art("tau2prime:tau2-rebased-on-lexer-table-v2")
w3 = {"h":d2,"t":t2p,"sigma":"parser@1.0","v":V,"eta":ENV,"F":["parser/tokenizer","parser/lexer-table","libA","libB"],
      "r":{"result":"pass","certificate":"corpus:parser-corpus@7"}}
w3d = sha(canon(w3))
e3 = {"kind":"COLLAPSE","parent":d2,"payload":{"artifact":t2p,"touches":["parser/tokenizer","libA","libB"],
      "maintenance_delta":{"added":[],"removed":["o1","o2"],"burden_before":70,"burden_after":40}},
      "evidence":[w3d],"authorization":{"principal":"maintainer-A","policy":"merge-policy@2","expected_parent":d2}}
d3 = chain(d2, e3)
rec3 = {"disposition":"ACCEPTABLE","tau":t2p,"evidence":[w3d],"expected_parent":d2,"actual_parent":d2,"committed_event":d3}

t3 = art("tau3:repair-unterminated-comment")
w4 = {"h":d3,"t":t3,"sigma":"parser@1.0","v":V,"eta":ENV,"F":["parser/tokenizer"],"r":{"result":"pass","certificate":"corpus:parser-corpus@8"}}
w4d = sha(canon(w4))
e4 = {"kind":"REPAIR","parent":d3,"payload":{"repairs":d3,"cause":"escaped-defect:unterminated-comment","artifact":t3},
      "evidence":[w4d],"authorization":{"principal":"maintainer-A","policy":"merge-policy@2","expected_parent":d3}}
d4 = chain(d3, e4)

fx = {"profile":"sp-dev-0.1","encoding":"utf-8 JSON, sorted keys, separators (',',':'), ASCII escapes",
      "chain":"d_i = SHA-256(d_{i-1} hex || 0x0A || canonical(e_i)); d_0 = 'root'",
      "events":[e1,e2,e3,e4],"digests":[d1,d2,d3,d4],
      "evidence":{"w1":w1,"w2":w2,"wx":wx,"w3":w3,"w4":w4},
      "evidence_digests":{"w1":w1d,"w2":w2d,"wx":wxd,"w3":w3d,"w4":w4d},
      "receipts":{"rho1":rec1,"rho2":rec2,"rho3":rec3},
      "note":"Artifact digests are SHA-256 of placeholder descriptions; they stand in for artifact content."}
json.dump(fx, open(os.path.join(os.path.dirname(os.path.abspath(__file__)),"parser_example_fixture.json"),"w"), indent=1, sort_keys=True)
# self-check replay
prev="root"
for e,d in zip(fx["events"],fx["digests"]):
    prev=chain(prev,e); assert prev==d
for n,v in [("d1",d1),("d2",d2),("d3",d3),("d4",d4),("w1",w1d),("w2",w2d),("w3",w3d),("k1",k1),("k2",k2),("t1",t1),("t2",t2),("t2p",t2p)]:
    print(n, v[:12])
