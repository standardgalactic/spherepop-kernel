import os, unittest
from spop.index import *
from spop.racket import Racket, LispError
from spop.shell import *

RKT = os.path.join(os.path.dirname(__file__), "..", "rkt")


def src(n):
    with open(os.path.join(RKT, n + ".rkt")) as f: return f.read()


def diamond():
    ix = Index()
    for v in ("1.0.0", "1.5.0", "2.0.0"): ix.publish("C", v)
    ix.publish("A", "1.0.0", {"C": "^1.0"}); ix.publish("A", "2.0.0", {"C": "^2.0"})
    ix.publish("B", "1.0.0", {"C": "^1.0"})
    return ix


class IndexTests(unittest.TestCase):
    def test_specifiers(self):
        self.assertTrue(satisfies("1.4.2", "^1.2"));  self.assertFalse(satisfies("2.0.0", "^1.2"))
        self.assertTrue(satisfies("0.2.9", "^0.2.3")); self.assertFalse(satisfies("0.3.0", "^0.2.3"))
        self.assertTrue(satisfies("1.2.9", "~1.2.3")); self.assertFalse(satisfies("1.3.0", "~1.2.3"))
        self.assertTrue(satisfies("1.5", ">=1.2,<2.0,!=1.4.0"))

    def test_flat_backtracks(self):
        ix = diamond()
        got = ix.install({"A": "*", "B": "*"})
        self.assertEqual(got, {"A": "1.0.0", "B": "1.0.0", "C": "1.5.0"})
        self.assertIn("backtrack", ix.w.reasons.values())
        self.assertTrue(ix.w.verify())

    def test_flat_conflict_is_refusal_nested_succeeds(self):
        ix = diamond()
        with self.assertRaises(ResolutionError): ix.install({"A": "==2.0.0", "B": "*"})
        self.assertIn("unsatisfiable", ix.w.reasons.values())
        self.assertEqual(ix.installed(), {})
        out = ix.solve_nested({"A": "==2.0.0", "B": "*"})
        self.assertEqual(ix.node_lookup(("A@2.0.0",), "C"), "2.0.0")
        self.assertEqual(ix.node_lookup(("B@1.0.0",), "C"), "1.5.0")
        self.assertIsNone(ix.node_lookup((), "C"))
        self.assertEqual(ix.node_lookup(("B@1.0.0", "X@1"), "C"), "1.5.0")      # walks outward

    def test_uninstall_and_upgrade(self):
        ix = diamond(); ix.install({"A": "*"})
        with self.assertRaises(ResolutionError): ix.uninstall("C")
        self.assertEqual(ix.why("C"), ["A"])
        ix.uninstall("A"); ix.uninstall("C")
        self.assertEqual(ix.installed(), {})
        ix2 = diamond(); ix2.install({"C": "==1.0.0"}); ix2.install({"C": "^2.0"})
        self.assertEqual(ix2.installed(), {"C": "2.0.0"})
        self.assertIn("upgraded", ix2.w.reasons.values())

    def test_install_respects_pins(self):
        ix = diamond(); ix.install({"C": "==1.0.0"})
        ix.install({"B": "*"})                        # C stays at 1.0.0 although 1.5.0 exists
        self.assertEqual(ix.installed()["C"], "1.0.0")

    def test_lock_is_order_independent(self):
        a, b = diamond(), diamond()
        for ix in (a, b): ix.publish("D", "1.0.0", {"C": "*"})
        a.install({"A": "*"}); a.install({"D": "*"}); b.install({"D": "*", "A": "*"})
        self.assertEqual(a.lock(), b.lock())
        c = diamond()
        c.install({"A": "*"})
        with self.assertRaises(ResolutionError): c.install({"B": "*"})      # pinned C 2.0.0 conflicts with B

    def test_search_path_shadowing(self):
        w = World(); sp = SearchPath(w, ["user", "install", "main"])
        sp.contents = {"user": {"fsm"}, "install": {"fsm", "units"}, "main": {"base"}}
        self.assertEqual(sp.find("fsm"), "user"); self.assertEqual(sp.find("units"), "install")
        self.assertIsNone(sp.find("nothing"))
        sp.set(["install", "user", "main"]); self.assertEqual(sp.find("fsm"), "install")
        self.assertIn("reassigned", w.reasons.values()); self.assertTrue(w.verify())

    def test_shell_hook_uses_index(self):
        ix = Index(); ix.publish("htop", "3.0", provides=("/usr/bin/htop",))
        m = ubuntu_machine(); sh = Shell(m, "bash", hook=ix.hook())
        self.assertEqual(sh.run("htop"), 127); self.assertIn("sudo apt install htop", sh.output())
        self.assertIn("command not found", (sh.run("zzz"), sh.output())[1])

    def test_package_feeds_racket_require(self):
        ix = Index()
        ix.publish("fsm-dsl", "1.0.0", modules={"fsm": src("fsm")})
        ix.publish("traffic-app", "1.2.0", {"fsm-dsl": "^1.0"}, modules={"traffic": src("traffic")})
        r = Racket()
        with self.assertRaises(LispError): r.run("(require traffic)")
        self.assertEqual(ix.provider_of_module("traffic"), "traffic-app")
        ix.install({"traffic-app": "*"}); ix.sync_racket(r)
        r.run("(require traffic)")
        self.assertEqual(str(r.run("(run 'green '(timer))")), "yellow")
        self.assertEqual(r.where("run"), ("imported", "traffic"))
        ix.uninstall("traffic-app"); ix.sync_racket(r)
        self.assertIn("package-removed", r.w.reasons.values())
        r2 = Racket()
        with self.assertRaises(LispError): r2.run("(require traffic)")

if __name__ == "__main__":
    unittest.main()
