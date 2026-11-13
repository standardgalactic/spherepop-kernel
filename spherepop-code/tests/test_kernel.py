import unittest
from spop.kernel import *


class KernelTests(unittest.TestCase):
    def test_primitives_and_status(self):
        w = World()
        a = w.bind("t", "k", 1)
        b = w.bind("t", "k", 2, (a,))
        self.assertEqual(w.view.live("t"), [a, b])
        self.assertEqual(w.pop(a), 1)
        w.refuse(b, "no")
        self.assertEqual(w.view.live("t"), [])
        self.assertEqual(w.status[a], POPPED)
        self.assertEqual(w.reasons[b], "no")

    def test_inadmissible(self):
        w = World()
        a = w.bind("t")
        w.pop(a)
        with self.assertRaises(Inadmissible): w.pop(a)
        with self.assertRaises(Inadmissible): w.refuse(a, "x")
        c = w.bind("t")
        with self.assertRaises(Inadmissible): w.refuse(c, "")
        with self.assertRaises(Inadmissible): w.bind("t", deps=(99,))

    def test_conservation_of_live_count(self):
        w = World()
        live = lambda: sum(len(d) for d in w._tag.values())
        a = w.bind("t"); self.assertEqual(live(), 1)
        w.bind("t", deps=(a,)); self.assertEqual(live(), 2)
        w.collapse(lambda v: v.count("t")); self.assertEqual(live(), 2)
        w.pop(a); self.assertEqual(live(), 1)

    def test_history_strictly_grows(self):
        w = World(); n = 0
        for f in (lambda: w.bind("t"), lambda: w.collapse(lambda v: 0), lambda: w.refuse(0, "r")):
            f(); self.assertGreater(len(w.ledger), n); n = len(w.ledger)

    def test_replay_faithfulness(self):
        w = World()
        a = w.bind("x", 1, "p"); supersede(w, a, "q")
        w.collapse(lambda v: v.count("x"), "n")
        self.assertTrue(w.verify({"n": lambda v: v.count("x")}, w.chain()))

    def test_tamper_detected(self):
        w = World(); a = w.bind("x", 1, "p"); w.pop(a)
        good = w.chain()
        w.ledger[0] = ("bind", 0, "x", 1, "forged", ())
        self.assertNotEqual(w.chain(), good)
        with self.assertRaises(Inadmissible): w.verify(expected_chain=good)

    def test_collapse_digest_checked(self):
        w = World(); w.bind("x", None, 5)
        w.collapse(lambda v: v.payload(0), "val")
        with self.assertRaises(Inadmissible):
            World.replay(w.ledger, {"val": lambda v: 6})

    def test_choice_commutes(self):
        def run(order):
            w = World(); a = w.bind("b"); b = w.bind("b")
            for step in order:
                w.pop(a) if step == "A" else w.refuse(b, "nt")
            return dict(w.status)
        self.assertEqual(run("AB"), run("BA"))

    def test_supersede_lineage(self):
        w = World(); a = w.bind("v", "x", 1)
        b = supersede(w, a, 2); c = supersede(w, b, 3)
        self.assertEqual(w.view.last_key("v", "x"), c)
        self.assertEqual(w.view.ancestors(c), {a, b})

    def test_apply_via(self):
        w = World(); f = w.bind("f", None, lambda x: x + 1); x = w.bind("x", None, 4)
        _, v = apply_via(w, lambda fn, a: fn(a), f, x)
        self.assertEqual(v, 5)

if __name__ == "__main__":
    unittest.main()
