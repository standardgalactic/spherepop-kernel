import itertools, unittest
from spop.regs import *
from spop.kernel import World


def ref_next(q, b):
    return (b,) + q[:-1], q[-1]


class RegisterTests(unittest.TestCase):
    def test_exhaustive_32_cases_and_replay(self):
        for q in itertools.product((0, 1), repeat=4):
            for b in (0, 1):
                r = ShiftRegister(q).edge(b)
                nxt, out = ref_next(q, b)
                self.assertEqual(r.word(), nxt)
                self.assertEqual(r.shifted_out(), out)
                r2 = World.replay(r.w.ledger, {"word": word_rule})
                self.assertEqual(word_rule(r2.view), nxt)
                self.assertEqual(r2.view.payload(r2.view.last("shifted-out")), out)
                self.assertEqual(r.w.view.count("stage"), 4)

    def test_counterexamples(self):
        self.assertEqual(ShiftRegister((1, 0, 0, 0)).edge(0).word(), (0, 1, 0, 0))
        a = ShiftRegister((1, 0, 1, 0)).edge(0)
        b = ShiftRegister((1, 0, 1, 1)).edge(0)
        self.assertEqual(a.word(), (0, 1, 0, 1)); self.assertEqual(b.word(), (0, 1, 0, 1))
        self.assertEqual((a.shifted_out(), b.shifted_out()), (0, 1))
        self.assertNotEqual(a.w.chain(), b.w.chain())

    def test_edge_sequence(self):
        r = ShiftRegister((1, 0, 1, 1))
        for b, expect in ((0, (0, 1, 0, 1)), (0, (0, 0, 1, 0)), (1, (1, 0, 0, 1))):
            self.assertEqual(r.edge(b).word(), expect)
        self.assertTrue(r.w.verify())

    def test_ripple_fault_is_caught_by_the_same_test(self):
        bad = sum(RippleRegister(q).edge(b).word() != ref_next(q, b)[0]
                  for q in itertools.product((0, 1), repeat=4) for b in (0, 1))
        self.assertGreater(bad, 0)
        self.assertEqual(RippleRegister((1, 0, 0, 0)).edge(0).word(), (0, 0, 0, 0))

    def test_transfer_register_exhaustive(self):
        srcs = [5, 9, 12]
        for K in itertools.product((0, 1), repeat=3):
            r = TransferRegister(3)
            if sum(K) > 1:
                with self.assertRaises(ControlError): r.clock(srcs, list(K))
                self.assertEqual(r.value(), 3)
                self.assertIn("multiple-select", r.w.reasons.values())
            else:
                got = r.clock(srcs, list(K))
                self.assertEqual(got, 3 if not any(K) else srcs[K.index(1)])
            self.assertTrue(r.w.verify())

    def test_mux_choice_recorded(self):
        r = TransferRegister(0); r.clock([1, 2, 3], [0, 1, 0])
        why = list(r.w.reasons.values())
        self.assertEqual(why.count("not-selected"), 2)

if __name__ == "__main__":
    unittest.main()
