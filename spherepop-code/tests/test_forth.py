import random, unittest
from spop.forth import Forth, ForthError


class Ref:
    """Independent plain-list reference for the stack subset."""
    def run(self, toks):
        s = []
        for t in toks:
            if t.lstrip("-").isdigit(): s.append(int(t))
            elif t == "+": b = s.pop(); a = s.pop(); s.append(a + b)
            elif t == "-": b = s.pop(); a = s.pop(); s.append(a - b)
            elif t == "*": b = s.pop(); a = s.pop(); s.append(a * b)
            elif t == "dup": s.append(s[-1])
            elif t == "drop": s.pop()
            elif t == "swap": s[-1], s[-2] = s[-2], s[-1]
            elif t == "over": s.append(s[-2])
            elif t == "rot": s.append(s.pop(-3))
            elif t == "nip": del s[-2]
            elif t == "tuck": s.insert(-2, s[-1])
        return s


EFFECT = {"+": (2, -1), "-": (2, -1), "*": (2, -1), "dup": (1, 1), "drop": (1, -1), "swap": (2, 0),
          "over": (2, 1), "rot": (3, 0), "nip": (2, -1), "tuck": (2, 1)}


class ForthTests(unittest.TestCase):
    def test_instruction_boundary_invariant(self):
        # pi(H_i) = S_i after every completed instruction
        random.seed(7)
        for _ in range(200):
            f, ref, depth, toks = Forth(), Ref(), 0, []
            for _ in range(25):
                ok = [w for w, (n, d) in EFFECT.items() if depth >= n]
                t = random.choice(ok + ["%d" % random.randint(-9, 9)] * 2)
                toks.append(t)
                f.run(t)
                depth += EFFECT[t][1] if t in EFFECT else 1
                self.assertEqual(f.stack(), Ref().run(toks))
            f.w.verify()

    def test_basics(self):
        f = Forth().run("2 3 +")
        self.assertEqual(f.stack(), [5])
        self.assertEqual(Forth().run("10 3 - 2 *").stack(), [14])
        self.assertEqual(Forth().run("3 10 -").stack(), [-7])

    def test_provenance_distinguishes_equal_stacks(self):
        a, b = Forth().run("2 3 +"), Forth().run("5")
        self.assertEqual(a.stack(), b.stack())
        self.assertEqual(a.explain_top(), "(2 + 3)")
        self.assertEqual(b.explain_top(), "5")
        self.assertEqual(Forth().run("3 dup *").explain_top(), "(3 * 3)")

    def test_definitions_and_shadowing(self):
        f = Forth().run(": sq dup * ; : cube dup sq * ; 3 cube")
        self.assertEqual(f.stack(), [27])
        f.run(": sq drop 0 ; 3 cube")
        self.assertEqual(f.stack(), [27, 27])          # early binding: cube still uses the old sq
        self.assertIn("shadowed", f.w.reasons.values())
        g = Forth(early_binding=False).run(": sq dup * ; : cube dup sq * ; 3 cube : sq drop 0 ; 3 cube".replace("3 cube : sq", "3 cube\n: sq"))
        self.assertEqual(g.stack(), [27, 0])           # late binding: cube sees the new sq

    def test_unknown_word_in_definition_is_refused_at_compile_time(self):
        f = Forth()
        with self.assertRaises(ForthError): f.run(": bad nosuch ;")
        self.assertIn("unknown-word", f.w.reasons.values())

    def test_control_and_recursion(self):
        f = Forth().run(": fact dup 1 > if dup 1- recurse * then ; 10 fact")
        self.assertEqual(f.stack(), [3628800])
        f = Forth().run(": abs2 dup 0< if negate then ; -5 abs2 5 abs2")
        self.assertEqual(f.stack(), [5, 5])
        f = Forth().run("0 10 0 do i + loop")
        self.assertEqual(f.stack(), [45])
        f = Forth().run("1 begin dup 100 < while 2 * repeat")
        self.assertEqual(f.stack(), [128])
        f = Forth().run("0 begin 1+ dup 5 = until")
        self.assertEqual(f.stack(), [5])

    def test_variables(self):
        f = Forth().run("variable x 5 x ! x @ 3 + x ! x @")
        self.assertEqual(f.stack(), [5, 8][1:])

    def test_choice_recorded(self):
        f = Forth().run("1 if 7 else 8 then")
        taken = [s for s in f.w.spheres.values() if s.tag == "branch" and f.w.status[s.id] == "popped"]
        refused = [s for s in f.w.spheres.values() if s.tag == "branch" and f.w.status[s.id] == "refused"]
        self.assertEqual((len(taken), len(refused)), (1, 1))

    def test_errors_are_documented_refusals(self):
        f = Forth()
        f.run("1 2")
        with self.assertRaises(ForthError): f.run("+ + +")
        self.assertEqual(f.stack(), [])
        att = [i for i in f.w.view.live("attempt")] + [s.id for s in f.w.spheres.values() if s.tag == "attempt"]
        self.assertTrue(any(f.w.reasons.get(i) == "stack-underflow" for i in att))
        with self.assertRaises(ForthError): Forth().run("1 0 /")
        with self.assertRaises(ForthError): Forth().run("nosuchword")

    def test_output(self):
        f = Forth().run('." hi " 1 2 + . cr')
        self.assertEqual(f.output(), "hi 3 \n")

    def test_replay(self):
        f = Forth().run(": f 3 0 do i . loop ; f 1 2 +")
        self.assertTrue(f.w.verify())

if __name__ == "__main__":
    unittest.main()
