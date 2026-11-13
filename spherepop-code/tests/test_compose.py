import os, unittest
from spop.kernel import World
from spop.forth import Forth, stack_rule, output_rule
from spop.racket import Racket
from spop.basic import Basic
from spop.shell import *
from spop.regs import ShiftRegister, word_rule

SRC = ": fact dup 1 > if dup 1- recurse * then ; 6 fact . 1 2 + 3 *"


class ComposeTests(unittest.TestCase):
    def test_fragments_commute_in_a_shared_ledger(self):
        alone = Forth().run(SRC)
        w = World()
        f = Forth(w)
        r = Racket(w); r.run("(define (sq x) (* x x)) (sq 12)")
        b = Basic(w); b.enter("10 PRINT 7"); b.enter("RUN")
        m = Machine(w); ubuntu_machine(m); sh = Shell(m, "bash"); sh.run("ls; type cd")
        f.run(SRC)
        sr = ShiftRegister((1, 0, 1, 1), w).edge(0)
        self.assertEqual(f.stack(), alone.stack())
        self.assertEqual(f.output(), alone.output())
        self.assertEqual(f.explain_top(), alone.explain_top())
        self.assertEqual(sr.word(), (0, 1, 0, 1))
        self.assertEqual(b.output(), " 7 \n")
        self.assertEqual(r.run("(sq 5)"), 25)
        self.assertTrue(w.verify())
        tags = {s.tag for s in w.spheres.values()}
        self.assertTrue({"cell", "binding", "line", "fs", "stage"} <= tags)

    def test_value_crosses_languages_through_spheres(self):
        w = World(); r = Racket(w); f = Forth(w)
        v = r.run("(foldl + 0 (range 1 11))")
        f.push(v, "from-lisp"); f.run("dup *")
        self.assertEqual(f.stack(), [3025])

if __name__ == "__main__":
    unittest.main()
