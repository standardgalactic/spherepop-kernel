import os, unittest
from spop.racket import *
from spop.lisp import Sym

RKT = os.path.join(os.path.dirname(__file__), "..", "rkt")


def mk():
    r = Racket(); r.load_dir(RKT); return r


class RacketTests(unittest.TestCase):
    def test_base_language_available(self):
        r = Racket()
        self.assertEqual(r.run("(map (lambda (x) (+ x 1)) '(1 2))"), (2, 3))
        self.assertEqual(r.where("map"), ("language", "base"))

    def test_lazy_load_from_index_instantiates_once(self):
        r = mk()
        self.assertNotIn("units", r.module_names())
        r.run("(require units)")
        self.assertIn("units", r.module_names())
        self.assertEqual(r.run("(c->f 100)"), 212)
        n = len(r.w.view.live("module"))
        r.run("(require units)")
        self.assertEqual(len(r.w.view.live("module")), n)
        self.assertEqual(r.where("c->f"), ("imported", "units"))

    def test_provide_hides_internals(self):
        r = mk(); r.run("(require units)")
        with self.assertRaises(LispError): r.run("(internal-helper 2)")
        self.assertEqual(r.exports("units"), ["c->f", "km->miles"])

    def test_require_forms(self):
        r = mk()
        r.run("(require (only-in units c->f))")
        with self.assertRaises(LispError): r.run("(km->miles 1)")
        r.run("(require (prefix-in u: units))")
        self.assertEqual(r.run("(u:km->miles 1000000)"), 621371)
        r.run("(require (rename-in (only-in units km->miles) (km->miles k2m)))")
        self.assertEqual(r.run("(k2m 1000000)"), 621371)
        r2 = mk()
        with self.assertRaises(LispError): r2.run("(require (only-in units nothing-here))")

    def test_conflicts_are_refusals(self):
        r = mk()
        r.run("(define c->f 1)")
        with self.assertRaises(LispError): r.run("(require units)")
        r = mk(); r.run("(require units)")
        with self.assertRaises(LispError): r.run("(define c->f 1)")
        self.assertIn("already-imported", r.w.reasons.values())
        r.add_source("units2", "(module units2 base (define (c->f x) 0) (provide c->f))")
        with self.assertRaises(LispError): r.run("(require units2)")
        self.assertIn("conflicting-import", r.w.reasons.values())

    def test_module_language_is_a_dsl(self):
        r = mk()
        r.run("(require game)")
        self.assertEqual(r.run("(score 60 30 20)"), 100)      # saturating +
        self.assertEqual(r.run("(+ 60 30 20)"), 110)           # top level uses base +
        self.assertEqual(r.where("score"), ("imported", "game"))
        r.run("(require traffic)")
        self.assertIn(("define-fsm", "fsm"), r.imports_of("traffic"))

    def test_macro_dsl_with_nested_ellipsis(self):
        r = mk(); r.run("(require traffic)")
        self.assertEqual(r.run("(run 'green '(timer timer timer))"), Sym("green"))
        self.assertEqual(r.run("(light 'red 'fault)"), Sym("flashing"))
        self.assertEqual(r.run("(light 'green 'fault)"), Sym("error"))
        self.assertEqual(r.run("(light 'purple 'timer)"), Sym("error"))
        self.assertEqual(r.where("define-fsm"), None)           # macro not leaked

    def test_redeclaration_leaves_old_importers(self):
        r = mk(); r.run("(require units)")
        r.add_source("units", "(module units base (define (c->f c) 0) (provide c->f))")
        r.reload("units")
        self.assertEqual(r.run("(c->f 100)"), 212)             # stale import persists
        self.assertIn("module-redeclared", r.w.reasons.values())
        r2 = Racket(); r2.add_source("units", "(module units base (define (c->f c) 0) (provide c->f))")
        self.assertEqual(r2.run("(require units) (c->f 100)"), 0)

    def test_unknown_module_documented(self):
        r = Racket()
        with self.assertRaises(LispError): r.run("(require no-such)")
        self.assertIn("cannot-open-module", r.w.reasons.values())
        self.assertTrue(r.w.verify())

if __name__ == "__main__":
    unittest.main()
