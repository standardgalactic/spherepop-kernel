import unittest
from spop.lisp import *


class LispTests(unittest.TestCase):
    def setUp(self):
        self.L = Lisp()

    def ev(self, s):
        return self.L.run(s)

    def test_arith_and_lists(self):
        self.assertEqual(self.ev("(+ 1 2 3)"), 6)
        self.assertEqual(self.ev("(map (lambda (x) (* x x)) '(1 2 3))"), (1, 4, 9))
        self.assertEqual(self.ev("(foldl + 0 (range 0 11))"), 55)
        self.assertEqual(self.ev("(reverse '(1 2 3))"), (3, 2, 1))
        self.assertEqual(self.ev("(filter (lambda (x) (> x 1)) '(1 2 3))"), (2, 3))

    def test_recursion(self):
        self.ev("(define (fact n) (if (= n 0) 1 (* n (fact (- n 1)))))")
        self.assertEqual(self.ev("(fact 12)"), 479001600)
        self.ev("(define (fib n) (if (< n 2) n (+ (fib (- n 1)) (fib (- n 2)))))")
        self.assertEqual(self.ev("(fib 15)"), 610)

    def test_tail_calls_pop_frames(self):
        self.ev("(define (loop n acc) (if (= n 0) acc (loop (- n 1) (+ acc 1))))")
        self.assertEqual(self.ev("(loop 5000 0)"), 5000)
        self.assertEqual(self.L.w.view.count("call"), 0)

    def test_closures_and_mutation_lineage(self):
        self.ev("(define (make-counter) (let ((n 0)) (lambda () (set! n (+ n 1)) n)))")
        self.ev("(define c (make-counter))")
        self.assertEqual([self.ev("(c)") for _ in range(3)], [1, 2, 3])
        d = self.ev("(define d (make-counter))")
        self.assertEqual(self.ev("(d)"), 1)
        # find c's captured frame through the closure sphere
        cl = self.L.lookup(self.L.top, "c")
        env = self.L.w.spheres[cl.id].deps[0]
        self.assertEqual(self.L.lineage(env, "n"), [0, 1, 2, 3])

    def test_scope_is_lexical(self):
        self.ev("(define x 1)")
        self.ev("(define (f) x)")
        self.assertEqual(self.ev("(let ((x 2)) (f))"), 1)
        self.assertEqual(self.ev("(let ((x 2)) x)"), 2)

    def test_macros(self):
        self.ev("(define-syntax-rule (swap! a b) (let ((t a)) (set! a b) (set! b t)))")
        self.ev("(define p 1) (define q 2) (swap! p q)")
        self.assertEqual(self.ev("(list p q)"), (2, 1))
        self.ev("(define-syntax-rule (my-or2 a b) (let ((t a)) (if t t b)))")
        self.assertEqual(self.ev("(my-or2 #f 7)"), 7)
        self.ev("(define-syntax-rule (my-list (k v) ...) (list (list 'k v) ...))")
        self.assertEqual(self.ev("(my-list (a 1) (b 2))"), ((Sym("a"), 1), (Sym("b"), 2)))

    def test_errors_refused_and_cleaned(self):
        for bad in ("(car 5)", "(undefined-thing)", "(/ 1 0)", "((lambda (x) x))"):
            with self.assertRaises(LispError): self.ev(bad)
        self.assertEqual(self.L.w.view.count("call"), 0)
        reasons = set(self.L.w.reasons.values())
        self.assertTrue({"contract", "unbound", "division-by-zero", "arity"} <= reasons)

    def test_output_and_replay(self):
        self.ev('(display "a") (display (list 1 2)) (newline)')
        self.assertEqual(self.L.output(), "a(1 2)\n")
        self.assertTrue(self.L.w.verify())

    def test_variadic(self):
        self.assertEqual(self.ev("((lambda args (length args)) 1 2 3)"), 3)

if __name__ == "__main__":
    unittest.main()
