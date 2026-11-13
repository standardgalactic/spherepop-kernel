"""A small lexically scoped Lisp on SpherePOP.

An environment frame is a sphere, a binding is a sphere coupled to its
frame, a closure is Sphere := Bind(params, scope), and a call is a coupling
sphere that is popped when the activation returns. Mutation is supersession.
"""
import re
from dataclasses import dataclass
from .kernel import World, supersede, attempt_refused


class LispError(Exception):
    pass


class Sym(str):
    pass


@dataclass(frozen=True)
class Closure:
    id: int


@dataclass(frozen=True)
class Builtin:
    name: str
    fn: object

    def __repr__(self):
        return "#<builtin %s>" % self.name


@dataclass(frozen=True)
class Macro:
    literals: tuple
    rules: tuple


ELL = Sym("...")
TOK = re.compile(r'''\s*(?:(;[^\n]*)|(\()|(\))|(')|("(?:[^"\\]|\\.)*")|([^\s()';]+))''')
TAGS = ("binding", "import", "langimport")


def read_all(text):
    toks = []
    for m in TOK.finditer(text):
        if m.group(1) is not None:
            continue
        for g in range(2, 7):
            if m.group(g) is not None:
                toks.append((g, m.group(g)))
                break
    pos, out = 0, []

    def read():
        nonlocal pos
        if pos >= len(toks):
            raise LispError("unexpected end of input")
        g, t = toks[pos]
        pos += 1
        if g == 2:
            items = []
            while True:
                if pos >= len(toks):
                    raise LispError("missing close parenthesis")
                if toks[pos][0] == 3:
                    pos += 1
                    return tuple(items)
                items.append(read())
        if g == 3:
            raise LispError("unexpected close parenthesis")
        if g == 4:
            return (Sym("quote"), read())
        if g == 5:
            return bytes(t[1:-1], "utf8").decode("unicode_escape")
        if t == "#t":
            return True
        if t == "#f":
            return False
        try:
            return int(t)
        except ValueError:
            try:
                return float(t)
            except ValueError:
                return Sym(t)

    while pos < len(toks):
        out.append(read())
    return out


def fmt(v):
    if v is True:
        return "#t"
    if v is False:
        return "#f"
    if v is None:
        return ""
    if isinstance(v, tuple):
        return "(" + " ".join(fmt(x) for x in v) + ")"
    if isinstance(v, Sym):
        return str(v)
    if isinstance(v, str):
        return v
    if isinstance(v, Closure):
        return "#<procedure>"
    return str(v)


def show(v):
    if isinstance(v, str) and not isinstance(v, Sym):
        return '"%s"' % v
    if isinstance(v, tuple):
        return "(" + " ".join(show(x) for x in v) + ")"
    return fmt(v)


# pattern matching for syntax-rules style macros (non-hygienic)
class Seq(list):
    pass


def pvars(p, lits):
    if isinstance(p, Sym):
        return [] if (p in lits or p == ELL or p == "_") else [p]
    if isinstance(p, tuple):
        return [v for q in p for v in pvars(q, lits)]
    return []


def match(p, f, lits, b):
    if isinstance(p, Sym):
        if p in lits:
            return f == p
        if p != "_":
            b[p] = f
        return True
    if isinstance(p, tuple):
        if not isinstance(f, tuple):
            return False
        i = 0
        while i < len(p):
            if i + 1 < len(p) and p[i + 1] == ELL:
                after = p[i + 2:]
                avail = len(f) - i - len(after)
                if avail < 0:
                    return False
                subs = []
                for it in f[i:i + avail]:
                    bb = {}
                    if not match(p[i], it, lits, bb):
                        return False
                    subs.append(bb)
                for v in pvars(p[i], lits):
                    b[v] = Seq(bb[v] for bb in subs)
                return match(after, f[i + avail:], lits, b)
            if i >= len(f) or not match(p[i], f[i], lits, b):
                return False
            i += 1
        return i == len(f)
    return p == f


def expand(t, b):
    if isinstance(t, Sym):
        return b.get(t, t)
    if isinstance(t, tuple):
        out, i = [], 0
        while i < len(t):
            if i + 1 < len(t) and t[i + 1] == ELL:
                vs = [v for v in pvars(t[i], ()) if isinstance(b.get(v), Seq)]
                n = max((len(b[v]) for v in vs), default=0)
                for k in range(n):
                    bb = dict(b)
                    for v in vs:
                        bb[v] = b[v][k]
                    out.append(expand(t[i], bb))
                i += 2
            else:
                out.append(expand(t[i], b))
                i += 1
        return tuple(out)
    return t


PRELUDE = """
(define (map f l) (if (null? l) '() (cons (f (car l)) (map f (cdr l)))))
(define (filter p l) (cond ((null? l) '()) ((p (car l)) (cons (car l) (filter p (cdr l)))) (else (filter p (cdr l)))))
(define (foldl f a l) (if (null? l) a (foldl f (f a (car l)) (cdr l))))
(define (foldr f a l) (if (null? l) a (f (car l) (foldr f a (cdr l)))))
(define (reverse l) (foldl (lambda (acc x) (cons x acc)) '() l))
(define (iota n) (let loop ((i (- n 1)) (acc '())) acc))
(define (range a b) (if (>= a b) '() (cons a (range (+ a 1) b))))
"""
PRELUDE = PRELUDE.replace("(define (iota n) (let loop ((i (- n 1)) (acc '())) acc))\n", "")

CORE = {"quote", "if", "define", "set!", "lambda", "let", "let*", "letrec", "begin", "cond",
        "and", "or", "when", "unless", "define-syntax-rule"}


class Lisp:
    def __init__(self, world=None, boot=True):
        self.w = world or World()
        self.forms = {}
        if boot:
            self.top = self.w.bind("env", None, None)
            self.install_builtins(self.top)
            self.run(PRELUDE, env=self.top)

    # environments
    def new_env(self, parent, deps=()):
        return self.w.bind("env", None, parent, tuple(deps) + ((parent,) if parent is not None else ()))

    def lookup(self, env, name):
        v, e = self.w.view, env
        while e is not None:
            for tag in TAGS:
                i = v.last_key(tag, (e, name))
                if i is not None:
                    return self.w.spheres[i].payload
            e = self.w.spheres[e].payload
        self.err("unbound identifier: %s" % name, "unbound")

    def owner(self, env, name):
        e = env
        while e is not None:
            for tag in TAGS:
                i = self.w.view.last_key(tag, (e, name))
                if i is not None:
                    return e, tag, i
            e = self.w.spheres[e].payload
        return None

    def err(self, msg, reason):
        attempt_refused(self.w, "attempt", msg, reason)
        raise LispError(msg)

    def define(self, env, name, value):
        v = self.w.view
        if v.last_key("import", (env, name)) is not None:
            self.err("define: identifier already imported: %s" % name, "already-imported")
        i = v.last_key("binding", (env, name))
        if i is not None:
            return supersede(self.w, i, value)
        return self.w.bind("binding", (env, name), value, (env,))

    def set_bang(self, env, name, value):
        o = self.owner(env, name)
        if o is None:
            self.err("set!: unbound identifier: %s" % name, "unbound")
        if o[1] != "binding":
            self.err("set!: cannot mutate imported identifier: %s" % name, "immutable-import")
        return supersede(self.w, o[2], value, "set!")

    def lineage(self, env, name):
        """Values of a mutable binding, oldest first, from its supersession chain."""
        o = self.owner(env, name)
        out, i = [], o[2]
        while True:
            s = self.w.spheres[i]
            out.append(s.payload)
            if s.deps and self.w.spheres[s.deps[0]].tag == "binding" and self.w.spheres[s.deps[0]].key == s.key:
                i = s.deps[0]
            else:
                break
        return out[::-1]

    def make_closure(self, params, body, env):
        return Closure(self.w.bind("lambda", None, (params, body), (env,)))

    # running
    def run(self, text, env=None):
        env = self.top if env is None else env
        result = None
        for form in read_all(text):
            result = self.eval(form, env)
            self.w.collapse(lambda v, r=result: show(r), "form-result")
        return result

    def apply_proc(self, f, args):
        if isinstance(f, Builtin):
            return f.fn(*args)
        return self.eval((f,) + tuple((Sym("quote"), a) for a in args), self.top)

    def eval(self, x, env):
        couplings = []
        try:
            value = self._loop(x, env, couplings)
        except BaseException:
            for c in reversed(couplings):
                if self.w.status[c] == "live":
                    self.w.refuse(c, "abort")
            raise
        for c in reversed(couplings):
            self.w.pop(c)
        return value

    def _body(self, forms, env):
        for f in forms[:-1]:
            self.eval(f, env)
        return forms[-1]

    def _loop(self, x, env, couplings):
        w = self.w
        while True:
            if isinstance(x, Sym):
                v = self.lookup(env, x)
                if isinstance(v, Macro):
                    self.err("bad syntax: %s" % x, "syntax")
                return v
            if not isinstance(x, tuple):
                return x
            if not x:
                return ()
            op = x[0]
            if isinstance(op, Sym):
                s = str(op)
                if s == "quote":
                    return x[1]
                if s == "if":
                    t = self.eval(x[1], env)
                    if t is not False:
                        x = x[2]
                    elif len(x) > 3:
                        x = x[3]
                    else:
                        return None
                    continue
                if s == "begin":
                    x = self._body(x[1:], env)
                    continue
                if s in ("when", "unless"):
                    t = self.eval(x[1], env)
                    if (t is not False) == (s == "when"):
                        x = self._body(x[2:], env)
                        continue
                    return None
                if s == "cond":
                    for cl in x[1:]:
                        if cl[0] == "else" or (t := self.eval(cl[0], env)) is not False:
                            if len(cl) == 1:
                                return t
                            x = self._body(cl[1:], env)
                            break
                    else:
                        return None
                    continue
                if s == "and":
                    r = True
                    for a in x[1:]:
                        r = self.eval(a, env)
                        if r is False:
                            return False
                    return r
                if s == "or":
                    for a in x[1:]:
                        r = self.eval(a, env)
                        if r is not False:
                            return r
                    return False
                if s in ("let", "let*", "letrec"):
                    env2 = self.new_env(env)
                    for b in x[1]:
                        val = self.eval(b[1], env if s == "let" else env2)
                        w.bind("binding", (env2, str(b[0])), val, (env2,))
                    env, x = env2, self._body(x[2:], env2)
                    continue
                if s == "define":
                    if isinstance(x[1], tuple):
                        val = self.make_closure(x[1][1:], x[2:], env)
                        self.define(env, str(x[1][0]), val)
                    else:
                        self.define(env, str(x[1]), self.eval(x[2], env))
                    return None
                if s == "set!":
                    self.set_bang(env, str(x[1]), self.eval(x[2], env))
                    return None
                if s == "lambda":
                    return self.make_closure(x[1], x[2:], env)
                if s == "define-syntax-rule":
                    pat = x[1]
                    self.define(env, str(pat[0]), Macro((), ((pat[1:], x[2]),)))
                    return None
                if s in self.forms:
                    return self.forms[s](x, env)
                f = self.lookup(env, op)
            else:
                f = self.eval(op, env)
            if isinstance(f, Macro):
                for pat, tmpl in f.rules:
                    b = {}
                    if match(pat, x[1:], f.literals, b):
                        x = expand(tmpl, b)
                        break
                else:
                    self.err("no matching syntax rule for %s" % op, "syntax")
                continue
            args = [self.eval(a, env) for a in x[1:]]
            if isinstance(f, Closure):
                if couplings:
                    w.pop(couplings.pop())
                params, body = w.spheres[f.id].payload
                cenv = w.spheres[f.id].deps[0]
                call = w.bind("call", None, len(args), (f.id,))
                couplings.append(call)
                env = self.new_env(cenv, (call,))
                if isinstance(params, Sym):
                    w.bind("binding", (env, str(params)), tuple(args), (env, call))
                else:
                    if len(params) != len(args):
                        self.err("arity mismatch: expected %d, given %d" % (len(params), len(args)), "arity")
                    for p, a in zip(params, args):
                        w.bind("binding", (env, str(p)), a, (env, call))
                x = self._body(body, env)
                continue
            if isinstance(f, Builtin):
                return f.fn(*args)
            self.err("application: not a procedure: %s" % show(f), "not-procedure")

    # primitive procedures
    def install_builtins(self, env):
        w = self.w

        def num(name, fn):
            def f(*a):
                for x in a:
                    if isinstance(x, bool) or not isinstance(x, (int, float)):
                        self.err("%s: contract violation, expected number: %s" % (name, show(x)), "contract")
                return fn(*a)
            return f

        def div(a, *r):
            for b in r:
                if b == 0:
                    self.err("/: division by zero", "division-by-zero")
                a = a // b if isinstance(a, int) and isinstance(b, int) and a % b == 0 else a / b
            return a

        def cmp(op):
            return lambda *a: all(op(a[i], a[i + 1]) for i in range(len(a) - 1))

        def sub(a, *r):
            return -a if not r else a - sum(r)

        def mul(*a):
            p = 1
            for x in a:
                p *= x
            return p

        def car(l):
            if not isinstance(l, tuple) or not l:
                self.err("car: contract violation", "contract")
            return l[0]

        def cdr(l):
            if not isinstance(l, tuple) or not l:
                self.err("cdr: contract violation", "contract")
            return l[1:]

        def display(x):
            w.bind("lisp.out", None, fmt(x))

        def error(msg, *rest):
            self.err(" ".join([fmt(msg)] + [show(r) for r in rest]), "user-error")

        prims = {
            "+": num("+", lambda *a: sum(a)), "-": num("-", sub), "*": num("*", mul), "/": num("/", div),
            "=": cmp(lambda a, b: a == b), "<": cmp(lambda a, b: a < b), ">": cmp(lambda a, b: a > b),
            "<=": cmp(lambda a, b: a <= b), ">=": cmp(lambda a, b: a >= b),
            "quotient": lambda a, b: a // b, "remainder": lambda a, b: a % b, "modulo": lambda a, b: a % b,
            "abs": abs, "min": min, "max": max,
            "cons": lambda a, d: (a,) + d, "car": car, "cdr": cdr, "list": lambda *a: tuple(a),
            "null?": lambda x: x == (), "pair?": lambda x: isinstance(x, tuple) and len(x) > 0,
            "not": lambda x: x is False, "number?": lambda x: isinstance(x, (int, float)) and not isinstance(x, bool),
            "symbol?": lambda x: isinstance(x, Sym), "string?": lambda x: isinstance(x, str) and not isinstance(x, Sym),
            "eq?": lambda a, b: (a is b) if isinstance(a, tuple) and a else a == b,
            "equal?": lambda a, b: a == b, "length": len,
            "append": lambda *ls: tuple(x for l in ls for x in l),
            "list-ref": lambda l, i: l[i],
            "string-append": lambda *a: "".join(a),
            "number->string": lambda n: str(n), "string-length": len,
            "symbol->string": lambda s: str(s), "string->symbol": lambda s: Sym(s),
            "display": display, "newline": lambda: w.bind("lisp.out", None, "\n"),
            "apply": lambda f, a: self.apply_proc(f, list(a)), "error": error,
            "void": lambda: None,
        }
        for n, f in prims.items():
            w.bind("binding", (env, n), Builtin(n, f), (env,))

    def output(self):
        return "".join(self.w.view.payload(i) for i in self.w.view.live("lisp.out"))
