"""Forth on SpherePOP: stack cells are spheres, the stack is a collapse."""
import re
from .kernel import World, supersede, choose, attempt_refused


class ForthError(Exception):
    pass


def stack_rule(v):
    return tuple(v.payload(i) for i in v.live("cell"))


def output_rule(v):
    return "".join(v.payload(i) for i in v.live("forth.out"))


PASS = {"dup", "swap", "over", "rot", "tuck", "?dup", "2dup", "2swap", "-rot"}
TOKEN = re.compile(r'\."\s[^"]*"|\(\s[^)]*\)|\\[^\n]*|\S+')


class Forth:
    def __init__(self, world=None, early_binding=True):
        self.w = world or World()
        self.early = early_binding
        self.depth = 0
        b = {
            "+": lambda a, c: a + c, "-": lambda a, c: a - c, "*": lambda a, c: a * c,
            "/": lambda a, c: a // c, "mod": lambda a, c: a % c,
            "max": max, "min": min,
            "and": lambda a, c: a & c, "or": lambda a, c: a | c, "xor": lambda a, c: a ^ c,
            "=": lambda a, c: -(a == c), "<>": lambda a, c: -(a != c), "<": lambda a, c: -(a < c),
            ">": lambda a, c: -(a > c), "<=": lambda a, c: -(a <= c), ">=": lambda a, c: -(a >= c),
        }
        self.binary = b
        self.unary = {
            "negate": lambda a: -a, "abs": abs, "1+": lambda a: a + 1, "1-": lambda a: a - 1,
            "2*": lambda a: a * 2, "2/": lambda a: a // 2, "0=": lambda a: -(a == 0),
            "0<": lambda a: -(a < 0), "invert": lambda a: ~a,
        }

    NAMES = {"dup", "?dup", "drop", "nip", "swap", "over", "rot", "-rot", "tuck", "2dup", "2drop", "depth",
             "true", "false", ".", "emit", "cr", ".s", "i", "j", "@", "!", "+!"}

    def is_builtin(self, name):
        return name in self.binary or name in self.unary or name in self.NAMES

    # observation
    def stack(self):
        return list(stack_rule(self.w.view))

    def output(self):
        return output_rule(self.w.view)

    # state transitions: every one is a composition of the four primitives
    def push(self, n, key=None, deps=()):
        return self.w.bind("cell", key, n, deps)

    def fault(self, word, reason):
        attempt_refused(self.w, "attempt", word, reason)
        raise ForthError("%s: %s" % (word, reason))

    def need(self, n, word):
        if self.w.view.count("cell") < n:
            self.fault(word, "stack-underflow")

    def pop1(self):
        i = self.w.view.last("cell")
        return self.w.pop(i), i

    def emit(self, text):
        self.w.bind("forth.out", None, text)

    # reading source
    def parse(self, toks, p, terms):
        items = []
        while p < len(toks):
            t = toks[p]
            tl = t.lower()
            if tl in terms:
                return items, p + 1, tl
            p += 1
            if tl == "if":
                a, p, term = self.parse(toks, p, {"else", "then"})
                b = []
                if term == "else":
                    b, p, term = self.parse(toks, p, {"then"})
                if term != "then":
                    self.fault("if", "unterminated")
                items.append(("if", tuple(a), tuple(b)))
            elif tl == "begin":
                a, p, term = self.parse(toks, p, {"until", "while"})
                if term == "until":
                    items.append(("until", tuple(a)))
                elif term == "while":
                    b, p, term = self.parse(toks, p, {"repeat"})
                    items.append(("while", tuple(a), tuple(b)))
                else:
                    self.fault("begin", "unterminated")
            elif tl == "do":
                a, p, term = self.parse(toks, p, {"loop", "+loop"})
                if term is None:
                    self.fault("do", "unterminated")
                items.append(("do", tuple(a), term == "+loop"))
            elif t.startswith('." '):
                items.append(("print", t[3:-1]))
            elif t.startswith("(") or t.startswith("\\"):
                continue
            elif tl in ("variable", "constant"):
                items.append((tl, toks[p].lower()))
                p += 1
            elif tl == ":":
                name = toks[p].lower()
                body, p, term = self.parse(toks, p + 1, {";"})
                if term is None:
                    self.fault(":", "unterminated")
                items.append(("define", name, tuple(body)))
            elif re.fullmatch(r"-?\d+", t):
                items.append(("lit", int(t)))
            else:
                items.append(("call", tl))
        return items, p, None

    def run(self, src):
        toks = TOKEN.findall(src)
        items, _, _ = self.parse(toks, 0, set())
        try:
            self.run_items(items)
        except ForthError:
            self.abort()
            raise
        self.w.collapse(stack_rule, "stack")
        return self

    def abort(self):
        for tag in ("cell", "frame", "loop", "iter"):
            for i in self.w.view.live(tag):
                self.w.refuse(i, "abort")
        self.depth = 0

    # execution
    def run_items(self, items):
        for it in items:
            self.run_item(it)

    def run_item(self, it):
        w, k = self.w, it[0]
        if k == "lit":
            self.push(it[1])
        elif k == "call":
            self.call(it[1])
        elif k == "callw":
            self.call_word(it[1])
        elif k == "callb":
            self.builtin(it[1])
        elif k == "print":
            self.emit(it[1])
        elif k == "if":
            self.need(1, "if")
            flag, fid = self.pop1()
            a = w.bind("branch", "then", it[1], (fid,))
            b = w.bind("branch", "else", it[2], (fid,))
            taken, other = (a, b) if flag != 0 else (b, a)
            choose(w, taken, [other])
            self.run_items(w.spheres[taken].payload)
        elif k == "until":
            while True:
                n = w.bind("iter", None, "until")
                self.run_items(it[1])
                self.need(1, "until")
                flag, _ = self.pop1()
                w.pop(n)
                if flag != 0:
                    break
        elif k == "while":
            while True:
                n = w.bind("iter", None, "while")
                self.run_items(it[1])
                self.need(1, "while")
                flag, _ = self.pop1()
                if flag == 0:
                    w.pop(n)
                    break
                self.run_items(it[2])
                w.pop(n)
        elif k == "do":
            self.need(2, "do")
            start, _ = self.pop1()
            limit, _ = self.pop1()
            lid = w.bind("loop", None, (start, limit))
            while True:
                self.run_items(it[1])
                idx, lim = w.spheres[lid].payload
                step = 1
                if it[2]:
                    self.need(1, "+loop")
                    step, _ = self.pop1()
                idx += step
                if (idx >= lim) if step > 0 else (idx < lim):
                    w.pop(lid)
                    break
                lid = supersede(w, lid, (idx, lim), "advance")
        elif k == "define":
            prior = w.view.last_key("word", it[1])
            if prior is not None:
                w.refuse(prior, "shadowed")
            body = self.resolve_body(it[2]) if self.early else it[2]
            w.bind("word", it[1], body, (prior,) if prior is not None else ())
        elif k == "variable":
            w.bind("forth.var", it[1], 0)
        elif k == "constant":
            self.need(1, "constant")
            v, vid = self.pop1()
            w.bind("const", it[1], v, (vid,))

    def resolve_body(self, items):
        """Early binding: a call inside a definition is fixed to the word it names when compiled."""
        out = []
        for it in items:
            k = it[0]
            if k == "call":
                n = it[1]
                wid = self.w.view.last_key("word", n)
                if n == "recurse" or self.w.view.last_key("forth.var", n) is not None \
                        or self.w.view.last_key("const", n) is not None:
                    out.append(it)
                elif wid is not None:
                    out.append(("callw", wid))
                elif self.is_builtin(n):
                    out.append(("callb", n))
                else:
                    self.fault(n, "unknown-word")
            elif k == "if":
                out.append(("if", self.resolve_body(it[1]), self.resolve_body(it[2])))
            elif k == "until":
                out.append(("until", self.resolve_body(it[1])))
            elif k == "while":
                out.append(("while", self.resolve_body(it[1]), self.resolve_body(it[2])))
            elif k == "do":
                out.append(("do", self.resolve_body(it[1]), it[2]))
            else:
                out.append(it)
        return tuple(out)

    def call_word(self, wid):
        w = self.w
        self.depth += 1
        frame = w.bind("frame", self.depth, w.spheres[wid].key, (wid,))
        self.run_items(w.spheres[wid].payload)
        w.pop(frame)
        self.depth -= 1

    def call(self, name):
        w = self.w
        wid = w.view.last_key("word", name)
        if name == "recurse":
            f = w.view.last("frame")
            if f is None:
                self.fault(name, "outside-definition")
            wid = w.spheres[f].deps[0]
        if wid is not None:
            self.call_word(wid)
        elif w.view.last_key("forth.var", name) is not None:
            self.push(("addr", name), "addr")
        elif w.view.last_key("const", name) is not None:
            c = w.view.last_key("const", name)
            self.push(w.spheres[c].payload, "const", (c,))
        else:
            self.builtin(name)

    def builtin(self, name):
        w, v = self.w, self.w.view
        if name in self.binary:
            self.need(2, name)
            ids = v.live("cell")[-2:]
            x, y = v.payload(ids[0]), v.payload(ids[1])
            try:
                r = self.binary[name](x, y)
            except ZeroDivisionError:
                self.fault(name, "division-by-zero")
            w.pop(ids[1]); w.pop(ids[0])
            self.push(r, name, tuple(ids))
        elif name in self.unary:
            self.need(1, name)
            x, i = self.pop1()
            self.push(self.unary[name](x), name, (i,))
        elif name == "dup":
            self.need(1, name)
            t = v.last("cell"); self.push(v.payload(t), "dup", (t,))
        elif name == "?dup":
            self.need(1, name)
            t = v.last("cell")
            if v.payload(t) != 0:
                self.push(v.payload(t), "dup", (t,))
        elif name == "drop":
            self.need(1, name); w.refuse(v.last("cell"), "drop")
        elif name == "nip":
            self.need(2, name); w.refuse(v.live("cell")[-2], "nip")
        elif name == "swap":
            self.need(2, name)
            b, bi = self.pop1(); a, ai = self.pop1()
            self.push(b, "swap", (bi,)); self.push(a, "swap", (ai,))
        elif name == "over":
            self.need(2, name)
            s = v.live("cell")[-2]; self.push(v.payload(s), "over", (s,))
        elif name == "rot":
            self.need(3, name)
            c, ci = self.pop1(); b, bi = self.pop1(); a, ai = self.pop1()
            self.push(b, "rot", (bi,)); self.push(c, "rot", (ci,)); self.push(a, "rot", (ai,))
        elif name == "-rot":
            self.need(3, name)
            c, ci = self.pop1(); b, bi = self.pop1(); a, ai = self.pop1()
            self.push(c, "rot", (ci,)); self.push(a, "rot", (ai,)); self.push(b, "rot", (bi,))
        elif name == "tuck":
            self.need(2, name)
            b, bi = self.pop1(); a, ai = self.pop1()
            self.push(b, "tuck", (bi,)); self.push(a, "tuck", (ai,)); self.push(b, "tuck", (bi,))
        elif name == "2dup":
            self.need(2, name)
            for s in v.live("cell")[-2:]:
                self.push(v.payload(s), "dup", (s,))
        elif name == "2drop":
            self.need(2, name)
            for s in v.live("cell")[-2:]:
                w.refuse(s, "drop")
        elif name == "depth":
            self.push(v.count("cell"), "depth")
        elif name == "true":
            self.push(-1, "true")
        elif name == "false":
            self.push(0, "false")
        elif name == ".":
            self.need(1, name); x, _ = self.pop1(); self.emit("%s " % (x,))
        elif name == "emit":
            self.need(1, name); x, _ = self.pop1(); self.emit(chr(x))
        elif name == "cr":
            self.emit("\n")
        elif name == ".s":
            self.emit("<%d> %s " % (v.count("cell"), " ".join(str(x) for x in stack_rule(v))))
        elif name in ("i", "j"):
            ls = v.live("loop")
            n = 1 if name == "i" else 2
            if len(ls) < n:
                self.fault(name, "outside-loop")
            lid = ls[-n]
            self.push(w.spheres[lid].payload[0], name, (lid,))
        elif name == "@":
            self.need(1, name)
            a, ai = self.pop1()
            vid = v.last_key("forth.var", a[1])
            self.push(w.spheres[vid].payload, "@", (vid,))
        elif name == "!":
            self.need(2, name)
            a, _ = self.pop1(); x, xi = self.pop1()
            vid = v.last_key("forth.var", a[1])
            nid = supersede(w, vid, x)
        elif name == "+!":
            self.need(2, name)
            a, _ = self.pop1(); x, _ = self.pop1()
            vid = v.last_key("forth.var", a[1])
            supersede(w, vid, w.spheres[vid].payload + x)
        else:
            self.fault(name, "unknown-word")

    # provenance: how did a stack position come to exist
    def explain(self, cid):
        s = self.w.spheres[cid]
        if not s.deps:
            return str(s.payload)
        if s.key in PASS or s.key in ("@", "const", "depth", "i", "j", "dup"):
            return self.explain(s.deps[0])
        if len(s.deps) == 2:
            return "(%s %s %s)" % (self.explain(s.deps[0]), s.key, self.explain(s.deps[1]))
        return "%s(%s)" % (s.key, self.explain(s.deps[0]))

    def explain_top(self):
        return self.explain(self.w.view.last("cell"))
