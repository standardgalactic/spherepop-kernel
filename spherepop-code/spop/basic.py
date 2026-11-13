"""Commodore-style BASIC on SpherePOP.

Program lines, variables, memory cells, call stacks and disk files are all
spheres. Entering a line with an existing number supersedes it, an empty
line refuses it, and LOAD couples each loaded line to the file it came from.
"""
import math
import random
import re
from .kernel import World, supersede, attempt_refused


class BasicError(Exception):
    pass


KEYWORDS = sorted(["PRINT", "INPUT", "LET", "GOTO", "GOSUB", "RETURN", "IF", "FOR", "NEXT", "DIM", "READ",
                   "DATA", "RESTORE", "POKE", "REM", "END", "STOP", "ON", "RUN", "LIST", "NEW", "LOAD", "SAVE",
                   "CLR", "?"], key=len, reverse=True)
FUNCS = {"INT", "ABS", "SGN", "SQR", "RND", "LEN", "LEFT$", "RIGHT$", "MID$", "CHR$", "ASC", "STR$", "VAL",
         "PEEK", "SIN", "COS", "ATN", "LOG", "EXP", "FRE", "TAB"}
ERR = {"syntax": "SYNTAX  ERROR", "undef": "UNDEF'D STATEMENT  ERROR", "return": "RETURN WITHOUT GOSUB  ERROR",
       "next": "NEXT WITHOUT FOR  ERROR", "data": "OUT OF DATA  ERROR", "div": "DIVISION BY ZERO  ERROR",
       "type": "TYPE MISMATCH  ERROR", "qty": "ILLEGAL QUANTITY  ERROR", "subscript": "BAD SUBSCRIPT  ERROR",
       "notfound": "FILE NOT FOUND  ERROR", "device": "DEVICE NOT PRESENT  ERROR",
       "exists": "FILE EXISTS  ERROR", "break": "BREAK", "input": "OUT OF DATA  ERROR"}
TOKRE = re.compile(r'\s*(?:(\d+\.?\d*(?:E[+-]?\d+)?|\.\d+)|("[^"]*"?)|([A-Z][A-Z0-9]*\$?%?)|(<>|<=|>=|[-+*/^()<>=,;:]))', re.I)


def split_stmts(text):
    out, cur, q = [], "", False
    for ch in text:
        if ch == '"':
            q = not q
        if ch == ":" and not q:
            out.append(cur)
            cur = ""
        else:
            cur += ch
    out.append(cur)
    return [s.strip() for s in out if s.strip()]


def varkey(name):
    name = name.upper()
    suffix = name[-1] if name[-1] in "$%" else ""
    base = name[:-1] if suffix else name
    return base[:2] + suffix          # only two characters are significant


def fmt_num(x):
    if isinstance(x, float) and x == int(x) and abs(x) < 1e9:
        x = int(x)
    s = ("%d" % x) if isinstance(x, int) else "%.9g" % x
    return (" " if x >= 0 else "") + s + " "


class Basic:
    def __init__(self, world=None, inputs=(), seed=1, max_steps=200000, device=8):
        self.w = world or World()
        self.rng = random.Random(seed)
        self.max_steps = max_steps
        self.device = device
        self.col = 0
        for i, t in enumerate(inputs):
            self.w.bind("basic.in", i, t)

    # observation
    def output(self):
        return "".join(self.w.view.payload(i) for i in self.w.view.live("basic.out"))

    def emit(self, text):
        self.w.bind("basic.out", None, text)
        nl = text.rfind("\n")
        self.col = len(text) - nl - 1 if nl >= 0 else self.col + len(text)

    def numbers(self):
        v = self.w.view
        return sorted(v.sphere(i).key for i in v.live("line"))

    def listing(self):
        v = self.w.view
        return "\n".join("%d %s" % (n, v.payload(v.last_key("line", n))) for n in self.numbers())

    def fail(self, kind, line=None):
        attempt_refused(self.w, "attempt", kind, kind)
        msg = "?" + ERR[kind] + ((" IN %d" % line) if line is not None else "")
        self.emit(("\n" if self.col else "") + msg + "\n")
        raise BasicError(msg)

    # program store: the editor
    def enter(self, text):
        text = text.strip()
        m = re.match(r"(\d+)\s*(.*)$", text)
        v = self.w.view
        if not m:
            return self.direct(text)
        n, body = int(m.group(1)), m.group(2)
        old = v.last_key("line", n)
        if not body:
            if old is not None:
                self.w.refuse(old, "deleted")
        elif old is not None:
            supersede(self.w, old, body, "replaced")
        else:
            self.w.bind("line", n, body)

    def direct(self, text):
        for st in split_stmts(text):
            sig = self.exec_stmt(st, None)
            if sig and sig[0] == "run":
                self.run_program()

    # variables
    def get(self, key):
        i = self.w.view.last_key("basic.var", key)
        if i is None:
            return "" if key.endswith("$") else 0
        return self.w.view.payload(i)

    def put(self, key, val, line=None):
        if key.endswith("$") != isinstance(val, str):
            self.fail("type", line)
        i = self.w.view.last_key("basic.var", key)
        if i is None:
            self.w.bind("basic.var", key, val)
        else:
            supersede(self.w, i, val)

    def elem(self, name, idx, line):
        key = varkey(name)
        d = self.w.view.last_key("dim", key)
        size = 10 if d is None else self.w.view.payload(d)
        if not (0 <= idx <= size):
            self.fail("subscript", line)
        return key, int(idx)

    # expressions
    def tokens(self, text, line):
        pos, out = 0, []
        text = text.rstrip()
        while pos < len(text):
            m = TOKRE.match(text, pos)
            if not m or m.end() == pos:
                self.fail("syntax", line)
            pos = m.end()
            if m.group(1) is not None:
                n = m.group(1)
                out.append(("n", float(n) if re.search(r"[.E]", n, re.I) else int(n)))
            elif m.group(2) is not None:
                out.append(("s", m.group(2).strip('"')))
            elif m.group(3) is not None:
                out.append(("id", m.group(3).upper()))
            else:
                out.append(("op", m.group(4)))
        return out

    def evaluate(self, text, line=None):
        toks = self.tokens(text, line)
        p = [0]
        w = self

        def peek():
            return toks[p[0]] if p[0] < len(toks) else (None, None)

        def take():
            t = peek(); p[0] += 1; return t

        def isop(*ops):
            t = peek(); return t[0] == "op" and t[1] in ops

        def isid(*ids):
            t = peek(); return t[0] == "id" and t[1] in ids

        def num(x):
            if isinstance(x, str):
                w.fail("type", line)
            return x

        def expr():
            a = and_()
            while isid("OR"):
                take(); a = int(num(a)) | int(num(and_()))
            return a

        def and_():
            a = not_()
            while isid("AND"):
                take(); a = int(num(a)) & int(num(not_()))
            return a

        def not_():
            if isid("NOT"):
                take(); return ~int(num(not_()))
            return cmp_()

        def cmp_():
            a = add()
            while isop("=", "<>", "<", ">", "<=", ">="):
                op = take()[1]; b = add()
                if isinstance(a, str) != isinstance(b, str):
                    w.fail("type", line)
                a = -int({"=": a == b, "<>": a != b, "<": a < b, ">": a > b, "<=": a <= b, ">=": a >= b}[op])
            return a

        def add():
            a = mul()
            while isop("+", "-"):
                op = take()[1]; b = mul()
                if op == "+" and isinstance(a, str) and isinstance(b, str):
                    a = a + b
                else:
                    a = num(a) + num(b) if op == "+" else num(a) - num(b)
            return a

        def mul():
            a = unary()
            while isop("*", "/"):
                op = take()[1]; b = unary()
                if op == "/":
                    if num(b) == 0:
                        w.fail("div", line)
                    a = num(a) / b
                else:
                    a = num(a) * num(b)
            return a

        def unary():
            if isop("-"):
                take(); return -num(unary())
            if isop("+"):
                take(); return num(unary())
            return power()

        def power():
            a = primary()
            while isop("^"):
                take(); a = num(a) ** num(primary())
            return a

        def args():
            out = []
            if isop("("):
                take()
                out.append(expr())
                while isop(","):
                    take(); out.append(expr())
                if not isop(")"):
                    w.fail("syntax", line)
                take()
            return out

        def primary():
            t = take()
            if t[0] in ("n", "s"):
                return t[1]
            if t == ("op", "("):
                v = expr()
                if not isop(")"):
                    w.fail("syntax", line)
                take(); return v
            if t[0] == "id":
                name = t[1]
                if name in FUNCS:
                    return w.func(name, args(), line)
                if isop("("):
                    a = args()
                    key, i = w.elem(name, num(a[0]), line)
                    j = w.w.view.last_key("elem", (key, i))
                    return ("" if key.endswith("$") else 0) if j is None else w.w.view.payload(j)
                return w.get(varkey(name))
            w.fail("syntax", line)

        val = expr()
        if p[0] != len(toks):
            self.fail("syntax", line)
        return val

    def func(self, name, a, line):
        def n(i):
            if isinstance(a[i], str):
                self.fail("type", line)
            return a[i]
        try:
            if name == "INT": return math.floor(n(0))
            if name == "ABS": return abs(n(0))
            if name == "SGN": return (n(0) > 0) - (n(0) < 0)
            if name == "SQR":
                if n(0) < 0: self.fail("qty", line)
                return math.sqrt(n(0))
            if name == "RND": return self.rng.random()
            if name == "LEN": return len(a[0])
            if name == "LEFT$": return a[0][:int(n(1))]
            if name == "RIGHT$": return a[0][-int(n(1)):] if int(n(1)) > 0 else ""
            if name == "MID$": return a[0][int(n(1)) - 1:int(n(1)) - 1 + (int(n(2)) if len(a) > 2 else 10 ** 6)]
            if name == "CHR$": return chr(int(n(0)))
            if name == "ASC": return ord(a[0][0]) if a[0] else self.fail("qty", line)
            if name == "STR$": return fmt_num(n(0)).rstrip() if n(0) < 0 else fmt_num(n(0)).rstrip()
            if name == "VAL":
                m = re.match(r"\s*[-+]?\d*\.?\d+", a[0]); return float(m.group()) if m and "." in m.group() else (int(m.group()) if m else 0)
            if name == "PEEK":
                i = self.w.view.last_key("mem", int(n(0)))
                return 0 if i is None else self.w.view.payload(i)
            if name == "SIN": return math.sin(n(0))
            if name == "COS": return math.cos(n(0))
            if name == "ATN": return math.atan(n(0))
            if name == "LOG":
                if n(0) <= 0: self.fail("qty", line)
                return math.log(n(0))
            if name == "EXP": return math.exp(n(0))
            if name == "FRE": return 38911 - sum(len(self.w.view.payload(i)) for i in self.w.view.live("line"))
            if name == "TAB": return " " * max(0, int(n(0)) - self.col)
        except IndexError:
            self.fail("syntax", line)

    # statements
    def exec_stmt(self, st, line, ctx=None):
        up = st.upper()
        kw = next((k for k in KEYWORDS if up.startswith(k)), None)
        rest = st[len(kw):].strip() if kw else st
        w, v = self.w, self.w.view
        if kw is None:
            m = re.match(r"([A-Za-z][A-Za-z0-9]*[$%]?)\s*(\((.*?)\))?\s*=(.*)$", st)
            if not m:
                self.fail("syntax", line)
            self.assign(m, line)
            return None
        if kw == "LET":
            m = re.match(r"([A-Za-z][A-Za-z0-9]*[$%]?)\s*(\((.*?)\))?\s*=(.*)$", rest)
            if not m: self.fail("syntax", line)
            self.assign(m, line); return None
        if kw in ("PRINT", "?"):
            self.do_print(rest, line); return None
        if kw == "REM" or kw == "DATA":
            return None
        if kw == "GOTO":
            return ("goto", int(rest))
        if kw == "GOSUB":
            return ("gosub", int(rest))
        if kw == "RETURN":
            return ("return",)
        if kw in ("END", "STOP"):
            return ("end" if kw == "END" else "break",)
        if kw == "IF":
            m = re.match(r"(.*?)\bTHEN\b(.*)$", rest, re.I)
            if not m:
                m2 = re.match(r"(.*?)\bGOTO\b(.*)$", rest, re.I)
                if not m2: self.fail("syntax", line)
                cond, then = m2.group(1), "GOTO" + m2.group(2)
            else:
                cond, then = m.group(1), m.group(2).strip()
            if self.evaluate(cond, line) == 0:
                return ("skipline",)
            if re.fullmatch(r"\d+", then):
                return ("goto", int(then))
            return self.exec_stmt(then, line, ctx)
        if kw == "FOR":
            m = re.match(r"([A-Za-z][A-Za-z0-9]*)\s*=(.*?)\bTO\b(.*?)(?:\bSTEP\b(.*))?$", rest, re.I)
            if not m: self.fail("syntax", line)
            k = varkey(m.group(1))
            self.put(k, self.evaluate(m.group(2), line), line)
            lim = self.evaluate(m.group(3), line)
            step = self.evaluate(m.group(4), line) if m.group(4) else 1
            old = v.last_key("for", k)
            if old is not None:
                w.refuse(old, "restarted")
            w.bind("for", k, (lim, step, ctx))
            return None
        if kw == "NEXT":
            names = [varkey(x) for x in re.split(r"[,\s]+", rest) if x] or [None]
            for k in names:
                fid = v.last("for") if k is None else v.last_key("for", k)
                if fid is None: self.fail("next", line)
                k = v.sphere(fid).key
                lim, step, back = v.payload(fid)
                val = self.get(k) + step
                self.put(k, val, line)
                if (val <= lim) if step >= 0 else (val >= lim):
                    return ("goback", back)
                w.pop(fid)
            return None
        if kw == "DIM":
            for m in re.finditer(r"([A-Za-z][A-Za-z0-9]*[$%]?)\s*\((\d+)\)", rest):
                w.bind("dim", varkey(m.group(1)), int(m.group(2)))
            return None
        if kw == "READ":
            for name in [x.strip() for x in rest.split(",")]:
                val = self.next_data(line)
                m = re.match(r"([A-Za-z][A-Za-z0-9]*[$%]?)\s*(\((.*?)\))?$", name)
                self.store(m, val, line)
            return None
        if kw == "RESTORE":
            p = v.last("dptr")
            if p is not None: w.refuse(p, "restore")
            return None
        if kw == "POKE":
            a, b = [self.evaluate(x, line) for x in rest.split(",", 1)]
            if not (0 <= b <= 255 and 0 <= a <= 65535): self.fail("qty", line)
            i = v.last_key("mem", int(a))
            if i is None: w.bind("mem", int(a), int(b))
            else: supersede(w, i, int(b), "poke")
            return None
        if kw == "INPUT":
            m = re.match(r'(?:"([^"]*)"\s*;)?\s*(.*)$', rest)
            self.emit((m.group(1) or "") + "? ")
            for name in [x.strip() for x in m.group(2).split(",")]:
                i = v.first("basic.in")
                if i is None: self.fail("input", line)
                raw = w.pop(i)
                key = varkey(name)
                self.put(key, raw if key.endswith("$") else (float(raw) if "." in raw else int(raw)), line)
            self.emit("\n")
            return None
        if kw == "ON":
            m = re.match(r"(.*?)\b(GOTO|GOSUB)\b(.*)$", rest, re.I)
            idx = int(self.evaluate(m.group(1), line))
            targets = [int(x) for x in m.group(3).split(",")]
            return (m.group(2).lower(), targets[idx - 1]) if 1 <= idx <= len(targets) else None
        if kw == "CLR":
            self.clear("CLR"); return None
        if kw == "NEW":
            for i in v.live("line"): w.refuse(i, "NEW")
            self.clear("NEW"); return None
        if kw == "RUN":
            return ("run",)
        if kw == "LIST":
            self.emit(self.listing() + ("\n" if self.numbers() else "")); return None
        if kw == "SAVE":
            self.save(rest, line); return None
        if kw == "LOAD":
            self.load(rest, line); return None
        self.fail("syntax", line)

    def clear(self, why):
        for tag in ("basic.var", "elem", "dim", "for", "gosub", "dptr"):
            for i in self.w.view.live(tag):
                self.w.refuse(i, why)

    def assign(self, m, line):
        self.store(m, self.evaluate(m.group(4), line), line)

    def store(self, m, val, line):
        name, sub = m.group(1), m.group(3)
        if sub is not None:
            key, i = self.elem(name, self.evaluate(sub, line), line)
            if key.endswith("$") != isinstance(val, str): self.fail("type", line)
            j = self.w.view.last_key("elem", (key, i))
            if j is None: self.w.bind("elem", (key, i), val)
            else: supersede(self.w, j, val)
        else:
            self.put(varkey(name), val, line)

    def next_data(self, line):
        v = self.w.view
        items = []
        for n in self.numbers():
            body = v.payload(v.last_key("line", n))
            for st in split_stmts(body):
                if st.upper().startswith("DATA"):
                    for x in re.findall(r'"[^"]*"|[^,]+', st[4:]):
                        x = x.strip()
                        items.append(x[1:-1] if x.startswith('"') else (float(x) if "." in x else int(x)) if re.fullmatch(r"-?\d+\.?\d*", x) else x)
        p = v.last("dptr")
        k = 0 if p is None else v.payload(p)
        if k >= len(items): self.fail("data", line)
        if p is None: self.w.bind("dptr", None, k + 1)
        else: supersede(self.w, p, k + 1, "advance")
        return items[k]

    def do_print(self, rest, line):
        out, i, nl = "", 0, True
        parts = re.findall(r'"[^"]*"?|[^;,"]+|[;,]', rest)
        for part in parts:
            if part == ";":
                nl = False
            elif part == ",":
                nl = False
                self.emit(" " * (10 - (self.col + len(out)) % 10) if False else "")
                out += " " * (10 - (len(out)) % 10)
            else:
                nl = True
                val = self.evaluate(part, line)
                out += val if isinstance(val, str) else fmt_num(val)
        self.emit(out + ("\n" if nl else ""))
        if nl:
            self.col = 0

    # disk
    def save(self, rest, line):
        m = re.match(r'"([^"]*)"\s*(?:,\s*(\d+))?', rest)
        name, dev = m.group(1), int(m.group(2) or 1)
        if dev != self.device: self.fail("device", line)
        replace = name.startswith("@0:")
        name = name[3:] if replace else name
        v = self.w.view
        text = tuple((n, v.payload(v.last_key("line", n))) for n in self.numbers())
        old = v.last_key("file", (dev, name))
        if old is not None:
            if not replace: self.fail("exists", line)
            supersede(self.w, old, text, "replaced")
        else:
            self.w.bind("file", (dev, name), text, tuple(v.last_key("line", n) for n in self.numbers()))

    def directory(self, dev):
        v = self.w.view
        names = sorted(v.sphere(i).key[1] for i in v.live("file") if v.sphere(i).key[0] == dev)
        return [(0, '"DISK" 00 2A')] + [(max(1, len(v.payload(v.last_key("file", (dev, n)))) // 2 + 1), '"%s" PRG' % n) for n in names]

    def load(self, rest, line):
        m = re.match(r'"([^"]*)"\s*(?:,\s*(\d+))?', rest)
        name, dev = m.group(1), int(m.group(2) or 1)
        if dev != self.device: self.fail("device", line)
        v = self.w.view
        for i in v.live("line"): self.w.refuse(i, "replaced by LOAD")
        self.clear("LOAD")
        if name == "$":
            for n, t in self.directory(dev): self.w.bind("line", n, t)
            return
        pat = name.replace("*", "")
        cands = sorted(v.sphere(i).key[1] for i in v.live("file") if v.sphere(i).key[0] == dev)
        hit = next((c for c in cands if (c == name if "*" not in name else c.startswith(pat))), None)
        if hit is None: self.fail("notfound", line)
        fid = v.last_key("file", (dev, hit))
        for n, t in v.payload(fid):
            self.w.bind("line", n, t, (fid,))

    # running
    def run_program(self):
        w, v = self.w, self.w.view
        self.clear("RUN")
        nums = self.numbers()
        prog = {n: split_stmts(v.payload(v.last_key("line", n))) for n in nums}
        pos = {n: i for i, n in enumerate(nums)}
        li, si, steps = 0, 0, 0

        def jump(frm, to):
            if to not in pos: self.fail("undef", frm)
            j = w.bind("jump", None, (frm, to))
            w.pop(j)
            return pos[to], 0

        while li < len(nums):
            n = nums[li]
            if si >= len(prog[n]):
                li, si = li + 1, 0
                continue
            steps += 1
            if steps > self.max_steps: self.fail("break", n)
            sig = self.exec_stmt(prog[n][si], n, (li, si + 1))
            if sig is None:
                si += 1
            elif sig[0] == "goto":
                li, si = jump(n, sig[1])
            elif sig[0] == "gosub":
                w.bind("gosub", None, (li, si + 1))
                li, si = jump(n, sig[1])
            elif sig[0] == "return":
                g = v.last("gosub")
                if g is None: self.fail("return", n)
                li, si = w.pop(g)
            elif sig[0] == "goback":
                li, si = sig[1]
            elif sig[0] == "skipline":
                li, si = li + 1, 0
            elif sig[0] in ("end", "break"):
                if sig[0] == "break": self.emit("\nBREAK IN %d\n" % n)
                break
        w.collapse(lambda vw: tuple(sorted((vw.sphere(i).key, vw.payload(i)) for i in vw.live("basic.var"))), "variables")
