"""Produce the transcripts and tables that the book includes. ASCII only."""
import itertools, os, sys
sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))
from spop.kernel import World
from spop.forth import Forth
from spop.regs import ShiftRegister, TransferRegister, ControlError, RippleRegister
from spop.lisp import Lisp, fmt, show
from spop.racket import Racket
from spop.basic import Basic, BasicError
from spop.shell import *
from spop.index import Index, ResolutionError, SearchPath

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "..", "out")
RKT = os.path.join(HERE, "..", "rkt")
os.makedirs(OUT, exist_ok=True)


def write(name, text):
    with open(os.path.join(OUT, name), "w") as f:
        f.write(text)


def live(w):
    return sum(len(d) for d in w._tag.values())


# registers
rows = []
for q in itertools.product((0, 1), repeat=4):
    cells = []
    for b in (0, 1):
        r = ShiftRegister(q).edge(b)
        cells += ["".join(map(str, r.word())), str(r.shifted_out())]
    rows.append("%s & %s & %s & %s & %s \\\\" % ("".join(map(str, q)), *cells))
write("regtable.tex", "\\begin{tabular}{ccccc}\n\\toprule\nInitial word & Next, input $0$ & Out & Next, input $1$ & Out\\\\\n\\midrule\n" + "\n".join(rows) + "\n\\bottomrule\n\\end{tabular}\n")

r = ShiftRegister((1, 0, 1, 1))
t = ["start  %s" % "".join(map(str, r.word()))]
for b in (0, 0, 1):
    r.edge(b)
    t.append("edge %d %s  out %d" % (b, "".join(map(str, r.word())), r.shifted_out()))
bad = RippleRegister((1, 0, 0, 0)).edge(0)
t.append("ripple fault on 1000 with 0: %s (expected 0100)" % "".join(map(str, bad.word())))
tr = TransferRegister(3)
t.append("transfer: select 1 of [5,9,12] -> %d" % tr.clock([5, 9, 12], [0, 1, 0]))
t.append("transfer: no select holds -> %d" % tr.clock([5, 9, 12], [0, 0, 0]))
try:
    tr.clock([5, 9, 12], [1, 1, 0])
except ControlError as e:
    t.append("transfer: %s" % e)
t.append("ledger events: %s" % dict(sorted(r.w.counts().items())))
write("regs.txt", "\n".join(t) + "\n")

# forth
f = Forth()
t = []
def fo(src):
    f.run(src); t.append("ok> %s\n    stack %s" % (src, f.stack()))
fo("2 3 +")
t.append("    explain: %s" % f.explain_top())
fo("drop 3 dup *")
t.append("    explain: %s" % f.explain_top())
fo("drop : sq dup * ; 7 sq")
fo("drop : cube dup sq * ; 3 cube")
fo(": sq drop 0 ; 3 cube")
g = Forth(early_binding=False); g.run(": sq dup * ; : cube dup sq * ;"); g.run("3 cube"); a = g.stack(); g.run(": sq drop 0 ;"); g.run("drop 3 cube")
t.append("    with late binding the same cube now yields %s" % g.stack())
fo(": fact dup 1 > if dup 1- recurse * then ; drop drop 10 fact")
f.run('." result " . cr'); t.append("    output %r" % f.output())
try:
    f.run("+ + +")
except Exception as e:
    t.append("ok> + + +\n    refused: %s ; stack after abort %s" % (e, f.stack()))
write("forth.txt", "\n".join(t) + "\n")

# lisp
L = Lisp()
t = []
for form in ["(define (make-counter) (let ((n 0)) (lambda () (set! n (+ n 1)) n)))", "(define c (make-counter))",
             "(c)", "(c)", "(c)", "(map (lambda (x) (* x x)) '(1 2 3 4))"]:
    v = L.run(form); t.append("> %s\n%s" % (form, "" if v is None else show(v)))
cl = L.lookup(L.top, "c"); env = L.w.spheres[cl.id].deps[0]
t.append("lineage of n in the captured frame: %s" % (L.lineage(env, "n"),))
L.run("(define (loop n acc) (if (= n 0) acc (loop (- n 1) (+ acc 1))))")
t.append("(loop 3000 0) = %s ; live call spheres afterward: %d" % (L.run("(loop 3000 0)"), L.w.view.count("call")))
write("lisp.txt", "\n".join(t) + "\n")

# racket
R = Racket(); R.load_dir(RKT)
t = []
def rk(form):
    try:
        v = R.run(form)
        t.append("> %s\n%s" % (form, "" if v is None else show(v)))
    except Exception as e:
        t.append("> %s\nerror: %s" % (form, e))
rk("(require units)"); rk("(c->f 100)"); rk("(internal-helper 2)")
rk("(require (prefix-in u: units))"); rk("(u:km->miles 1000000)")
rk("(require game)"); rk("(score 60 30 20)"); rk("(+ 60 30 20)")
rk("(require traffic)"); rk("(run 'green '(timer timer))"); rk("(light 'red 'fault)")
rk("(define c->f 1)"); rk("(require no-such)")
t.append("where c->f: %s ; where score: %s ; where map: %s" % (R.where("c->f"), R.where("score"), R.where("map")))
t.append("imports of traffic: %s" % (R.imports_of("traffic"),))
t.append("imports of game: %s" % (R.imports_of("game"),))
t.append("modules instantiated: %s" % (R.module_names(),))
write("racket.txt", "\n".join(t) + "\n")

# basic
B = Basic(inputs=[])
t = []
for line in ['10 REM SUM OF SQUARES', '20 FOR I=1 TO 5', '30 S=S+I*I', '40 NEXT I', '50 PRINT "SUM ="; S', '60 GOSUB 100', '70 END',
             '100 PRINT "DONE"', '110 RETURN']:
    B.enter(line)
t.append("LIST\n" + B.listing())
B.enter("RUN"); t.append("RUN\n" + B.output().rstrip("\n"))
B.enter('SAVE "SUMSQ",8'); B.enter("NEW"); B.enter('LOAD "$",8')
t.append("LOAD \"$\",8 then LIST\n" + B.listing())
B.enter('LOAD "SU*",8'); t.append('LOAD "SU*",8 then LIST (first line)\n' + B.listing().split("\n")[0])
B.enter("30 S=S+I"); B.enter("RUN")
t.append("after editing line 30 to S=S+I and RUN\n" + [l for l in B.output().split("\n") if l.startswith("SUM")][-1].rstrip())
for cmd in ['LOAD "NOPE",8', 'LOAD "SUMSQ"']:
    try:
        B.enter(cmd)
    except BasicError as e:
        t.append("%s\n%s" % (cmd, e))
t.append("COUNT and COUNTER share a variable: ")
B2 = Basic(); B2.enter("10 COUNT=5"); B2.enter("20 COUNTER=9"); B2.enter("30 PRINT COUNT"); B2.enter("RUN")
t[-1] += B2.output().strip()
write("basic.txt", "\n".join(t) + "\n")

# shells
def probes(m, start=0):
    v = m.w
    return [("%s%s" % (v.spheres[i].payload[0] if isinstance(v.spheres[i].payload[0], str) else "%s+%s" % v.spheres[i].payload[0],
                       "" if True else ""), v.status[i]) for i in range(start, len(v.spheres)) if v.spheres[i].tag == "probe"]

t = []
m = windows_machine(); ubuntu_machine(m)
m.mk("linux", "/usr/local/bin/hello", ("exe", "hello", True))
m.mk("win", "C:\\Users\\me\\hello.bat", ("exe", "hello", True))
m.mk("win", "C:\\Windows\\System32\\hello.exe", ("exe", "hello", True))
def trace(label, sh, cmd):
    n = len(m.w.spheres)
    st = sh.run(cmd)
    t.append("%s> %s   (status %d)" % (label, cmd, st))
    for i in range(n, len(m.w.spheres)):
        s = m.w.spheres[i]
        if s.tag == "probe":
            sc, nm = s.payload[0], s.payload[1]
            path = (sc[0].rstrip("\\") + "\\" + nm + sc[1]) if isinstance(sc, tuple) else sc.rstrip("/") + "/" + nm
            t.append("    probe %-40s %s" % (path, "HIT" if m.w.status[i] == "popped" else "miss"))
bash = Shell(m, "bash"); cmd = Shell(m, "cmd")
trace("bash", bash, "ls")
trace("bash", bash, "ls")
trace("bash", bash, "hello")
trace("bash", bash, "export PATH=/bin:/usr/local/bin")
trace("bash", bash, "hello")
trace("cmd ", cmd, "hello")
trace("cmd ", cmd, "nosuch")
wsl = Shell(m, "bash", env={"PATH": LINUX_PATH + ":/mnt/c/Windows/System32"})
trace("wsl ", wsl, "notepad.exe")
trace("wsl ", wsl, "notepad")
t.append("")
bash.run("export PATH=" + LINUX_PATH)
chunks = []
for c in ("type cd", "alias ll='ls'", "type ll", "which cd"):
    n = len(bash.output()); st = bash.run(c)
    chunks.append("    %s   (status %d)  %s" % (c, st, bash.output()[n:].strip()))
t.append("type and which on bash:\n" + "\n".join(chunks))
mb = busybox_machine(); sb = Shell(mb, "bash", env={"PATH": "/bin"})
sb.run("busybox --list"); sb.run("uname"); sb.run("busybox uname")
t.append("busybox: applets %s ; links resolving to /bin/busybox: %d of %d" % (
    " ".join(sb.output().split("\n")[:6]), sum(1 for n in APPLETS if mb.resolve_link("linux", "/bin/" + n)[0] == "/bin/busybox"), len(APPLETS)))
write("shell.txt", "\n".join(t) + "\n")

# index
t = []
ix = Index()
for v in ("1.0.0", "1.5.0", "2.0.0"): ix.publish("C", v)
ix.publish("A", "1.0.0", {"C": "^1.0"}); ix.publish("A", "2.0.0", {"C": "^2.0"}); ix.publish("B", "1.0.0", {"C": "^1.0"})
t.append("flat   install A *, B *            -> %s   (decisions backtracked: %d)" % (ix.install({"A": "*", "B": "*"}), list(ix.w.reasons.values()).count("backtrack")))
ix2 = Index()
for v in ("1.0.0", "1.5.0", "2.0.0"): ix2.publish("C", v)
ix2.publish("A", "1.0.0", {"C": "^1.0"}); ix2.publish("A", "2.0.0", {"C": "^2.0"}); ix2.publish("B", "1.0.0", {"C": "^1.0"})
try:
    ix2.install({"A": "==2.0.0", "B": "*"})
except ResolutionError as e:
    t.append("flat   install A ==2.0.0, B *     -> refused: %s" % e)
out = ix2.solve_nested({"A": "==2.0.0", "B": "*"})
t.append("nested install A ==2.0.0, B *     -> " + "; ".join("%s%s=%s" % ("/".join(p) + ":" if p else "", n, v) for (p, n), v in sorted(out.items())))
t.append("nested lookup of C from A@2.0.0: %s ; from B@1.0.0: %s" % (ix2.node_lookup(("A@2.0.0",), "C"), ix2.node_lookup(("B@1.0.0",), "C")))
try:
    ix.uninstall("C")
except ResolutionError as e:
    t.append("uninstall C -> refused: %s" % e)
w = World(); sp = SearchPath(w, ["user", "install", "main"])
sp.contents = {"user": {"fsm"}, "install": {"fsm", "units"}, "main": {"base"}}
t.append("search path user,install,main: fsm found in %s ; units in %s" % (sp.find("fsm"), sp.find("units")))
sp.set(["install", "user", "main"])
t.append("after reassigning the path: fsm found in %s" % sp.find("fsm"))
write("index.txt", "\n".join(t) + "\n")

# structural profile
def prof(name, w):
    c = w.counts()
    return "%s & %d & %d & %d & %d & %d & %d \\\\" % (name, c["bind"], c["pop"], c["refuse"], c["collapse"], len(w.ledger), live(w))

rows = []
f = Forth(); f.run(": fact dup 1 > if dup 1- recurse * then ; 10 fact .")
rows.append(prof("Forth, factorial of 10", f.w))
r = ShiftRegister((1, 0, 1, 1))
for b in (0, 0, 1, 1, 0, 1, 0, 0): r.edge(b)
rows.append(prof("Shift register, 8 edges", r.w))
L = Lisp(); base = len(L.w.ledger)
L.run("(define (fib n) (if (< n 2) n (+ (fib (- n 1)) (fib (- n 2))))) (fib 12)")
rows.append(prof("Lisp, fib 12 (with prelude)", L.w))
B = Basic()
for line in ["10 FOR I=1 TO 100", "20 S=S+I", "30 NEXT I", "40 PRINT S"]: B.enter(line)
B.enter("RUN")
rows.append(prof("BASIC, sum 1 to 100", B.w))
m = ubuntu_machine(); sh = Shell(m, "bash"); sh.run("ls; ls; type cd; nope")
rows.append(prof("bash, four commands", m.w))
ix = Index()
for v in ("1.0.0", "1.5.0", "2.0.0"): ix.publish("C", v)
ix.publish("A", "1.0.0", {"C": "^1.0"}); ix.publish("A", "2.0.0", {"C": "^2.0"}); ix.publish("B", "1.0.0", {"C": "^1.0"})
ix.install({"A": "*", "B": "*"})
rows.append(prof("Index, diamond install", ix.w))
write("profile.tex", "\\begin{tabular}{lrrrrrr}\n\\toprule\nWorkload & Bind & Pop & Refuse & Collapse & Events & Live\\\\\n\\midrule\n" + "\n".join(rows) + "\n\\bottomrule\n\\end{tabular}\n")
print("transcripts written to", os.path.abspath(OUT))
