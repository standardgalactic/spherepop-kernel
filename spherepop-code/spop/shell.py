"""Shells as loading languages: resolve a name against ordered scopes, load the
image, bind argv. Dialects differ in the resolution rule, not in the machinery."""
import posixpath
import re
import shlex
from .kernel import World, supersede
from .loading import search

PATHEXT = [".COM", ".EXE", ".BAT", ".CMD"]
WIN_PATH = "C:\\Windows\\System32;C:\\Windows"
LINUX_PATH = "/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin"


def norm(ns, p):
    if ns == "win":
        p = p.replace("/", "\\").lower()
        return p if re.fullmatch(r"[a-z]:\\?", p) else p.rstrip("\\")
    return posixpath.normpath(p)


class Machine:
    """One world holding a Windows namespace and a Linux namespace."""

    def __init__(self, world=None):
        self.w = world or World()

    def mk(self, ns, path, payload):
        key = (ns, norm(ns, path))
        i = self.w.view.last_key("fs", key)
        if i is None:
            return self.w.bind("fs", key, payload)
        return supersede(self.w, i, payload, "overwritten")

    def get(self, ns, path):
        if ns == "linux" and (path == "/mnt/c" or path.startswith("/mnt/c/")):
            p = "c:\\" + path[7:].replace("/", "\\")
            pl = self.get("win", p)
            return pl
        i = self.w.view.last_key("fs", (ns, norm(ns, path)))
        return None if i is None else self.w.view.payload(i)

    def resolve_link(self, ns, path):
        for _ in range(8):
            pl = self.get(ns, path)
            if pl and pl[0] == "link":
                path = pl[1]
            else:
                return path, pl
        return path, None

    def listdir(self, ns, d):
        v, out = self.w.view, []
        d = norm(ns, d)
        for i in v.live("fs"):
            k = v.sphere(i).key
            if k[0] != ns:
                continue
            parent = k[1].rsplit("\\", 1)[0] if ns == "win" else posixpath.dirname(k[1])
            if parent == d or (ns == "win" and parent + "\\" == d):
                out.append(k[1].rsplit("\\", 1)[-1] if ns == "win" else posixpath.basename(k[1]))
        return sorted(out)


# programs (executable images)
def p_hello(sh, argv):
    return 0, "Hello from %s\n" % argv[0]


def a_ls(sh, argv):
    return 0, "".join(n + "\n" for n in sh.m.listdir(sh.ns, sh.cwd()))


def a_cat(sh, argv):
    out = ""
    for f in argv[1:]:
        pl = sh.m.get(sh.ns, sh.abspath(f))
        if not pl or pl[0] != "data":
            return 1, "cat: %s: No such file or directory\n" % f
        out += pl[1]
    return 0, out


def a_echo(sh, argv):
    return 0, " ".join(argv[1:]) + "\n"


def a_uname(sh, argv):
    return 0, "Linux\n"


APPLETS = {"ls": a_ls, "cat": a_cat, "echo": a_echo, "uname": a_uname,
           "true": lambda sh, a: (0, ""), "false": lambda sh, a: (1, "")}


def p_busybox(sh, argv):
    base = posixpath.basename(argv[0])
    if base == "busybox":
        if len(argv) == 1 or argv[1] == "--list":
            return 0, "".join(n + "\n" for n in sorted(APPLETS))
        argv = argv[1:]
        base = argv[0]
    if base not in APPLETS:
        return 127, "%s: applet not found\n" % base
    return APPLETS[base](sh, argv)


def p_which(sh, argv):
    out, st = "", 1
    for n in argv[1:]:
        r = sh.find_in_path(n)
        if r:
            out += r[0] + "\n"; st = 0
    return st, out


def p_where(sh, argv):
    out = ""
    for n in argv[1:]:
        for d in [sh.cwd()] + sh.pathlist():
            for e in ([""] if "." in n else []) + PATHEXT:
                cand = d.rstrip("\\") + "\\" + n + e.lower()
                pl = sh.m.get("win", cand)
                if pl and pl[0] == "exe":
                    out += cand + "\n"
    return (0 if out else 1), out


def p_notepad(sh, argv):
    return 0, "[notepad %s]\n" % " ".join(argv[1:])


PROG = {"hello": p_hello, "ls": a_ls, "cat": a_cat, "busybox": p_busybox, "which": p_which,
        "where": p_where, "notepad": p_notepad}


class Shell:
    def __init__(self, machine, dialect="bash", env=None, cwd=None, hook=None):
        self.m, self.w, self.dialect, self.hook = machine, machine.w, dialect, hook
        self.ns = "win" if dialect == "cmd" else "linux"
        self.id = self.w.bind("shell", None, dialect)
        defaults = {"PATH": WIN_PATH if dialect == "cmd" else LINUX_PATH}
        defaults.update(env or {})
        for k, v in defaults.items():
            self.w.bind("envvar", (self.id, k), v)
        self.w.bind("cwd", self.id, cwd or ("C:\\Users\\me" if dialect == "cmd" else "/home/me"))
        self.w.bind("status", self.id, 0)

    # state
    def getenv(self, k):
        i = self.w.view.last_key("envvar", (self.id, k if self.dialect == "bash" else k.upper()))
        if i is None and self.dialect == "cmd":
            i = next((j for j in self.w.view.live("envvar") if self.w.view.sphere(j).key[0] == self.id
                      and self.w.view.sphere(j).key[1].upper() == k.upper()), None)
        return "" if i is None else self.w.view.payload(i)

    def setenv(self, k, val):
        key = (self.id, k if self.dialect == "bash" else k.upper())
        i = self.w.view.last_key("envvar", key)
        if i is None:
            self.w.bind("envvar", key, val)
        else:
            supersede(self.w, i, val, "reassigned")
        if k.upper() == "PATH":
            for h in self.w.view.live("hash"):
                if self.w.view.sphere(h).key[0] == self.id:
                    self.w.refuse(h, "path-changed")

    def cwd(self):
        return self.w.view.payload(self.w.view.last_key("cwd", self.id))

    def abspath(self, p):
        if self.ns == "win":
            return p if re.match(r"[A-Za-z]:", p) else self.cwd().rstrip("\\") + "\\" + p
        return p if p.startswith("/") else posixpath.join(self.cwd(), p)

    def pathlist(self):
        sep = ";" if self.dialect == "cmd" else ":"
        return [d for d in self.getenv("PATH").split(sep) if d]

    def status(self):
        return self.w.view.payload(self.w.view.last_key("status", self.id))

    def set_status(self, n):
        i = self.w.view.last_key("status", self.id)
        supersede(self.w, i, n, "exit")

    def emit(self, text):
        if text:
            self.w.bind("shell.out", self.id, text)

    def output(self):
        v = self.w.view
        return "".join(v.payload(i) for i in v.live("shell.out") if v.sphere(i).key == self.id)

    # resolution
    def probe_linux(self, d, name):
        cand = posixpath.join(d, name)
        path, pl = self.m.resolve_link("linux", cand)
        if pl is None or pl[0] == "dir":
            return "missing", None
        if pl[0] == "exe" and pl[2]:
            return "hit", (cand, pl)
        return "skip:not-executable", (cand, pl)

    def probe_win(self, scope, name):
        d, e = scope
        cand = d.rstrip("\\") + "\\" + name + e
        pl = self.m.get("win", cand)
        if pl and pl[0] == "exe":
            return "hit", (cand, pl)
        return "missing", None

    def find_in_path(self, name):
        hit, _ = search(self.w, name, self.pathlist(), self.probe_linux)
        return hit

    def resolve(self, name):
        """Return (kind, detail). Kinds follow the dialect's rule order."""
        v = self.w.view
        if self.dialect == "cmd":
            if name.lower() in CMD_BUILTINS:
                return "builtin", name.lower()
            exts = [""] if os_ext(name) else PATHEXT
            if "\\" in name:
                scopes = [(name.rsplit("\\", 1)[0], e) for e in exts]
                name = name.rsplit("\\", 1)[1]
            else:
                scopes = [(d, e) for d in [self.cwd()] + self.pathlist() for e in exts]
            hit, _ = search(self.w, name, scopes, self.probe_win)
            return ("path", hit) if hit else ("missing", None)
        a = v.last_key("alias", (self.id, name))
        if a is not None:
            return "alias", v.payload(a)
        if name in BASH_BUILTINS:
            return "builtin", name
        if "/" in name:
            d, n = posixpath.split(self.abspath(name))
            out, hit = self.probe_linux(d, n)
            if out == "hit":
                return "path", hit
            return ("noexec", hit) if out.startswith("skip") else ("missing", None)
        h = v.last_key("hash", (self.id, name))
        if h is not None:
            return "hashed", v.payload(h)
        hit, tried = search(self.w, name, self.pathlist(), self.probe_linux)
        if hit:
            self.w.bind("hash", (self.id, name), hit[0])
            return "path", hit
        if any(o.startswith("skip") for _, o in tried):
            return "noexec", None
        return "missing", None

    # running
    def run(self, line):
        status = 0
        for seg, op in self.split(line):
            if op == "&&" and status != 0:
                continue
            if op == "||" and status == 0:
                continue
            status = self.simple(seg)
            self.set_status(status)
        return status

    def split(self, line):
        out, cur, q, i, op = [], "", None, 0, ";"
        while i < len(line):
            ch = line[i]
            if q:
                q = None if ch == q else q
                cur += ch
            elif ch in "'\"":
                q = ch; cur += ch
            elif ch == ";" or line[i:i + 2] in ("&&", "||"):
                out.append((cur, op)); op = ch if ch == ";" else line[i:i + 2]
                cur = ""; i += 0 if ch == ";" else 1
            else:
                cur += ch
            i += 1
        out.append((cur, op))
        return [(s.strip(), o) for s, o in out if s.strip()]

    def expand(self, s):
        if self.dialect == "cmd":
            return re.sub(r"%(\w+)%", lambda m: str(self.status()) if m.group(1).upper() == "ERRORLEVEL" else self.getenv(m.group(1)), s)
        return re.sub(r"\$\{?(\w+|\?)\}?", lambda m: str(self.status()) if m.group(1) == "?" else self.getenv(m.group(1)), s)

    def simple(self, seg):
        seg = self.expand(seg)
        toks = shlex.split(seg, posix=(self.dialect == "bash"))
        redirect = None
        if ">" in toks:
            k = toks.index(">")
            redirect, toks = toks[k + 1], toks[:k]
        if not toks:
            return 0
        if self.dialect == "bash" and re.fullmatch(r"\w+=.*", toks[0]) and len(toks) == 1:
            k, val = toks[0].split("=", 1)
            self.setenv(k, val)
            return 0
        status, text = self.dispatch(toks)
        if redirect:
            self.m.mk(self.ns, self.abspath(redirect), ("data", text))
        else:
            self.emit(text)
        return status

    def dispatch(self, toks):
        name = toks[0]
        kind, detail = self.resolve(name)
        if kind == "alias":
            return self.dispatch(shlex.split(detail) + toks[1:])
        if kind == "builtin":
            return (CMD_BUILTINS if self.dialect == "cmd" else BASH_BUILTINS)[detail](self, toks)
        if kind in ("path", "hashed"):
            pl = detail[1] if kind == "path" else self.m.resolve_link("linux", detail)[1]
            return PROG[pl[1]](self, [name] + toks[1:])
        if kind == "noexec":
            return 126, "bash: %s: Permission denied\n" % name
        if self.dialect == "cmd":
            return 9009, "'%s' is not recognized as an internal or external command,\noperable program or batch file.\n" % name
        if self.hook:
            msg = self.hook(name)
            if msg:
                return 127, msg
        return 127, "bash: %s: command not found\n" % name


def os_ext(name):
    return "." + name.rsplit(".", 1)[-1].upper() in PATHEXT if "." in name else False


def b_echo(sh, t):
    return 0, " ".join(t[1:]) + "\n"


def b_cd(sh, t):
    target = sh.abspath(t[1]) if len(t) > 1 else sh.cwd()
    pl = sh.m.get(sh.ns, target)
    if not pl or pl[0] != "dir":
        return 1, "%s: cd: %s: No such file or directory\n" % ("bash" if sh.dialect == "bash" else "cmd", t[1])
    supersede(sh.w, sh.w.view.last_key("cwd", sh.id), target, "cd")
    return 0, ""


def b_export(sh, t):
    for a in t[1:]:
        k, _, val = a.partition("=")
        sh.setenv(k, val)
    return 0, ""


def b_alias(sh, t):
    for a in t[1:]:
        k, _, val = a.partition("=")
        i = sh.w.view.last_key("alias", (sh.id, k))
        if i is None:
            sh.w.bind("alias", (sh.id, k), val)
        else:
            supersede(sh.w, i, val, "redefined")
    return 0, ""


def b_type(sh, t):
    out, st = "", 0
    for n in t[1:]:
        kind, d = sh.resolve(n)
        if kind == "alias": out += "%s is aliased to `%s'\n" % (n, d)
        elif kind == "builtin": out += "%s is a shell builtin\n" % n
        elif kind == "hashed": out += "%s is hashed (%s)\n" % (n, d)
        elif kind == "path": out += "%s is %s\n" % (n, d[0])
        else: out += "bash: type: %s: not found\n" % n; st = 1
    return st, out


def c_set(sh, t):
    if len(t) == 1:
        v = sh.w.view
        return 0, "".join("%s=%s\n" % (v.sphere(i).key[1], v.payload(i)) for i in v.live("envvar") if v.sphere(i).key[0] == sh.id)
    k, _, val = " ".join(t[1:]).partition("=")
    sh.setenv(k, val)
    return 0, ""


def c_dir(sh, t):
    return 0, "".join(n + "\n" for n in sh.m.listdir("win", sh.cwd()))


def c_type(sh, t):
    pl = sh.m.get("win", sh.abspath(t[1]))
    return (0, pl[1]) if pl and pl[0] == "data" else (1, "The system cannot find the file specified.\n")


BASH_BUILTINS = {"echo": b_echo, "cd": b_cd, "export": b_export, "alias": b_alias, "type": b_type,
                 "true": lambda s, t: (0, ""), "false": lambda s, t: (1, ""),
                 "pwd": lambda s, t: (0, s.cwd() + "\n")}
CMD_BUILTINS = {"echo": b_echo, "set": c_set, "cd": b_cd, "dir": c_dir, "type": c_type}


# canned machines
def mkdirs(m, ns, *paths):
    for p in paths:
        m.mk(ns, p, ("dir",))


def windows_machine(m=None):
    m = m or Machine()
    mkdirs(m, "win", "C:\\", "C:\\Windows", "C:\\Windows\\System32", "C:\\Users", "C:\\Users\\me", "C:\\Users\\me\\tools")
    m.mk("win", "C:\\Windows\\System32\\notepad.exe", ("exe", "notepad", True))
    m.mk("win", "C:\\Windows\\System32\\where.exe", ("exe", "where", True))
    m.mk("win", "C:\\Windows\\System32\\cmd.exe", ("exe", "hello", True))
    return m


def ubuntu_machine(m=None):
    m = m or Machine()
    mkdirs(m, "linux", "/", "/bin", "/usr", "/usr/bin", "/usr/local", "/usr/local/bin", "/home", "/home/me", "/mnt", "/mnt/c")
    for n in ("ls", "cat"):
        m.mk("linux", "/bin/" + n, ("exe", n, True))
    m.mk("linux", "/usr/bin/which", ("exe", "which", True))
    return m


def busybox_machine(m=None):
    m = m or Machine()
    mkdirs(m, "linux", "/", "/bin", "/home", "/home/me")
    m.mk("linux", "/bin/busybox", ("exe", "busybox", True))
    for n in APPLETS:
        m.mk("linux", "/bin/" + n, ("link", "/bin/busybox"))
    return m
