"""Package indexes as spheres: releases, decisions, installs, search paths.

Two resolution policies share one release store. The flat policy installs a
single version per name and backtracks over decisions. The nested policy
installs per dependent and resolves a name by walking outward, which is the
same shape as lexical scope lookup.
"""
from .kernel import World, supersede, attempt_refused
from .loading import search


class ResolutionError(Exception):
    pass


def pv(s):
    p = [int(x) for x in str(s).split(".")]
    return tuple(p + [0] * (3 - len(p)))


def satisfies(ver, spec):
    v = pv(ver)
    for c in [c.strip() for c in spec.split(",") if c.strip()]:
        if c == "*":
            continue
        if c[0] == "^":
            b = pv(c[1:])
            hi = (b[0] + 1, 0, 0) if b[0] > 0 else ((0, b[1] + 1, 0) if b[1] > 0 else (0, 0, b[2] + 1))
            ok = b <= v < hi
        elif c[0] == "~":
            b = pv(c[1:])
            ok = b <= v < (b[0], b[1] + 1, 0)
        else:
            for op in ("==", "!=", ">=", "<=", ">", "<"):
                if c.startswith(op):
                    b = pv(c[len(op):])
                    ok = {"==": v == b, "!=": v != b, ">=": v >= b, "<=": v <= b, ">": v > b, "<": v < b}[op]
                    break
            else:
                raise ValueError("bad specifier %r" % c)
        if not ok:
            return False
    return True


class Index:
    def __init__(self, world=None):
        self.w = world or World()

    def publish(self, name, version, deps=None, provides=(), modules=None):
        pl = (tuple(sorted((deps or {}).items())), tuple(provides), tuple(sorted((modules or {}).items())))
        return self.w.bind("release", (name, version), pl)

    def yank(self, name, version):
        self.w.refuse(self.w.view.last_key("release", (name, version)), "yanked")

    def releases(self, name):
        v = self.w.view
        vs = [v.sphere(i).key[1] for i in v.live("release") if v.sphere(i).key[0] == name]
        return sorted(vs, key=pv, reverse=True)

    def release(self, name, ver):
        return self.w.view.payload(self.w.view.last_key("release", (name, ver)))

    # flat policy
    def solve_flat(self, reqs, pinned=None):
        w = self.w
        pinned = pinned or {}
        decided = []

        def rec(todo, chosen, cons, parent):
            if not todo:
                return chosen
            name = todo[0]
            for ver in self.releases(name):
                if not all(satisfies(ver, s) for s, _ in cons[name]):
                    continue
                deps = dict(self.release(name, ver)[0])
                ncons = {k: list(x) for k, x in cons.items()}
                bad = False
                for dn, ds in deps.items():
                    ncons.setdefault(dn, []).append((ds, name))
                    if dn in chosen and not satisfies(chosen[dn], ds):
                        bad = True
                if bad:
                    continue
                d = w.bind("decision", name, ver, tuple(parent.get(r) for r in [name] if parent.get(r) is not None))
                decided.append(d)
                nxt = todo[1:] + [dn for dn in deps if dn not in chosen and dn not in todo and dn != name]
                res = rec(nxt, {**chosen, name: ver}, ncons, {**parent, **{dn: d for dn in deps}})
                if res is not None:
                    return res
                w.refuse(d, "backtrack")
            return None

        cons = {n: [(s, "root")] for n, s in reqs.items()}
        for n, v in pinned.items():
            cons.setdefault(n, []).append(("==" + v, "installed"))
        res = rec(list(cons), {}, cons, {})
        if res is None:
            attempt_refused(w, "attempt", tuple(sorted(reqs.items())), "unsatisfiable")
            raise ResolutionError("no consistent set of versions for %r" % (reqs,))
        return res

    def installed(self):
        v = self.w.view
        return {v.sphere(i).key: v.payload(i) for i in v.live("installed")}

    def install(self, reqs, upgrade=False):
        pinned = {} if upgrade else dict(self.installed())
        pinned = {k: x for k, x in pinned.items() if k not in reqs} if not upgrade else pinned
        chosen = self.solve_flat(reqs, pinned)
        w, v = self.w, self.w.view
        done = {}

        def make(name):
            if name in done:
                return done[name]
            ver = chosen[name]
            deps = [make(d) for d, _ in self.release(name, ver)[0] if d in chosen]
            cur = v.last_key("installed", name)
            if cur is not None and v.payload(cur) == ver:
                done[name] = cur
            elif cur is not None:
                done[name] = supersede(w, cur, ver, "upgraded")
                w.bind("link", name, None, (done[name],) + tuple(deps))
            else:
                done[name] = w.bind("installed", name, ver, tuple(deps))
            return done[name]

        for n in chosen:
            make(n)
        return chosen

    def uninstall(self, name):
        v, w = self.w.view, self.w
        i = v.last_key("installed", name)
        if i is None:
            attempt_refused(w, "attempt", name, "not-installed")
            raise ResolutionError("%s is not installed" % name)
        users = [v.sphere(j).key for j in v.live("installed") if i in v.sphere(j).deps]
        if users:
            attempt_refused(w, "attempt", name, "required-by")
            raise ResolutionError("%s is required by %s" % (name, ", ".join(sorted(users))))
        w.refuse(i, "removed")

    def lock(self):
        return tuple(sorted(self.installed().items()))

    def why(self, name):
        v = self.w.view
        i = v.last_key("installed", name)
        return sorted(v.sphere(j).key for j in v.live("installed") if i in v.sphere(j).deps)

    # nested policy
    def solve_nested(self, reqs, path=()):
        w, out = self.w, {}
        for name, spec in reqs.items():
            ver = next((x for x in self.releases(name) if satisfies(x, spec)), None)
            if ver is None:
                attempt_refused(w, "attempt", (name, spec), "unsatisfiable")
                raise ResolutionError("no version of %s satisfies %s" % (name, spec))
            w.bind("nested", (path, name), ver)
            out[(path, name)] = ver
            tag = "%s@%s" % (name, ver)
            if tag not in path:
                out.update(self.solve_nested(dict(self.release(name, ver)[0]), path + (tag,)))
        return out

    def node_lookup(self, frm, name):
        v = self.w.view
        for k in range(len(frm), -1, -1):
            i = v.last_key("nested", (frm[:k], name))
            if i is not None:
                return v.payload(i)
        return None

    # command-not-found and module-provider queries
    def provider_of_file(self, path):
        v = self.w.view
        for i in v.live("release"):
            if path in v.payload(i)[1]:
                return v.sphere(i).key[0]
        return None

    def hook(self):
        def h(name):
            for d in ("/usr/bin/", "/bin/", "/usr/local/bin/"):
                p = self.provider_of_file(d + name)
                if p:
                    return "Command '%s' not found, but can be installed with:\nsudo apt install %s\n" % (name, p)
            return None
        return h

    def provider_of_module(self, mod):
        v = self.w.view
        for i in v.live("release"):
            if any(m == mod for m, _ in v.payload(i)[2]):
                return v.sphere(i).key[0]
        return None

    def sync_racket(self, rkt):
        """Feed installed packages' modules into a Racket source index; retract removed ones."""
        v, w = self.w.view, self.w
        want = {}
        for name, ver in self.installed().items():
            for m, src in self.release(name, ver)[2]:
                want[m] = src
        for m, src in want.items():
            cur = rkt.w.view.last_key("source", m)
            if cur is None or rkt.w.view.payload(cur) != src:
                rkt.add_source(m, src)
            if rkt.w.view.last_key("owned", m) is None:
                rkt.w.bind("owned", m)
        for i in rkt.w.view.live("owned"):
            m = rkt.w.view.sphere(i).key
            if m not in want:
                s = rkt.w.view.last_key("source", m)
                if s is not None:
                    rkt.w.refuse(s, "package-removed")
                rkt.w.refuse(i, "package-removed")


class SearchPath:
    """An ordered list of scopes, reassigned by supersession like PATH."""

    def __init__(self, world, dirs):
        self.w = world
        self.p = world.bind("searchpath", None, tuple(dirs))
        self.contents = {}

    def set(self, dirs):
        self.p = supersede(self.w, self.p, tuple(dirs), "reassigned")

    def dirs(self):
        return self.w.view.payload(self.p)

    def find(self, name):
        def probe(d, n):
            return ("hit", d) if n in self.contents.get(d, ()) else ("missing", None)
        hit, _ = search(self.w, name, self.dirs(), probe)
        return hit
