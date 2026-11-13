"""A Racket-flavoured module layer on the Lisp of spop.lisp.

A module is a sphere whose environment is closed over its language's exports.
provide creates export spheres coupled to the bindings they expose, require
creates import spheres coupled to exports, and an unresolved module name is
looked up in a source index, which loads and instantiates it once.
"""
import os
from .lisp import Lisp, LispError, Sym, PRELUDE, show
from .kernel import supersede


class Racket(Lisp):
    def __init__(self, world=None, lang="base"):
        super().__init__(world, boot=False)
        self.forms.update({"module": self._module, "require": self._require, "provide": self._provide})
        self._provides = []
        benv = self.w.bind("env", None, None)
        self.install_builtins(benv)
        self.run(PRELUDE, env=benv)
        self._declare("base", benv, [("all-defined-out",)])
        self.lang = lang
        self.top = self.w.bind("env", None, None)
        self._import_lang(self.top, lang)

    # source index (the collects directory)
    def add_source(self, name, text):
        old = self.w.view.last_key("source", name)
        if old is not None:
            return supersede(self.w, old, text, "new-version")
        return self.w.bind("source", name, text)

    def load_dir(self, path):
        for f in sorted(os.listdir(path)):
            if f.endswith(".rkt"):
                with open(os.path.join(path, f)) as fh:
                    self.add_source(f[:-4], fh.read())

    def reload(self, name):
        """Redeclare a module from its current source; old importers keep old imports."""
        text = self.w.spheres[self.w.view.last_key("source", name)].payload
        self.run(text, env=self.top)

    # modules
    def _find(self, name):
        v = self.w.view
        m = v.last_key("module", name)
        if m is None:
            s = v.last_key("source", name)
            if s is None:
                self.err("cannot open module: %s" % name, "cannot-open-module")
            self.run(self.w.spheres[s].payload, env=self.top)
            m = v.last_key("module", name)
            if m is None:
                self.err("module %s was not declared by its source" % name, "bad-module-source")
        return m

    def _exports(self, name):
        self._find(name)
        v = self.w.view
        return {k[1]: i for i in v.live("export") if (k := v.sphere(i).key)[0] == name}

    def exports(self, name):
        return sorted(self._exports(name))

    def module_names(self):
        return sorted(self.w.view.sphere(i).key for i in self.w.view.live("module"))

    def _import_lang(self, env, lang):
        for n, e in self._exports(lang).items():
            self.w.bind("langimport", (env, n), self.w.spheres[e].payload, (e,))

    def _module(self, x, env):
        name, lang = str(x[1]), str(x[2])
        menv = self.w.bind("env", None, None)
        self._import_lang(menv, lang)
        self._provides.append([])
        try:
            for f in x[3:]:
                self.eval(f, menv)
            specs = list(self._provides[-1])
        finally:
            self._provides.pop()
        self._declare(name, menv, specs)
        return Sym(name)

    def _declare(self, name, menv, specs):
        w, v = self.w, self.w.view
        old = v.last_key("module", name)
        if old is not None:
            for i in [i for i in v.live("export") if v.sphere(i).key[0] == name]:
                w.refuse(i, "module-redeclared")
            w.refuse(old, "redeclared")
        src = v.last_key("source", name)
        w.bind("module", name, menv, (menv,) + ((src,) if src is not None else ()))
        done = set()

        def export(pub, dep, value):
            if pub in done:
                return
            done.add(pub)
            w.bind("export", (name, pub), value, (dep,))

        for spec in specs:
            if isinstance(spec, Sym):
                o = self.owner(menv, str(spec))
                if o is None:
                    self.err("provide: identifier not defined: %s" % spec, "provide-undefined")
                export(str(spec), o[2], w.spheres[o[2]].payload)
            elif str(spec[0]) == "rename":
                o = self.owner(menv, str(spec[1]))
                export(str(spec[2]), o[2], w.spheres[o[2]].payload)
            elif str(spec[0]) == "all-defined-out":
                for i in v.live("binding"):
                    if v.sphere(i).key[0] == menv:
                        export(v.sphere(i).key[1], i, v.payload(i))
            elif str(spec[0]) == "all-from-out":
                for n, e in self._exports(str(spec[1])).items():
                    export(n, e, w.spheres[e].payload)
            else:
                self.err("provide: bad form", "provide-syntax")
        w.collapse(lambda vw: tuple(sorted(n for (m, n) in (vw.sphere(i).key for i in vw.live("export")) if m == name)), "provides")

    def _provide(self, x, env):
        if not self._provides:
            self.err("provide: not at module level", "provide-outside-module")
        self._provides[-1].extend(x[1:])
        return None

    def _spec(self, s):
        if isinstance(s, Sym):
            return dict(self._exports(str(s)))
        h = str(s[0])
        if h == "only-in":
            d = self._spec(s[1])
            out = {}
            for n in s[2:]:
                if str(n) not in d:
                    self.err("only-in: identifier not provided: %s" % n, "not-provided")
                out[str(n)] = d[str(n)]
            return out
        if h == "except-in":
            d = self._spec(s[1])
            for n in s[2:]:
                d.pop(str(n), None)
            return d
        if h == "prefix-in":
            return {str(s[1]) + k: e for k, e in self._spec(s[2]).items()}
        if h == "rename-in":
            d = self._spec(s[1])
            for a, b in s[2:]:
                d[str(b)] = d.pop(str(a))
            return d
        self.err("require: bad form", "require-syntax")

    def _require(self, x, env):
        w, v = self.w, self.w.view
        for spec in x[1:]:
            for n, e in self._spec(spec).items():
                if v.last_key("binding", (env, n)) is not None:
                    self.err("require: identifier already defined: %s" % n, "import-conflicts-with-definition")
                prior = v.last_key("import", (env, n))
                if prior is not None:
                    if w.spheres[prior].deps[0] == e:
                        continue
                    self.err("require: identifier imported twice with different bindings: %s" % n, "conflicting-import")
                w.bind("import", (env, n), w.spheres[e].payload, (e,))
        return None

    # introspection (the analogue of which / type / where)
    def where(self, name, env=None):
        env = self.top if env is None else env
        o = self.owner(env, name)
        if o is None:
            return None
        e, tag, i = o
        if tag == "binding":
            return ("defined", None)
        exp = self.w.spheres[self.w.spheres[i].deps[0]]
        return ("imported" if tag == "import" else "language", exp.key[0])

    def imports_of(self, mod):
        v = self.w.view
        menv = v.payload(self._find(mod))
        return sorted((v.sphere(i).key[1], v.sphere(v.sphere(i).deps[0]).key[0])
                      for i in v.live("import") if v.sphere(i).key[0] == menv)
