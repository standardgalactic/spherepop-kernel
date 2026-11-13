"""Register transfers and the clock boundary.

A register word is a row of stage spheres. A clock edge samples one old word
and one input, then commits one new word. The ledger retains the old
rightmost occurrence as evidence of the bit shifted out.
"""
from .kernel import World, attempt_refused, choose


class ControlError(Exception):
    pass


def word_rule(v):
    return tuple(v.payload(i) for i in sorted(v.live("stage"), key=lambda i: v.sphere(i).key))


class ShiftRegister:
    def __init__(self, bits=(0, 0, 0, 0), world=None):
        self.w = world or World()
        self.n = len(bits)
        for k, b in enumerate(bits):
            self.w.bind("stage", k, b)

    def word(self):
        return word_rule(self.w.view)

    def edge(self, b):
        """One clock edge. Every stage samples the same pre-edge word."""
        w, v = self.w, self.w.view
        old_ids = [v.last_key("stage", k) for k in range(self.n)]
        old = [v.payload(i) for i in old_ids]
        inp = w.bind("input", None, b)
        w.bind("shifted-out", None, old[-1], (old_ids[-1],))
        for i in old_ids:
            w.pop(i)
        for k in range(self.n):
            src = inp if k == 0 else old_ids[k - 1]
            w.bind("stage", k, b if k == 0 else old[k - 1], (src,))
        w.pop(inp)
        w.collapse(word_rule, "word")
        return self

    def shifted_out(self):
        i = self.w.view.last("shifted-out")
        return self.w.view.payload(i)


class RippleRegister(ShiftRegister):
    """Faulty variant: each stage reads the frontier already being updated."""

    def edge(self, b):
        w, v = self.w, self.w.view
        prev = b
        for k in range(self.n):
            cur = v.last_key("stage", k)
            old = v.payload(cur)
            w.pop(cur)
            w.bind("stage", k, prev if k == 0 else v.payload(v.last_key("stage", k - 1)), ())
            prev = old
        w.bind("shifted-out", None, 0)
        return self


class TransferRegister:
    """R0 loads one of n candidate sources chosen by control lines K."""

    def __init__(self, value=0, world=None):
        self.w = world or World()
        self.r = self.w.bind("reg", 0, value)

    def value(self):
        return self.w.view.payload(self.w.view.last_key("reg", 0))

    def clock(self, sources, controls):
        w = self.w
        if len(sources) != len(controls):
            raise ValueError("one control per source")
        if sum(controls) > 1:
            attempt_refused(w, "attempt", tuple(controls), "multiple-select")
            raise ControlError("more than one source-select asserted: %r" % (tuple(controls),))
        if not any(controls):
            return self.value()          # Load = OR(K) = 0: hold
        cands = [w.bind("candidate", k, s, (self.r,)) for k, s in enumerate(sources)]
        k = controls.index(1)
        choose(w, cands[k], [c for j, c in enumerate(cands) if j != k], "not-selected")
        new = w.bind("reg", 0, w.spheres[cands[k]].payload, (cands[k],))
        w.refuse(self.r, "loaded")
        self.r = new
        w.collapse(lambda v: v.payload(v.last_key("reg", 0)), "R0")
        return self.value()
