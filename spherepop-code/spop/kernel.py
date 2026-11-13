"""Reference kernel: four primitives over an append-only ledger.

Pop commits a live sphere. Refuse excludes a live sphere with a recorded
reason. Bind introduces a sphere coupled to its dependencies without
consuming them. Collapse projects the world under a rule and records the
commitment. All language state in later chapters lives in a World and is
read only through views.
"""
import hashlib
from collections import Counter
from dataclasses import dataclass
from typing import Any, Tuple

LIVE, POPPED, REFUSED = "live", "popped", "refused"


class Inadmissible(Exception):
    """A primitive was proposed outside the admissible region."""


@dataclass(frozen=True)
class Sphere:
    id: int
    tag: str
    key: Any
    payload: Any
    deps: Tuple[int, ...]


def digest(value):
    return hashlib.sha256(repr(value).encode()).hexdigest()[:16]


class View:
    """Read-only projection of a world (the pure part of Collapse)."""

    def __init__(self, w):
        self._w = w

    def live(self, tag):
        return list(self._w._tag.get(tag, ()))

    def live_key(self, tag, key):
        return list(self._w._key.get((tag, key), ()))

    def last(self, tag):
        d = self._w._tag.get(tag)
        return next(reversed(d)) if d else None

    def first(self, tag):
        d = self._w._tag.get(tag)
        return next(iter(d)) if d else None

    def last_key(self, tag, key):
        d = self._w._key.get((tag, key))
        return next(reversed(d)) if d else None

    def count(self, tag):
        return len(self._w._tag.get(tag, ()))

    def sphere(self, i):
        return self._w.spheres[i]

    def payload(self, i):
        return self._w.spheres[i].payload

    def status(self, i):
        return self._w.status[i]

    def reason(self, i):
        return self._w.reasons.get(i)

    def size(self):
        return len(self._w.ledger)

    def ancestors(self, i):
        seen, stack = set(), [i]
        while stack:
            for d in self._w.spheres[stack.pop()].deps:
                if d not in seen:
                    seen.add(d)
                    stack.append(d)
        return seen


class World:
    def __init__(self):
        self.ledger = []
        self.spheres = {}
        self.status = {}
        self.reasons = {}
        self._tag = {}
        self._key = {}
        self.view = View(self)

    # the four primitives
    def bind(self, tag, key=None, payload=None, deps=()):
        sid = len(self.spheres)
        self._commit(("bind", sid, tag, key, payload, tuple(deps)))
        return sid

    def pop(self, sid):
        self._commit(("pop", sid))
        return self.spheres[sid].payload

    def refuse(self, sid, reason):
        self._commit(("refuse", sid, reason))

    def collapse(self, rule, name=None):
        value = rule(self.view)
        self._commit(("collapse", name or getattr(rule, "__name__", "rule"), digest(value)))
        return value

    # admissibility and application of events
    def _commit(self, e):
        k = e[0]
        if k == "bind":
            if e[1] != len(self.spheres):
                raise Inadmissible("sphere id out of order")
            for d in e[5]:
                if d not in self.spheres:
                    raise Inadmissible("unborn dependency %r" % d)
        elif k in ("pop", "refuse"):
            if self.status.get(e[1]) != LIVE:
                raise Inadmissible("%s of non-live sphere %r" % (k, e[1]))
            if k == "refuse" and not (isinstance(e[2], str) and e[2]):
                raise Inadmissible("refusal requires a reason")
        elif k != "collapse":
            raise Inadmissible("unknown event %r" % (k,))
        self.ledger.append(e)
        if k == "bind":
            s = Sphere(e[1], e[2], e[3], e[4], e[5])
            self.spheres[s.id] = s
            self.status[s.id] = LIVE
            self._tag.setdefault(s.tag, {})[s.id] = None
            self._key.setdefault((s.tag, s.key), {})[s.id] = None
        elif k in ("pop", "refuse"):
            s = self.spheres[e[1]]
            self.status[s.id] = POPPED if k == "pop" else REFUSED
            if k == "refuse":
                self.reasons[s.id] = e[2]
            del self._tag[s.tag][s.id]
            kk = (s.tag, s.key)
            del self._key[kk][s.id]
            if not self._key[kk]:
                del self._key[kk]

    # evidence and acceptance
    def chain(self):
        h = ""
        for e in self.ledger:
            h = hashlib.sha256((h + repr(e)).encode()).hexdigest()
        return h[:16]

    def counts(self):
        return Counter(e[0] for e in self.ledger)

    @classmethod
    def replay(cls, events, rules=None):
        w = cls()
        for e in events:
            if e[0] == "collapse" and rules and e[1] in rules:
                if digest(rules[e[1]](w.view)) != e[2]:
                    raise Inadmissible("collapse digest mismatch for %s" % e[1])
            w._commit(e)
        return w

    def verify(self, rules=None, expected_chain=None):
        w2 = World.replay(self.ledger, rules)
        ok = (w2.status == self.status and w2.reasons == self.reasons
              and {t: list(d) for t, d in w2._tag.items()} == {t: list(d) for t, d in self._tag.items()})
        if expected_chain is not None:
            ok = ok and w2.chain() == expected_chain
        if not ok:
            raise Inadmissible("replay disagrees with indexed state")
        return True


# derived forms
def supersede(w, old, payload, reason="superseded"):
    """Mutation as documented refusal of the old sphere plus a coupled new one."""
    s = w.spheres[old]
    w.refuse(old, reason)
    return w.bind(s.tag, s.key, payload, (old,))


def choose(w, taken, rejected, reason="not-taken"):
    """Choice(A,B) = Pop(A) parallel Refuse(B)."""
    w.pop(taken)
    for r in rejected:
        w.refuse(r, reason)


def attempt_refused(w, tag, payload, reason):
    """Documented refusal of an inadmissible proposal."""
    i = w.bind(tag, None, payload)
    w.refuse(i, reason)
    return i


def apply_via(w, rule, fn, arg, name="subst"):
    """Application = Collapse_rule(Bind(fn, arg))."""
    c = w.bind("app", None, None, (fn, arg))
    value = w.collapse(lambda v: rule(v.payload(fn), v.payload(arg)), name)
    return c, value
