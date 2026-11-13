"""Ordered search, the one operation shared by PATH lookup, collection paths and device lookup."""


def search(w, name, scopes, probe, tag="probe"):
    """Probe scopes in order. Each probe is a sphere: a miss is refused with its
    reason, the hit is popped (committed). Returns (target or None, tried)."""
    tried = []
    for sc in scopes:
        outcome, target = probe(sc, name)
        p = w.bind(tag, None, (sc, name, outcome))
        tried.append((sc, outcome))
        if outcome == "hit":
            w.pop(p)
            return target, tried
        w.refuse(p, "missing" if outcome == "missing" else outcome)
    return None, tried
