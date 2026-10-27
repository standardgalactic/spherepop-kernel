package reduce

import "github.com/standardgalactic/spherepop-kernel/term"

// This file is the reference implementation of redex search, kept exactly as
// it was before the structural-flag shortcuts and the path buffer were added
// to find.go. It has no shortcuts and builds a path string at every step. The
// tests in find_equivalence_test.go require the optimised search to agree with
// it on every term they enumerate. Do not optimise this file.

type refKey struct {
	d    term.Digest
	mask PermSet
}

// session holds memo tables for one run. Every predicate it memoises is a
// pure function of a term's digest and an effective permission mask.
type refSession struct {
	cfg      *Config
	quiet    map[refKey]struct{} // subterms with no redex of any kind
	rnormal  map[refKey]bool
	settled  map[refKey]bool
	insens   map[term.Digest]bool
	strategy Strategy
	count    int
	visit    func(Redex) bool
}

func newRefSession(c *Config) *refSession {
	return &refSession{
		cfg:     c,
		quiet:   map[refKey]struct{}{},
		rnormal: map[refKey]bool{},
		settled: map[refKey]bool{},
		insens:  map[term.Digest]bool{},
	}
}

// contractionAt reports the contraction redex rooted at n, if any.
func (s *refSession) contractionAt(n *term.Term, mask PermSet) (RuleID, bool) {
	if n.Kind() != term.KindApp {
		return "", false
	}
	head, k := n.Head()
	if head.Kind() != term.KindConst {
		return "", false
	}
	r, ok := ruleForHead(head.Name())
	if !ok || r.Arity != k || !s.cfg.admissible(r.Head, mask) {
		return "", false
	}
	return r.ID, true
}

// redexAt reports the redex rooted at n, if any: a permitted contraction, an
// Sc step, or an Abs step whose side condition holds.
func (s *refSession) redexAt(n *term.Term, mask PermSet) (RuleID, bool) {
	if n.Kind() != term.KindApp {
		return "", false
	}
	switch n.Fun().Kind() {
	case term.KindScope:
		if s.scopes(n.Arg(), mask) {
			return RuleSc, true
		}
		return "", false
	case term.KindBracket:
		if s.absorbs(n.Arg(), mask) {
			return RuleAbs, true
		}
		return "", false
	}
	return s.contractionAt(n, mask)
}

// isRNormal reports that v has no permitted contraction at the chain whose
// effective permission is mask. Boundary rules are not part of R.
func (s *refSession) isRNormal(v *term.Term, mask PermSet) bool {
	k := refKey{v.Digest(), mask}
	if r, ok := s.rnormal[k]; ok {
		return r
	}
	r := true
	switch v.Kind() {
	case term.KindApp:
		if _, ok := s.contractionAt(v, mask); ok {
			r = false
		} else {
			r = s.isRNormal(v.Fun(), mask) && s.isRNormal(v.Arg(), mask)
		}
	case term.KindBracket:
		r = s.isRNormal(v.Body(), mask&s.cfg.perm(v.Label()))
	}
	s.rnormal[k] = r
	return r
}

// isSettled reports that v is R-normal and has no pending boundary step: no
// application whose function child is a bracket or a scope constructor. The
// scope clause is a deliberately conservative reading, see SPEC.md.
func (s *refSession) isSettled(v *term.Term, mask PermSet) bool {
	k := refKey{v.Digest(), mask}
	if r, ok := s.settled[k]; ok {
		return r
	}
	r := true
	switch v.Kind() {
	case term.KindApp:
		if fk := v.Fun().Kind(); fk == term.KindBracket || fk == term.KindScope {
			r = false
		} else if _, ok := s.contractionAt(v, mask); ok {
			r = false
		} else {
			r = s.isSettled(v.Fun(), mask) && s.isSettled(v.Arg(), mask)
		}
	case term.KindBracket:
		r = s.isSettled(v.Body(), mask&s.cfg.perm(v.Label()))
	}
	s.settled[k] = r
	return r
}

// isInsensitive reports that v contains no gated constant.
func (s *refSession) isInsensitive(v *term.Term) bool {
	if r, ok := s.insens[v.Digest()]; ok {
		return r
	}
	r := true
	switch v.Kind() {
	case term.KindConst:
		if bit, ok := permBit(v.Name()); ok && s.cfg.Gated&bit != 0 {
			r = false
		}
	case term.KindApp:
		r = s.isInsensitive(v.Fun()) && s.isInsensitive(v.Arg())
	case term.KindBracket:
		r = s.isInsensitive(v.Body())
	}
	s.insens[v.Digest()] = r
	return r
}

// absorbs evaluates the side condition of Abs for argument v at the chain
// whose effective permission is mask.
func (s *refSession) absorbs(v *term.Term, mask PermSet) bool {
	switch s.cfg.Absorb {
	case AbsAny:
		return true
	case AbsNF:
		return s.isRNormal(v, mask)
	case AbsS:
		return s.isSettled(v, mask)
	case AbsU:
		return s.isRNormal(v, mask) && (s.isSettled(v, mask) || s.isInsensitive(v))
	}
	return false
}

// scopes evaluates the side condition of Sc for argument v at the chain with
// effective permission mask.
func (s *refSession) scopes(v *term.Term, mask PermSet) bool {
	switch s.cfg.scMode() {
	case ScSafe:
		return s.isRNormal(v, mask) && (s.isSettled(v, mask) || s.isInsensitive(v))
	case ScSettled:
		return s.isSettled(v, mask)
	}
	return true
}

// walk visits redexes of t in the strategy's order and reports whether the
// visitor asked to stop.
func (s *refSession) walk(t *term.Term, mask PermSet, path term.Path) bool {
	k := refKey{t.Digest(), mask}
	if _, ok := s.quiet[k]; ok {
		return false
	}
	before := s.count
	var stop bool
	outer := s.strategy == LeftmostOutermost || s.strategy == RightmostOutermost
	rightFirst := s.strategy == RightmostOutermost || s.strategy == RightmostInnermost
	if outer {
		stop = s.here(t, mask, path) || s.kids(t, mask, path, rightFirst)
	} else {
		stop = s.kids(t, mask, path, rightFirst) || s.here(t, mask, path)
	}
	if !stop && s.count == before {
		s.quiet[k] = struct{}{}
	}
	return stop
}

func (s *refSession) here(t *term.Term, mask PermSet, path term.Path) bool {
	id, ok := s.redexAt(t, mask)
	if !ok {
		return false
	}
	s.count++
	return s.visit(Redex{Path: path, Rule: id})
}

func (s *refSession) kids(t *term.Term, mask PermSet, path term.Path, rightFirst bool) bool {
	switch t.Kind() {
	case term.KindApp:
		l := func() bool { return s.walk(t.Fun(), mask, path.Down(term.StepFun)) }
		r := func() bool { return s.walk(t.Arg(), mask, path.Down(term.StepArg)) }
		if rightFirst {
			return r() || l()
		}
		return l() || r()
	case term.KindBracket:
		return s.walk(t.Body(), mask&s.cfg.perm(t.Label()), path.Down(term.StepBody))
	}
	return false
}

// refRedexes lists every step of t in strategy order using the reference
// implementation.
func refRedexes(c *Config, t *term.Term, strat Strategy) []Redex {
	s := newRefSession(c)
	s.strategy = strat
	var out []Redex
	s.visit = func(r Redex) bool { out = append(out, r); return false }
	s.walk(t, c.Root, "")
	return out
}
