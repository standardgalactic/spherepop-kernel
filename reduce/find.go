package reduce

import "github.com/standardgalactic/spherepop-kernel/term"

// Strategy selects which redex to contract when several are available.
type Strategy uint8

// The four deterministic strategies. Outermost means a node is considered
// before its children, innermost after. Leftmost visits the function child
// before the argument, rightmost the reverse.
const (
	LeftmostOutermost Strategy = iota + 1
	LeftmostInnermost
	RightmostInnermost
	RightmostOutermost
)

func (s Strategy) String() string {
	switch s {
	case LeftmostOutermost:
		return "lo"
	case LeftmostInnermost:
		return "li"
	case RightmostInnermost:
		return "ri"
	case RightmostOutermost:
		return "ro"
	}
	return "strategy(?)"
}

// ParseStrategy reads a strategy name and fails closed on anything else.
func ParseStrategy(s string) (Strategy, bool) {
	for _, st := range []Strategy{LeftmostOutermost, LeftmostInnermost, RightmostInnermost, RightmostOutermost} {
		if st.String() == s {
			return st, true
		}
	}
	return 0, false
}

// Redex is a position where a step is available.
type Redex struct {
	Path term.Path
	Rule RuleID
}

type nkey struct {
	d    term.Digest
	mask PermSet
}

// session holds memo tables for one run. Every predicate it memoises is a
// pure function of a term's digest and an effective permission mask.
type session struct {
	cfg      *Config
	quiet    map[nkey]struct{} // subterms with no redex of any kind
	rnormal  map[nkey]bool
	settled  map[nkey]bool
	strategy Strategy
	count    int
	visit    func(Redex) bool
	path     []byte // the position being visited, one step character per level
}

func newSession(c *Config) *session {
	return &session{
		cfg:     c,
		quiet:   map[nkey]struct{}{},
		rnormal: map[nkey]bool{},
		settled: map[nkey]bool{},
	}
}

// contractFlags returns the structural flags of the constants that head a
// contraction admissible under mask. I and B are never gated. A gated
// constant counts only if its bit is in mask, an ungated one always counts.
// Entering a bracket only narrows the mask, so a subterm with none of these
// flags has no contraction anywhere inside it at mask or at any narrower one.
func (s *session) contractFlags(mask PermSet) uint8 {
	gated := s.cfg.Gated & PermAll
	return uint8(PermAll&^gated) | uint8(mask&gated) | term.FlagI | term.FlagB
}

// contractionAt reports the contraction redex rooted at n, if any.
func (s *session) contractionAt(n *term.Term, mask PermSet) (RuleID, bool) {
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
func (s *session) redexAt(n *term.Term, mask PermSet) (RuleID, bool) {
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
func (s *session) isRNormal(v *term.Term, mask PermSet) bool {
	if v.Flags()&s.contractFlags(mask) == 0 {
		return true // no admissible contraction head anywhere in v
	}
	k := nkey{v.Digest(), mask}
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
func (s *session) isSettled(v *term.Term, mask PermSet) bool {
	if v.Flags()&(term.FlagBracket|term.FlagScope) == 0 {
		// No bracket or scope constructor, so no pending boundary step can
		// exist and settled means R-normal.
		return s.isRNormal(v, mask)
	}
	k := nkey{v.Digest(), mask}
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

// isInsensitive reports that v contains no gated constant. The structural
// flags record which of W, K, C and S occur, in the bits of the permission
// alphabet, so this is one bitwise test.
func (s *session) isInsensitive(v *term.Term) bool {
	return v.Flags()&uint8(s.cfg.Gated&PermAll) == 0
}

// absorbs evaluates the side condition of Abs for argument v at the chain
// whose effective permission is mask.
func (s *session) absorbs(v *term.Term, mask PermSet) bool {
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
func (s *session) scopes(v *term.Term, mask PermSet) bool {
	switch s.cfg.scMode() {
	case ScSafe:
		return s.isRNormal(v, mask) && (s.isSettled(v, mask) || s.isInsensitive(v))
	case ScSettled:
		return s.isSettled(v, mask)
	}
	return true
}

// Safe is the decidable transfer criterion of the scoped-rules essay,
// Proposition 4.11: v is R-normal at the chain with effective permission mask
// and is either settled or insensitive. It is exported so a host can ask
// whether an argument could cross a boundary.
func (c *Config) Safe(v *term.Term, mask PermSet) bool {
	s := newSession(c)
	return s.isRNormal(v, mask) && (s.isSettled(v, mask) || s.isInsensitive(v))
}

// noRedex reports that t cannot contain any step at mask, from its flags
// alone. A contraction needs an admissible constant, Sc needs a scope
// constructor, and Abs needs a bracket and is available only when absorption
// is not off.
func (s *session) noRedex(t *term.Term, mask PermSet) bool {
	possible := s.contractFlags(mask) | term.FlagScope
	if s.cfg.Absorb != AbsOff {
		possible |= term.FlagBracket
	}
	return t.Flags()&possible == 0
}

// walk visits redexes of t in the strategy's order and reports whether the
// visitor asked to stop. The position is kept in s.path and a Path string is
// made only when a redex is reported.
func (s *session) walk(t *term.Term, mask PermSet) bool {
	if s.noRedex(t, mask) {
		return false
	}
	k := nkey{t.Digest(), mask}
	if _, ok := s.quiet[k]; ok {
		return false
	}
	before := s.count
	var stop bool
	outer := s.strategy == LeftmostOutermost || s.strategy == RightmostOutermost
	rightFirst := s.strategy == RightmostOutermost || s.strategy == RightmostInnermost
	if outer {
		stop = s.here(t, mask) || s.kids(t, mask, rightFirst)
	} else {
		stop = s.kids(t, mask, rightFirst) || s.here(t, mask)
	}
	if !stop && s.count == before {
		s.quiet[k] = struct{}{}
	}
	return stop
}

func (s *session) here(t *term.Term, mask PermSet) bool {
	id, ok := s.redexAt(t, mask)
	if !ok {
		return false
	}
	s.count++
	return s.visit(Redex{Path: term.Path(s.path), Rule: id})
}

func (s *session) down(step byte, t *term.Term, mask PermSet) bool {
	s.path = append(s.path, step)
	stop := s.walk(t, mask)
	s.path = s.path[:len(s.path)-1]
	return stop
}

func (s *session) kids(t *term.Term, mask PermSet, rightFirst bool) bool {
	switch t.Kind() {
	case term.KindApp:
		if rightFirst {
			return s.down(term.StepArg, t.Arg(), mask) || s.down(term.StepFun, t.Fun(), mask)
		}
		return s.down(term.StepFun, t.Fun(), mask) || s.down(term.StepArg, t.Arg(), mask)
	case term.KindBracket:
		return s.down(term.StepBody, t.Body(), mask&s.cfg.perm(t.Label()))
	}
	return false
}

// Redexes returns every available step of t in the order the strategy would
// consider them. The first element is the step the strategy takes.
func (c *Config) Redexes(t *term.Term, strat Strategy) []Redex {
	s := newSession(c)
	s.strategy = strat
	var out []Redex
	s.visit = func(r Redex) bool { out = append(out, r); return false }
	s.walk(t, c.Root)
	return out
}
