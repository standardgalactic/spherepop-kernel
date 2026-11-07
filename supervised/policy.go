package supervised

import (
	"fmt"
	"strings"

	"github.com/standardgalactic/spherepop-kernel/reduce"
	"github.com/standardgalactic/spherepop-kernel/term"
)

type perm uint8

const (
	pW perm = 1 << iota
	pK
	pC
	pS
)

const pAll = pW | pK | pC | pS

var arity = map[string]int{"I": 1, "B": 3, "C": 3, "K": 2, "W": 2, "S": 3}

func bit(name string) (perm, bool) {
	switch name {
	case "W":
		return pW, true
	case "K":
		return pK, true
	case "C":
		return pC, true
	case "S":
		return pS, true
	}
	return 0, false
}

func parsePerms(names []string) (perm, error) {
	var p perm
	for _, n := range names {
		b, ok := bit(n)
		if !ok || p&b != 0 {
			return 0, fmt.Errorf("supervised: bad permission name %q", n)
		}
		p |= b
	}
	return p, nil
}

func maskString(m perm) string {
	var sb strings.Builder
	for _, n := range []string{"W", "K", "C", "S"} {
		if b, _ := bit(n); m&b != 0 {
			sb.WriteString(n)
		}
	}
	if sb.Len() == 0 {
		return "."
	}
	return sb.String()
}

// Policy is the supervisor's reading of a configuration.
type Policy struct {
	root   perm
	labels map[string]perm
	gated  perm
	absorb string
	scope  string
}

// FromSpec reads the serialised configuration. Anything it does not
// recognise is an error, so the supervisor fails closed.
func FromSpec(s reduce.ConfigSpec) (Policy, error) {
	var p Policy
	var err error
	if p.root, err = parsePerms(s.Root); err != nil {
		return p, err
	}
	if p.gated, err = parsePerms(s.Gated); err != nil {
		return p, err
	}
	p.labels = map[string]perm{}
	for l, names := range s.Perm {
		if p.labels[l], err = parsePerms(names); err != nil {
			return p, err
		}
	}
	switch s.Absorb {
	case "off", "any", "nf", "s", "u":
		p.absorb = s.Absorb
	default:
		return p, fmt.Errorf("supervised: unknown absorption mode %q", s.Absorb)
	}
	switch s.Sc {
	case "any", "safe", "settled":
		p.scope = s.Sc
	default:
		return p, fmt.Errorf("supervised: unknown scope mode %q", s.Sc)
	}
	return p, nil
}

type key struct {
	d term.Digest
	m perm
}

// Evaluator answers the policy's predicates, memoising on the digest of a
// term and the permission in force.
type Evaluator struct {
	p   Policy
	rn  map[key]bool
	st  map[key]bool
	ins map[term.Digest]bool
}

// NewEvaluator returns an evaluator for p.
func NewEvaluator(p Policy) *Evaluator {
	return &Evaluator{p: p, rn: map[key]bool{}, st: map[key]bool{}, ins: map[term.Digest]bool{}}
}

// shape names the rule whose left-hand side matches n, or "" if none does.
// It looks at structure only; it knows nothing of permissions.
func shape(n *term.Term) string {
	if n.Kind() != term.KindApp {
		return ""
	}
	switch n.Fun().Kind() {
	case term.KindScope:
		return "Sc"
	case term.KindBracket:
		return "Abs"
	}
	head, k := n.Head()
	if head.Kind() == term.KindConst && arity[head.Name()] == k {
		return head.Name()
	}
	return ""
}

func (e *Evaluator) admissible(rule string, mask perm) bool {
	b, ok := bit(rule)
	if !ok || e.p.gated&b == 0 {
		return true
	}
	return mask&b != 0
}

func (e *Evaluator) contraction(n *term.Term, mask perm) bool {
	r := shape(n)
	if r == "" || r == "Sc" || r == "Abs" {
		return false
	}
	return e.admissible(r, mask)
}

func (e *Evaluator) rnormal(v *term.Term, mask perm) bool {
	k := key{v.Digest(), mask}
	if r, ok := e.rn[k]; ok {
		return r
	}
	r := true
	switch v.Kind() {
	case term.KindApp:
		r = !e.contraction(v, mask) && e.rnormal(v.Fun(), mask) && e.rnormal(v.Arg(), mask)
	case term.KindBracket:
		r = e.rnormal(v.Body(), mask&e.p.labels[v.Label()])
	}
	e.rn[k] = r
	return r
}

func (e *Evaluator) settled(v *term.Term, mask perm) bool {
	k := key{v.Digest(), mask}
	if r, ok := e.st[k]; ok {
		return r
	}
	r := true
	switch v.Kind() {
	case term.KindApp:
		fk := v.Fun().Kind()
		r = fk != term.KindBracket && fk != term.KindScope && !e.contraction(v, mask) &&
			e.settled(v.Fun(), mask) && e.settled(v.Arg(), mask)
	case term.KindBracket:
		r = e.settled(v.Body(), mask&e.p.labels[v.Label()])
	}
	e.st[k] = r
	return r
}

func (e *Evaluator) insensitive(v *term.Term) bool {
	if r, ok := e.ins[v.Digest()]; ok {
		return r
	}
	r := true
	switch v.Kind() {
	case term.KindConst:
		if b, ok := bit(v.Name()); ok && e.p.gated&b != 0 {
			r = false
		}
	case term.KindApp:
		r = e.insensitive(v.Fun()) && e.insensitive(v.Arg())
	case term.KindBracket:
		r = e.insensitive(v.Body())
	}
	e.ins[v.Digest()] = r
	return r
}

func (e *Evaluator) safe(v *term.Term, mask perm) bool {
	return e.rnormal(v, mask) && (e.settled(v, mask) || e.insensitive(v))
}

func (e *Evaluator) absorbOK(v *term.Term, mask perm) bool {
	switch e.p.absorb {
	case "any":
		return true
	case "nf":
		return e.rnormal(v, mask)
	case "s":
		return e.settled(v, mask)
	case "u":
		return e.safe(v, mask)
	}
	return false
}

func (e *Evaluator) scopeOK(v *term.Term, mask perm) bool {
	switch e.p.scope {
	case "any":
		return true
	case "safe":
		return e.safe(v, mask)
	case "settled":
		return e.settled(v, mask)
	}
	return false
}

// Decision is the supervisor's verdict on one proposal. Mask is the
// effective permission at the proposal's position, "." when empty, and "-"
// when the path leads nowhere.
type Decision struct {
	Allow bool
	Mask  string
}

func (e *Evaluator) locate(t *term.Term, path string) (*term.Term, perm, bool) {
	mask, cur := e.p.root, t
	for i := 0; i < len(path); i++ {
		switch {
		case path[i] == term.StepFun && cur.Kind() == term.KindApp:
			cur = cur.Fun()
		case path[i] == term.StepArg && cur.Kind() == term.KindApp:
			cur = cur.Arg()
		case path[i] == term.StepBody && cur.Kind() == term.KindBracket:
			mask &= e.p.labels[cur.Label()]
			cur = cur.Body()
		default:
			return nil, 0, false
		}
	}
	return cur, mask, true
}

// Decide rules on the proposal to apply rule at path of t.
func (e *Evaluator) Decide(t *term.Term, path, rule string) Decision {
	n, mask, ok := e.locate(t, path)
	if !ok {
		return Decision{Mask: "-"}
	}
	d := Decision{Mask: maskString(mask)}
	if shape(n) != rule {
		return d
	}
	switch rule {
	case "Sc":
		d.Allow = e.scopeOK(n.Arg(), mask)
	case "Abs":
		d.Allow = e.absorbOK(n.Arg(), mask)
	default:
		d.Allow = e.admissible(rule, mask)
	}
	return d
}
