package reduce

import (
	"fmt"

	"github.com/standardgalactic/spherepop-kernel/term"
)

// maskAt returns the effective permission at the end of path p in t: the
// root permission intersected with the permission of every bracket entered.
func (c *Config) maskAt(t *term.Term, p term.Path) (PermSet, *term.Term, error) {
	mask := c.Root
	cur := t
	for i := 0; i < len(p); i++ {
		switch {
		case p[i] == term.StepFun && cur.Kind() == term.KindApp:
			cur = cur.Fun()
		case p[i] == term.StepArg && cur.Kind() == term.KindApp:
			cur = cur.Arg()
		case p[i] == term.StepBody && cur.Kind() == term.KindBracket:
			mask &= c.perm(cur.Label())
			cur = cur.Body()
		default:
			return 0, nil, fmt.Errorf("%w: step %d (%q) of %q", term.ErrBadPath, i, p[i], string(p))
		}
	}
	return mask, cur, nil
}

// Apply performs one step: rule id at path p of t. It is the single authority
// on what a step means. The reducer calls it to move, and the trace checker
// calls it to verify, so a step is valid exactly when Apply accepts it.
func (c *Config) Apply(t *term.Term, p term.Path, id RuleID) (*term.Term, error) {
	rule, ok := Lookup(id)
	if !ok {
		return nil, fmt.Errorf("%w: %q", ErrUnknownRule, id)
	}
	mask, n, err := c.maskAt(t, p)
	if err != nil {
		return nil, err
	}
	var r *term.Term
	switch rule.ID {
	case RuleSc:
		if n.Kind() != term.KindApp || n.Fun().Kind() != term.KindScope {
			return nil, fmt.Errorf("%w: %s at %q", ErrRuleMismatch, id, string(p))
		}
		if !newSession(c).scopes(n.Arg(), mask) {
			return nil, fmt.Errorf("%w: scope mode %s, argument %s", ErrAbsorptionBlock, c.scMode(), n.Arg())
		}
		r = term.Bracket(n.Fun().Label(), n.Arg())
	case RuleAbs:
		if n.Kind() != term.KindApp || n.Fun().Kind() != term.KindBracket {
			return nil, fmt.Errorf("%w: %s at %q", ErrRuleMismatch, id, string(p))
		}
		s := newSession(c)
		if !s.absorbs(n.Arg(), mask) {
			return nil, fmt.Errorf("%w: mode %s, argument %s", ErrAbsorptionBlock, c.Absorb, n.Arg())
		}
		r = term.Bracket(n.Fun().Label(), term.App(n.Fun().Body(), n.Arg()))
	default:
		head, args := n.Spine()
		if head.Kind() != term.KindConst || head.Name() != rule.Head || len(args) != rule.Arity {
			return nil, fmt.Errorf("%w: %s at %q", ErrRuleMismatch, id, string(p))
		}
		if !c.admissible(rule.Head, mask) {
			return nil, fmt.Errorf("%w: %s at %q with permission %s", ErrNotAdmissible, id, string(p), mask)
		}
		r = rule.contract(args)
	}
	return t.Replace(p, r)
}

// EffectivePerm returns the permission in force at path p of t: the root
// permission narrowed by every bracket label on the way down.
func (c *Config) EffectivePerm(t *term.Term, p term.Path) (PermSet, error) {
	m, _, err := c.maskAt(t, p)
	return m, err
}
