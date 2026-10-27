// Package reduce applies the rules of SpherePOP to terms. It knows rules,
// permissions and strategies, and nothing about games, clocks, networks or
// persistence. A host that wants effects reads the trace or the result.
package reduce

import (
	"fmt"

	"github.com/standardgalactic/spherepop-kernel/term"
)

// Step is one recorded reduction: the rule, where it applied, and the digests
// of the whole term before and after. A step carries no term text; a checker
// holds the term it is replaying and recomputes the result itself.
type Step struct {
	Rule   RuleID      `json:"rule"`
	Path   term.Path   `json:"path"`
	Before term.Digest `json:"-"`
	After  term.Digest `json:"-"`
}

// Result is the outcome of a bounded reduction.
type Result struct {
	Term      *term.Term
	Steps     uint64
	Exhausted bool // fuel ran out while a redex was still available
	Stopped   bool // the caller's stop predicate held before the run could continue
	Trace     []Step
}

// Reduce reduces t under the default configuration.
func Reduce(t *term.Term, strat Strategy, fuel uint64) (Result, error) {
	c := DefaultConfig()
	return c.Reduce(t, strat, fuel)
}

// Reduce performs at most fuel steps under the strategy. If a normal form is
// reached within the budget, Exhausted is false and Term is that normal form.
// Otherwise Exhausted is true and Term is the term after the last step.
func (c *Config) Reduce(t *term.Term, strat Strategy, fuel uint64) (Result, error) {
	return c.ReduceUntil(t, strat, fuel, nil)
}

// ReduceUntil is Reduce with an execution boundary. Before each step, and
// before declaring a normal form or exhaustion, it asks stop of the current
// term; if stop holds the run ends there with Stopped set. The predicate is
// not a rule: it never changes a term, and a term it stops is a term the rules
// could still reduce. A nil stop never holds.
func (c *Config) ReduceUntil(t *term.Term, strat Strategy, fuel uint64, stop func(*term.Term) bool) (Result, error) {
	if _, ok := ParseStrategy(strat.String()); !ok {
		return Result{Term: t}, fmt.Errorf("reduce: unknown strategy %d", uint8(strat))
	}
	if err := c.Validate(t); err != nil {
		return Result{Term: t}, err
	}
	s := newSession(c)
	s.strategy = strat
	res := Result{Term: t}
	for {
		if stop != nil && stop(res.Term) {
			res.Stopped = true
			return res, nil
		}
		var next Redex
		var found bool
		s.visit = func(r Redex) bool { next, found = r, true; return true }
		s.walk(res.Term, c.Root)
		if !found {
			return res, nil
		}
		if res.Steps >= fuel {
			res.Exhausted = true
			return res, nil
		}
		out, err := c.Apply(res.Term, next.Path, next.Rule)
		if err != nil {
			return res, fmt.Errorf("reduce: internal error applying %s at %q: %w", next.Rule, next.Path, err)
		}
		if c.Trace {
			res.Trace = append(res.Trace, Step{Rule: next.Rule, Path: next.Path, Before: res.Term.Digest(), After: out.Digest()})
		}
		res.Term = out
		res.Steps++
	}
}
