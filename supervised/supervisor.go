package supervised

import (
	"fmt"

	"github.com/standardgalactic/spherepop-kernel/reduce"
	"github.com/standardgalactic/spherepop-kernel/term"
)

// flatConfig is the configuration the worker reduces under: nothing is
// gated, absorption and scope are unrestricted. Under it reduce.Apply checks
// shape and nothing else.
func flatConfig(start *term.Term) reduce.Config {
	c := reduce.Config{Root: reduce.PermAll, Absorb: reduce.AbsAny, Sc: reduce.ScAny, Perm: map[string]reduce.PermSet{}}
	for _, l := range start.Labels() {
		c.Perm[l] = reduce.PermAll
	}
	return c
}

// Result is the outcome of a supervised run.
type Result struct {
	Term      *term.Term
	Steps     uint64 // accepted steps
	Refused   uint64 // refused proposals
	Exhausted bool
}

// Run reduces start. The worker proposes in the strategy's order, the
// supervisor decides each proposal, and every decision is logged. Fuel
// counts accepted steps. Once the budget is spent a silent probe, which logs
// nothing, decides whether a permitted step remained.
func Run(spec reduce.ConfigSpec, start *term.Term, strat reduce.Strategy, fuel uint64) (Result, Audit, error) {
	pol, err := FromSpec(spec)
	if err != nil {
		return Result{Term: start}, Audit{}, err
	}
	for _, l := range start.Labels() {
		if _, ok := spec.Perm[l]; !ok {
			return Result{Term: start}, Audit{}, fmt.Errorf("supervised: term uses label %q with no permission entry", l)
		}
	}
	ev, w, flat := NewEvaluator(pol), NewWorker(), flatConfig(start)
	a := Audit{
		Format: AuditFormat, Config: spec, Start: start.String(), StartDigest: start.Digest().String(),
		Strategy: strat.String(), Fuel: fuel, Entries: []Entry{},
	}
	res := Result{Term: start}
	cur := start
	for res.Steps < fuel {
		var accept *Candidate
		w.Candidates(cur, strat, func(c Candidate) bool {
			d := ev.Decide(cur, string(c.Path), c.Rule)
			if d.Allow {
				c := c
				accept = &c
				return true
			}
			a.Entries = append(a.Entries, Entry{Seq: len(a.Entries), Rule: c.Rule, Path: string(c.Path),
				Decision: "deny", Mask: d.Mask, After: cur.Digest().String()})
			res.Refused++
			return false
		})
		if accept == nil {
			break
		}
		next, err := flat.Apply(cur, accept.Path, reduce.RuleID(accept.Rule))
		if err != nil {
			return res, a, fmt.Errorf("supervised: internal error applying %s at %q: %w", accept.Rule, accept.Path, err)
		}
		d := ev.Decide(cur, string(accept.Path), accept.Rule)
		a.Entries = append(a.Entries, Entry{Seq: len(a.Entries), Rule: accept.Rule, Path: string(accept.Path),
			Decision: "allow", Mask: d.Mask, After: next.Digest().String()})
		cur = next
		res.Steps++
	}
	if res.Steps >= fuel {
		w.Candidates(cur, strat, func(c Candidate) bool {
			if ev.Decide(cur, string(c.Path), c.Rule).Allow {
				res.Exhausted = true
				return true
			}
			return false
		})
	}
	res.Term = cur
	a.Final, a.FinalDigest, a.Exhausted = cur.String(), cur.Digest().String(), res.Exhausted
	if err := Seal(&a); err != nil {
		return res, a, err
	}
	return res, a, nil
}
