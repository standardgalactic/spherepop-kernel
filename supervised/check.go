package supervised

import (
	"errors"
	"fmt"

	"github.com/standardgalactic/spherepop-kernel/reduce"
	"github.com/standardgalactic/spherepop-kernel/term"
)

// Sentinel errors for the ways an audit log can fail.
var (
	ErrFormat   = errors.New("supervised: malformed log")
	ErrChain    = errors.New("supervised: hash chain does not verify")
	ErrDecision = errors.New("supervised: logged decision is not the policy's")
	ErrDigest   = errors.New("supervised: entry result does not match its claimed digest")
	ErrFinal    = errors.New("supervised: final term does not match the log")
	ErrStatus   = errors.New("supervised: claimed termination status is wrong")
	ErrStrategy = errors.New("supervised: proposals are not those of the claimed strategy")
	ErrApply    = errors.New("supervised: step cannot be applied")
)

// Options tune a check.
type Options struct {
	// RequireStrategy demands that the log is exactly the proposals the
	// claimed strategy would make, in order, each with the policy's decision.
	// Without it a log is valid when every entry carries the policy's
	// decision, and a refusal the worker left out goes unnoticed.
	RequireStrategy bool
	// Fuel, if non-zero, is the budget the host agreed.
	Fuel uint64
}

// common checks the format, the start term and the hash chain, and returns
// the parsed start term. It trusts nothing in the log but the text of the
// start term and the configuration.
func common(a Audit, opt Options) (*term.Term, error) {
	if a.Format != AuditFormat {
		return nil, fmt.Errorf("%w: format %q", ErrFormat, a.Format)
	}
	if _, err := a.Config.Config(); err != nil {
		return nil, fmt.Errorf("%w: %v", ErrFormat, err)
	}
	start, err := term.Parse(a.Start)
	if err != nil {
		return nil, fmt.Errorf("%w: start term: %v", ErrFormat, err)
	}
	if start.Digest().String() != a.StartDigest {
		return nil, fmt.Errorf("%w: start term does not match its digest", ErrFormat)
	}
	cd, err := configDigest(a.Config)
	if err != nil {
		return nil, fmt.Errorf("%w: %v", ErrFormat, err)
	}
	prev := genesis(a.StartDigest, cd)
	for i, e := range a.Entries {
		if e.Seq != i {
			return nil, fmt.Errorf("%w: entry %d carries sequence number %d", ErrFormat, i, e.Seq)
		}
		if e.Decision != "allow" && e.Decision != "deny" {
			return nil, fmt.Errorf("%w: entry %d decision %q", ErrFormat, i, e.Decision)
		}
		if want := link(prev, e); e.Link != want {
			return nil, fmt.Errorf("%w: entry %d", ErrChain, i)
		}
		prev = e.Link
	}
	if a.Head != prev {
		return nil, fmt.Errorf("%w: head", ErrChain)
	}
	if opt.Fuel != 0 && a.Fuel != opt.Fuel {
		return nil, fmt.Errorf("%w: stated fuel %d, expected %d", ErrStatus, a.Fuel, opt.Fuel)
	}
	return start, nil
}

// CheckLog verifies the chain and the log's own bookkeeping and replays
// nothing. It establishes that the log is intact, not that its decisions are
// right.
func CheckLog(a Audit, opt Options) error {
	if _, err := common(a, opt); err != nil {
		return err
	}
	last := a.StartDigest
	var allowed uint64
	for i, e := range a.Entries {
		if allowed >= a.Fuel {
			return fmt.Errorf("%w: entry %d follows the last permitted step of the budget", ErrStatus, i)
		}
		if e.Decision == "allow" {
			allowed++
		}
		last = e.After
	}
	if a.FinalDigest != last {
		return fmt.Errorf("%w: final digest is not the last entry's", ErrFinal)
	}
	fin, err := term.Parse(a.Final)
	if err != nil || fin.Digest().String() != a.FinalDigest {
		return fmt.Errorf("%w: final text does not match its digest", ErrFinal)
	}
	if allowed > a.Fuel || (a.Exhausted && allowed != a.Fuel) {
		return fmt.Errorf("%w: %d permitted steps, fuel %d, exhausted=%v", ErrStatus, allowed, a.Fuel, a.Exhausted)
	}
	return nil
}

// CheckReplay re-decides every entry against the policy, applies the
// permitted ones, and compares digests, status and, if asked, proposals.
func CheckReplay(a Audit, opt Options) error {
	start, err := common(a, opt)
	if err != nil {
		return err
	}
	pol, err := FromSpec(a.Config)
	if err != nil {
		return fmt.Errorf("%w: %v", ErrFormat, err)
	}
	strat, haveStrat := reduce.ParseStrategy(a.Strategy)
	if opt.RequireStrategy && !haveStrat {
		return fmt.Errorf("%w: unknown strategy %q", ErrFormat, a.Strategy)
	}
	for _, l := range start.Labels() {
		if _, ok := a.Config.Perm[l]; !ok {
			return fmt.Errorf("%w: label %q has no permission entry", ErrFormat, l)
		}
	}
	ev, w, flat := NewEvaluator(pol), NewWorker(), flatConfig(start)
	cur := start
	var accepted uint64
	var pending []Candidate
	var pi int
	refresh := func() {
		pending, pi = nil, 0
		if opt.RequireStrategy {
			w.Candidates(cur, strat, func(c Candidate) bool { pending = append(pending, c); return false })
		}
	}
	refresh()
	for i, e := range a.Entries {
		if accepted >= a.Fuel {
			return fmt.Errorf("%w: entry %d follows the budget", ErrStatus, i)
		}
		if opt.RequireStrategy {
			if pi >= len(pending) || pending[pi].Rule != e.Rule || string(pending[pi].Path) != e.Path {
				return fmt.Errorf("%w: entry %d (%s at %q)", ErrStrategy, i, e.Rule, e.Path)
			}
			pi++
		}
		d := ev.Decide(cur, e.Path, e.Rule)
		if (e.Decision == "allow") != d.Allow || e.Mask != d.Mask {
			return fmt.Errorf("%w: entry %d (%s at %q) logged %s with mask %s, policy says allow=%v mask %s",
				ErrDecision, i, e.Rule, e.Path, e.Decision, e.Mask, d.Allow, d.Mask)
		}
		if !d.Allow {
			if e.After != cur.Digest().String() {
				return fmt.Errorf("%w: refusal %d changes the term", ErrDigest, i)
			}
			continue
		}
		next, err := flat.Apply(cur, term.Path(e.Path), reduce.RuleID(e.Rule))
		if err != nil {
			return fmt.Errorf("%w: entry %d: %v", ErrApply, i, err)
		}
		if next.Digest().String() != e.After {
			return fmt.Errorf("%w: entry %d", ErrDigest, i)
		}
		cur = next
		accepted++
		refresh()
	}
	if cur.Digest().String() != a.FinalDigest || cur.String() != a.Final {
		return fmt.Errorf("%w: replay ends at %s", ErrFinal, cur.Digest().Short())
	}
	more := false
	NewWorker().Candidates(cur, reduce.LeftmostOutermost, func(c Candidate) bool {
		if ev.Decide(cur, string(c.Path), c.Rule).Allow {
			more = true
			return true
		}
		return false
	})
	if a.Exhausted != more {
		return fmt.Errorf("%w: claimed exhausted=%v but a permitted step available=%v", ErrStatus, a.Exhausted, more)
	}
	if accepted > a.Fuel || (a.Exhausted && accepted != a.Fuel) {
		return fmt.Errorf("%w: %d permitted steps, fuel %d", ErrStatus, accepted, a.Fuel)
	}
	if opt.RequireStrategy && accepted < a.Fuel && pi != len(pending) {
		return fmt.Errorf("%w: %d refusals after the last step are missing from the log", ErrStrategy, len(pending)-pi)
	}
	return nil
}
