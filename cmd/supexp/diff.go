package main

import (
	"fmt"

	"github.com/standardgalactic/spherepop-kernel/reduce"
	"github.com/standardgalactic/spherepop-kernel/supervised"
	"github.com/standardgalactic/spherepop-kernel/term"
	"github.com/standardgalactic/spherepop-kernel/trace"
)

const diffFuel = 60

func corpusTerms(seed int64, n, depth int) []*term.Term {
	return append(handTerms(), randomTerms(seed, n, depth)...)
}

// offered lists the steps the supervised design would take from t: the
// worker's proposals, in strategy order, that the policy allows.
func offered(spec reduce.ConfigSpec, t *term.Term, st reduce.Strategy) ([]reduce.Redex, error) {
	pol, err := supervised.FromSpec(spec)
	if err != nil {
		return nil, err
	}
	ev := supervised.NewEvaluator(pol)
	var out []reduce.Redex
	supervised.NewWorker().Candidates(t, st, func(c supervised.Candidate) bool {
		if ev.Decide(t, string(c.Path), c.Rule).Allow {
			out = append(out, reduce.Redex{Path: c.Path, Rule: reduce.RuleID(c.Rule)})
		}
		return false
	})
	return out, nil
}

func sameRedexes(a, b []reduce.Redex) bool {
	if len(a) != len(b) {
		return false
	}
	for i := range a {
		if a[i] != b[i] {
			return false
		}
	}
	return true
}

func runDiff() error {
	cfgs, terms := configs(), corpusTerms(1, 1000, 5)
	var runs, accepted, refused, outcomeDiff, states, stateDiff, honestRejected int
	for _, nc := range cfgs {
		cfg := nc.cfg
		cfg.Trace = true
		for _, start := range terms {
			for _, st := range strategies {
				runs++
				want, err := cfg.Reduce(start, st, diffFuel)
				if err != nil {
					return err
				}
				got, audit, err := supervised.Run(nc.spec, start, st, diffFuel)
				if err != nil {
					return err
				}
				accepted += int(got.Steps)
				refused += int(got.Refused)
				// Same outcome and same accepted steps, in order.
				var steps []supervised.Entry
				for _, e := range audit.Entries {
					if e.Decision == "allow" {
						steps = append(steps, e)
					}
				}
				same := got.Steps == want.Steps && got.Exhausted == want.Exhausted && term.Equal(got.Term, want.Term) && len(steps) == len(want.Trace)
				for i := 0; same && i < len(steps); i++ {
					same = steps[i].Rule == string(want.Trace[i].Rule) && steps[i].Path == string(want.Trace[i].Path)
				}
				if !same {
					outcomeDiff++
				}
				// Same offered steps at every state of the run.
				cur := start
				for i := 0; i <= len(want.Trace); i++ {
					states++
					a := cfg.Redexes(cur, st)
					b, err := offered(nc.spec, cur, st)
					if err != nil {
						return err
					}
					if !sameRedexes(a, b) {
						stateDiff++
					}
					if i < len(want.Trace) {
						if cur, err = cfg.Apply(cur, want.Trace[i].Path, want.Trace[i].Rule); err != nil {
							return err
						}
					}
				}
				// Honest records are accepted by every checker.
				doc, err := trace.Build(cfg, start, st, diffFuel, want)
				if err != nil {
					return err
				}
				strict := supervised.Options{RequireStrategy: true, Fuel: diffFuel}
				if _, err := trace.Check(doc, trace.Options{RequireStrategy: true, Fuel: diffFuel}); err != nil ||
					supervised.CheckLog(audit, strict) != nil || supervised.CheckReplay(audit, strict) != nil {
					honestRejected++
				}
			}
		}
	}
	fmt.Println("differential run")
	fmt.Printf("  configurations: %d, terms: %d (%d hand-chosen, 1000 random of depth 5, seed 1), strategies: %d, fuel: %d\n",
		len(cfgs), len(terms), len(handSources), len(strategies), diffFuel)
	fmt.Printf("  runs: %d, accepted steps in the supervised runs: %d, refused proposals: %d\n", runs, accepted, refused)
	fmt.Printf("  runs whose outcome or step sequence differs between the designs: %d\n", outcomeDiff)
	fmt.Printf("  states compared: %d, states where the offered step lists differ: %d\n", states, stateDiff)
	fmt.Printf("  honest records rejected by a checker that should accept them: %d\n", honestRejected)
	return nil
}

// runDiffControl shows that the differential can fail. The supervisor's
// policy is given a deliberate error, it reads absorption mode s as nf, and
// the runs under mode s are compared again.
func runDiffControl(seed int64, n, depth int, fuel uint64) error {
	terms := corpusTerms(seed, n, depth)
	var runs, differ int
	for _, nc := range configs() {
		if nc.cfg.Absorb != reduce.AbsS {
			continue
		}
		wrong := nc.spec
		wrong.Absorb = "nf"
		for _, start := range terms {
			for _, st := range strategies {
				runs++
				want, err := nc.cfg.Reduce(start, st, fuel)
				if err != nil {
					return err
				}
				got, _, err := supervised.Run(wrong, start, st, fuel)
				if err != nil {
					return err
				}
				if got.Steps != want.Steps || got.Exhausted != want.Exhausted || !term.Equal(got.Term, want.Term) {
					differ++
				}
			}
		}
	}
	fmt.Printf("positive control: supervisor policy reads absorption mode s as nf, %d runs, %d differ\n", runs, differ)
	return nil
}
