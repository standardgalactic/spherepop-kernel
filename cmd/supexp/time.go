package main

import (
	"fmt"
	"sort"
	"time"

	"github.com/standardgalactic/spherepop-kernel/reduce"
	"github.com/standardgalactic/spherepop-kernel/supervised"
	"github.com/standardgalactic/spherepop-kernel/term"
	"github.com/standardgalactic/spherepop-kernel/trace"
)

const reps = 9

func median(d []time.Duration) time.Duration {
	sort.Slice(d, func(i, j int) bool { return d[i] < d[j] })
	return d[len(d)/2]
}

func perStep(d time.Duration, steps uint64) float64 {
	return float64(d.Nanoseconds()) / float64(steps) / 1000
}

type workload struct {
	name  string
	src   string
	cfg   reduce.Config
	strat reduce.Strategy
	fuel  uint64
}

func runTime() error {
	omega := "W I (W I)"
	// M = S (W I) I, so M M reduces to M M M and the term keeps growing.
	m := "(S (W I) I)"
	forbidK := reduce.Config{Root: reduce.PermW, Gated: reduce.PermW | reduce.PermK | reduce.PermC, Absorb: reduce.AbsU}
	open := reduce.DefaultConfig()
	loads := []workload{
		{"omega loop, no refusals", omega, open, reduce.RightmostInnermost, 20000},
		{"omega loop beside a forbidden K, refused every step", "(" + omega + ") (K a b)", forbidK, reduce.RightmostInnermost, 20000},
		{"M M, growing term", m + " " + m, open, reduce.LeftmostOutermost, 400},
	}
	fmt.Printf("time per accepted step (median of %d repetitions, one core, microseconds)\n", reps)
	for _, w := range loads {
		start := term.MustParse(w.src)
		spec := w.cfg.Spec()
		var scoped, sup, ct, cl, cr []time.Duration
		var res reduce.Result
		var sres supervised.Result
		var doc trace.Document
		var audit supervised.Audit
		for i := 0; i < reps; i++ {
			t0 := time.Now()
			var err error
			res, doc, err = trace.Record(w.cfg, start, w.strat, w.fuel)
			if err != nil {
				return err
			}
			scoped = append(scoped, time.Since(t0))
			t0 = time.Now()
			if sres, audit, err = supervised.Run(spec, start, w.strat, w.fuel); err != nil {
				return err
			}
			sup = append(sup, time.Since(t0))
			opt := supervised.Options{Fuel: w.fuel}
			t0 = time.Now()
			if _, err = trace.Check(doc, trace.Options{Fuel: w.fuel}); err != nil {
				return err
			}
			ct = append(ct, time.Since(t0))
			t0 = time.Now()
			if err = supervised.CheckLog(audit, opt); err != nil {
				return err
			}
			cl = append(cl, time.Since(t0))
			t0 = time.Now()
			if err = supervised.CheckReplay(audit, opt); err != nil {
				return err
			}
			cr = append(cr, time.Since(t0))
		}
		fmt.Printf("  %s\n", w.name)
		fmt.Printf("    steps %d (scoped) %d (supervised), refused proposals %d, audit entries %d against %d trace steps\n",
			res.Steps, sres.Steps, sres.Refused, len(audit.Entries), len(doc.Steps))
		fmt.Printf("    run:   scoped %.2f, supervised %.2f\n", perStep(median(scoped), res.Steps), perStep(median(sup), sres.Steps))
		fmt.Printf("    check: trace.Check %.2f, CheckLog %.2f, CheckReplay %.2f\n",
			perStep(median(ct), res.Steps), perStep(median(cl), res.Steps), perStep(median(cr), res.Steps))
	}
	return nil
}
