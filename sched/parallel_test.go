package sched

import (
	"encoding/json"
	"fmt"
	"math/rand"
	"testing"

	"github.com/standardgalactic/spherepop-kernel/reduce"
	"github.com/standardgalactic/spherepop-kernel/term"
)

// randomWorld builds a world of several entities with random terms, some of
// which yield, and returns it together with the rearm terms to feed it.
func randomWorld(t *testing.T, rng *rand.Rand, cfg reduce.Config, strat reduce.Strategy, budget uint64) (*World, []string) {
	leaves := []string{"a", "b", "x", "S", "K", "I", "B", "C", "W", "yield", "yield", "K", "I"}
	var gen func(d int) string
	gen = func(d int) string {
		if d == 0 || rng.Intn(5) == 0 {
			return leaves[rng.Intn(len(leaves))]
		}
		return fmt.Sprintf("%s (%s)", gen(d-1), gen(d-1))
	}
	var in []Init
	for i := 0; i < 2+rng.Intn(7); i++ {
		in = append(in, Init{ID: fmt.Sprintf("e%02d", i), Term: term.MustParse(gen(1 + rng.Intn(5)))})
	}
	w, err := New(cfg, Policy{Strategy: strat, Budget: budget}, in)
	if err != nil {
		t.Fatal(err)
	}
	var re []string
	for i := 0; i < 8; i++ {
		re = append(re, gen(1+rng.Intn(4)))
	}
	return w, re
}

func logJSON(t *testing.T, w *World) string {
	b, err := json.Marshal(w.Log())
	if err != nil {
		t.Fatal(err)
	}
	return string(b)
}

// TestParallelTickGivesTheSameLogAsTick runs the same random worlds, with
// yields, resumptions and rearms, once sequentially and once on several
// workers, and requires the two logs to be byte-identical and both to verify.
func TestParallelTickGivesTheSameLogAsTick(t *testing.T) {
	cfg := HostConfig()
	rng := rand.New(rand.NewSource(11))
	resumedRuns, rearmed := 0, 0
	for n := 0; n < 150; n++ {
		strat := allStrategies[rng.Intn(len(allStrategies))]
		budget := []uint64{1, 2, 3, 5, 40}[rng.Intn(5)]
		seed := rng.Int63()
		build := func() (*World, []string, *rand.Rand) {
			r := rand.New(rand.NewSource(seed))
			w, re := randomWorld(t, r, cfg, strat, budget)
			return w, re, r
		}
		seq, re, r1 := build()
		par, _, _ := build()
		workers := 2 + int(seed%5)
		ticks := 4 + int(seed%9)
		for k := 0; k < ticks; k++ {
			// the same host input goes to both worlds before the same tick
			if r1.Intn(3) == 0 {
				id := fmt.Sprintf("e%02d", r1.Intn(len(seq.ents)))
				src := re[r1.Intn(len(re))]
				e1 := seq.Rearm(id, term.MustParse(src))
				e2 := par.Rearm(id, term.MustParse(src))
				if (e1 == nil) != (e2 == nil) {
					t.Fatalf("rearm disagrees: %v and %v", e1, e2)
				}
				if e1 == nil {
					rearmed++
				}
			}
			if err := seq.Tick(); err != nil {
				t.Fatal(err)
			}
			if err := par.TickParallel(workers); err != nil {
				t.Fatal(err)
			}
		}
		a, b := logJSON(t, seq), logJSON(t, par)
		if a != b {
			t.Fatalf("run %d: parallel log differs from sequential log (strategy %s, budget %d, %d workers)", n, strat, budget, workers)
		}
		if err := CheckLog(par.Log()); err != nil {
			t.Fatalf("run %d: %v", n, err)
		}
		for _, ev := range par.Log().Events {
			if ev.Resumed {
				resumedRuns++
				break
			}
		}
	}
	t.Logf("150 random worlds: logs identical; %d runs resumed at least once, %d rearms applied", resumedRuns, rearmed)
	if resumedRuns < 20 || rearmed < 50 {
		t.Fatalf("the comparison did not exercise resumption or rearming: %d, %d", resumedRuns, rearmed)
	}
}

func TestRunParallelAndDefaultWorkers(t *testing.T) {
	cfg := HostConfig()
	mk := func() *World {
		return world(t, cfg, 3, inits(t, "a", "S K K x", "b", "K x y", "c", "I (I (I a))", "d", "yield (K p q)"))
	}
	seq, par := mk(), mk()
	if err := seq.Run(6); err != nil {
		t.Fatal(err)
	}
	if err := par.RunParallel(6, 0); err != nil { // 0 means one worker per processor
		t.Fatal(err)
	}
	if logJSON(t, seq) != logJSON(t, par) {
		t.Fatal("RunParallel differs from Run")
	}
	empty, _ := New(cfg, Policy{Strategy: reduce.LeftmostOutermost, Budget: 1}, nil)
	if err := empty.TickParallel(4); err != nil {
		t.Fatal(err)
	}
}

// A tick that fails changes nothing: no events, no state, the same tick.
func TestFailedTickChangesNothing(t *testing.T) {
	cfg := HostConfig()
	w := world(t, cfg, 2, inits(t, "a", "W W W", "b", "W W W"))
	if err := w.Tick(); err != nil {
		t.Fatal(err)
	}
	before := logJSON(t, w)
	w.pol.Strategy = reduce.Strategy(200) // an invalid strategy makes every reduction fail
	if err := w.TickParallel(4); err == nil {
		t.Fatal("expected an error")
	}
	w.pol.Strategy = reduce.LeftmostOutermost
	if logJSON(t, w) != before {
		t.Fatal("failed tick changed the log")
	}
}

// A staged replacement is consumed by the tick that applies it: it is not
// applied again, and the entity can be rearmed once more.
func TestRearmIsConsumedByTheTickThatAppliesIt(t *testing.T) {
	for _, parallel := range []bool{false, true} {
		w := world(t, HostConfig(), 1, inits(t, "a", "W W W", "b", "W W W"))
		if err := w.Rearm("a", term.MustParse("K x y")); err != nil {
			t.Fatal(err)
		}
		tick := w.Tick
		if parallel {
			tick = func() error { return w.TickParallel(2) }
		}
		if err := tick(); err != nil {
			t.Fatal(err)
		}
		if err := w.Rearm("a", term.MustParse("I z")); err != nil {
			t.Fatalf("parallel=%v: entity cannot be rearmed after the tick that applied the first replacement: %v", parallel, err)
		}
		if err := tick(); err != nil {
			t.Fatal(err)
		}
		rearms := map[string]int{}
		for _, ev := range w.Log().Events {
			if ev.Rearm != nil {
				rearms[ev.Entity]++
			}
		}
		if rearms["a"] != 2 || rearms["b"] != 0 {
			t.Fatalf("parallel=%v: rearm events %v, want a:2 b:0", parallel, rearms)
		}
	}
}
