package reduce

import (
	"math/rand"
	"os"
	"strconv"
	"testing"

	"github.com/standardgalactic/spherepop-kernel/term"
)

// The optimised search in find.go must agree exactly with the reference in
// ref_test.go: the same predicates, the same redexes, in the same order, with
// the same paths, under every strategy and every configuration. The shortcuts
// are claimed to be equivalences and not approximations, and this is the test
// of that claim.

var (
	allAbsorb = []Absorption{AbsOff, AbsAny, AbsNF, AbsS, AbsU}
	allScope  = []ScopeMode{ScAny, ScSafe, ScSettled}
	allStrats = []Strategy{LeftmostOutermost, LeftmostInnermost, RightmostInnermost, RightmostOutermost}
)

func randomConfig(rng *rand.Rand, labels []string) Config {
	c := DefaultConfig()
	c.Trace = false
	c.Root = PermSet(rng.Intn(16))
	c.Gated = PermSet(rng.Intn(16))
	c.Absorb = allAbsorb[rng.Intn(len(allAbsorb))]
	c.Sc = allScope[rng.Intn(len(allScope))]
	c.Perm = map[string]PermSet{}
	for _, l := range labels {
		c.Perm[l] = PermSet(rng.Intn(16))
	}
	return c
}

// compareSearch checks everything the optimisation touches for one term under
// one configuration.
func compareSearch(t *testing.T, c Config, tm *term.Term) {
	t.Helper()
	for _, st := range allStrats {
		got := c.Redexes(tm, st)
		want := refRedexes(&c, tm, st)
		if len(got) != len(want) {
			t.Fatalf("%s under %+v strategy %s: %d redexes, reference %d", tm, c.Spec(), st, len(got), len(want))
		}
		for i := range got {
			if got[i] != want[i] {
				t.Fatalf("%s under %+v strategy %s: redex %d is %v, reference %v", tm, c.Spec(), st, i, got[i], want[i])
			}
		}
	}
	s, r := newSession(&c), newRefSession(&c)
	var subs func(u *term.Term)
	subs = func(u *term.Term) {
		for m := PermSet(0); m < 16; m++ {
			if s.isRNormal(u, m) != r.isRNormal(u, m) {
				t.Fatalf("isRNormal(%s, %v) differs under %+v", u, m, c.Spec())
			}
			if s.isSettled(u, m) != r.isSettled(u, m) {
				t.Fatalf("isSettled(%s, %v) differs under %+v", u, m, c.Spec())
			}
			if s.absorbs(u, m) != r.absorbs(u, m) {
				t.Fatalf("absorbs(%s, %v) differs under %+v", u, m, c.Spec())
			}
			if s.scopes(u, m) != r.scopes(u, m) {
				t.Fatalf("scopes(%s, %v) differs under %+v", u, m, c.Spec())
			}
		}
		if s.isInsensitive(u) != r.isInsensitive(u) {
			t.Fatalf("isInsensitive(%s) differs under %+v", u, c.Spec())
		}
		switch u.Kind() {
		case term.KindApp:
			subs(u.Fun())
			subs(u.Arg())
		case term.KindBracket:
			subs(u.Body())
		}
	}
	subs(tm)
}

func TestSearchShortcutsEqualReferenceOnEnumeratedTerms(t *testing.T) {
	spec := searchSpec{leaves: 4, brackets: 2, labels: []string{"x", "y"}}
	if v, err := strconv.Atoi(os.Getenv("SPHEREPOP_SEARCH_LEAVES")); err == nil {
		spec.leaves = v
	}
	if os.Getenv("SPHEREPOP_SEARCH_LEAVES") == "" {
		spec.leaves = 3
	}
	for _, n := range []string{"a", "K", "C", "W", "S", "I", "B", "sc_x", "sc_y"} {
		spec.symbols = append(spec.symbols, sym(n))
	}
	rng := rand.New(rand.NewSource(99))
	count := 0
	for n := 1; n <= spec.leaves; n++ {
		spec.enumerate(n, spec.brackets, func(tm *term.Term) {
			count++
			// several random configurations per term, including every
			// absorption and scope mode, random gated sets and permissions
			for k := 0; k < 3; k++ {
				compareSearch(t, randomConfig(rng, []string{"x", "y"}), tm)
			}
		})
	}
	t.Logf("%d terms compared against the reference under 3 random configurations each", count)
}

func TestSearchShortcutsEqualReferenceOnRandomLargeTerms(t *testing.T) {
	rng := rand.New(rand.NewSource(123))
	leaves := []string{"a", "b", "S", "K", "I", "B", "C", "W", "sc_x", "sc_y", "Z"}
	var gen func(d int) *term.Term
	gen = func(d int) *term.Term {
		k := rng.Intn(10)
		if d == 0 || k < 2 {
			return sym(leaves[rng.Intn(len(leaves))])()
		}
		if k == 9 {
			return term.Bracket([]string{"x", "y"}[rng.Intn(2)], gen(d-1))
		}
		return term.App(gen(d-1), gen(d-1))
	}
	for n := 0; n < 3000; n++ {
		compareSearch(t, randomConfig(rng, []string{"x", "y"}), gen(2+rng.Intn(6)))
	}
}

// Whole runs, not only single searches: reducing with the optimised search
// follows the reference step for step.
func TestReductionPathsEqualReference(t *testing.T) {
	rng := rand.New(rand.NewSource(8))
	leaves := []string{"a", "b", "S", "K", "I", "B", "C", "W", "sc_x"}
	var gen func(d int) *term.Term
	gen = func(d int) *term.Term {
		k := rng.Intn(10)
		if d == 0 || k < 2 {
			return sym(leaves[rng.Intn(len(leaves))])()
		}
		if k == 9 {
			return term.Bracket("x", gen(d-1))
		}
		return term.App(gen(d-1), gen(d-1))
	}
	totalSteps := 0
	for n := 0; n < 600; n++ {
		c := randomConfig(rng, []string{"x", "y"})
		c.Trace = true
		cur := gen(2 + rng.Intn(5))
		st := allStrats[rng.Intn(4)]
		res, err := c.Reduce(cur, st, 60)
		if err != nil {
			t.Fatal(err)
		}
		totalSteps += len(res.Trace)
		at := cur
		for i, step := range res.Trace {
			ref := refRedexes(&c, at, st)
			if len(ref) == 0 || ref[0].Path != step.Path || ref[0].Rule != step.Rule {
				t.Fatalf("run %d step %d: optimised took %v at %q, reference %v", n, i, step.Rule, step.Path, ref)
			}
			at, err = c.Apply(at, step.Path, step.Rule)
			if err != nil {
				t.Fatal(err)
			}
		}
		if res.Steps < 60 && len(refRedexes(&c, at, st)) != 0 && !res.Exhausted {
			t.Fatalf("run %d stopped early", n)
		}
	}
	t.Logf("%d reduction steps compared with the reference", totalSteps)
	if totalSteps < 1000 {
		t.Fatalf("only %d steps were exercised", totalSteps)
	}
}
