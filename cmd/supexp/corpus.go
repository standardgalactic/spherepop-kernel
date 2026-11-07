package main

import (
	"fmt"
	"math/rand"

	"github.com/standardgalactic/spherepop-kernel/reduce"
	"github.com/standardgalactic/spherepop-kernel/term"
)

type namedConfig struct {
	name string
	spec reduce.ConfigSpec
	cfg  reduce.Config
}

var absorbModes = []reduce.Absorption{reduce.AbsOff, reduce.AbsAny, reduce.AbsNF, reduce.AbsS, reduce.AbsU}
var scopeModes = []reduce.ScopeMode{reduce.ScAny, reduce.ScSafe, reduce.ScSettled}

// configs returns the 45 configurations of the corpus: three permission
// structures, five absorption modes and three scope modes, over the labels
// p, q and r.
func configs() []namedConfig {
	const wkc = reduce.PermW | reduce.PermK | reduce.PermC
	structures := []struct {
		name  string
		root  reduce.PermSet
		gated reduce.PermSet
		perm  map[string]reduce.PermSet
	}{
		// Labels restrict the root permission: the case in which Sc is unsafe.
		{"restrict", wkc, wkc, map[string]reduce.PermSet{"p": reduce.PermK | reduce.PermC, "q": reduce.PermW, "r": 0}},
		// The root permission lies inside every label's permission.
		{"contained", reduce.PermW, wkc, map[string]reduce.PermSet{"p": reduce.PermAll, "q": reduce.PermW | reduce.PermK, "r": reduce.PermW | reduce.PermC}},
		// S is gated as well.
		{"gatedS", reduce.PermAll, reduce.PermAll, map[string]reduce.PermSet{"p": reduce.PermS | reduce.PermK, "q": reduce.PermS | reduce.PermW | reduce.PermC, "r": reduce.PermS}},
	}
	var out []namedConfig
	for _, st := range structures {
		for _, a := range absorbModes {
			for _, s := range scopeModes {
				c := reduce.Config{Root: st.root, Gated: st.gated, Perm: st.perm, Absorb: a, Sc: s}
				out = append(out, namedConfig{fmt.Sprintf("%s/%s/%s", st.name, a, s), c.Spec(), c})
			}
		}
	}
	return out
}

var strategies = []reduce.Strategy{reduce.LeftmostOutermost, reduce.LeftmostInnermost, reduce.RightmostInnermost, reduce.RightmostOutermost}

var handSources = []string{
	"K a b", "W K a", "C K a b", "S K K a", "I a", "B K I a b",
	"<K a b>_p", "<W K a>_q", "<K a>_p b", "<W K a>_q (K c d)",
	"sc_p (K a b)", "sc_q (W K a)", "sc_r a", "<sc_p (K a b)>_q",
	"<<K a b>_q>_p (K c d)", "<K a b>_p (W K z)", "W I (W I)", "K a (W I (W I))",
	"<K>_p a b", "<K a>_p (K b c)", "sc_p <K a b>_q", "sc_q (sc_p (K a b))",
	"<S K K>_p (K a b)", "<W K>_q <K a b>_p", "C (<K a>_p) b c",
	"S (<K>_p) (<I>_q) a", "<I (K a b)>_r (I c)",
}

func handTerms() []*term.Term {
	out := make([]*term.Term, len(handSources))
	for i, s := range handSources {
		out[i] = term.MustParse(s)
	}
	return out
}

var leaves = []func() *term.Term{
	func() *term.Term { return term.Atom("a") }, func() *term.Term { return term.Atom("b") },
	func() *term.Term { return term.Atom("c") },
	func() *term.Term { return term.Const("S") }, func() *term.Term { return term.Const("K") },
	func() *term.Term { return term.Const("I") }, func() *term.Term { return term.Const("B") },
	func() *term.Term { return term.Const("C") }, func() *term.Term { return term.Const("W") },
	func() *term.Term { return term.Scope("p") }, func() *term.Term { return term.Scope("q") },
	func() *term.Term { return term.Scope("r") },
}

var labels = []string{"p", "q", "r"}

func randomTerm(rng *rand.Rand, depth int) *term.Term {
	if depth <= 0 || rng.Intn(6) == 0 {
		return leaves[rng.Intn(len(leaves))]()
	}
	if rng.Intn(5) == 0 {
		return term.Bracket(labels[rng.Intn(len(labels))], randomTerm(rng, depth-1))
	}
	return term.App(randomTerm(rng, depth-1), randomTerm(rng, depth-1))
}

func randomTerms(seed int64, n, depth int) []*term.Term {
	rng := rand.New(rand.NewSource(seed))
	out := make([]*term.Term, n)
	for i := range out {
		out[i] = randomTerm(rng, depth)
	}
	return out
}
