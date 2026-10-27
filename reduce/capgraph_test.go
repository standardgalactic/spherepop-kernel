package reduce

import (
	"context"
	"math/rand"
	"testing"

	"github.com/standardgalactic/spherepop-kernel/term"
)

// bruteReach explores the automaton one state at a time.
func bruteReach(c Config, from PermSet) map[PermSet]bool {
	seen := map[PermSet]bool{from & PermAll: true}
	queue := []PermSet{from & PermAll}
	for len(queue) > 0 {
		m := queue[0]
		queue = queue[1:]
		for _, p := range c.Perm {
			n := m & p & PermAll
			if !seen[n] {
				seen[n] = true
				queue = append(queue, n)
			}
		}
	}
	return seen
}

func TestCapGraphAgreesWithBreadthFirstSearch(t *testing.T) {
	rng := rand.New(rand.NewSource(5))
	for n := 0; n < 400; n++ {
		c := DefaultConfig()
		c.Root = PermSet(rng.Intn(16))
		c.Perm = map[string]PermSet{}
		for i := 0; i < rng.Intn(5); i++ {
			c.Perm[string(rune('a'+i))] = PermSet(rng.Intn(16))
		}
		g := c.BuildCapGraph()
		for from := PermSet(0); from < 16; from++ {
			want := bruteReach(c, from)
			for to := PermSet(0); to < 16; to++ {
				if g.CanReach(from, to) != want[to] {
					t.Fatalf("config %v: reach %v -> %v: graph %v, search %v", c.Perm, from, to, g.CanReach(from, to), want[to])
				}
			}
			if bits := popcount16(g.Reachable(from)); bits != len(want) {
				t.Fatalf("Reachable(%v) has %d states, search found %d", from, bits, len(want))
			}
		}
		// every reachable state is a subset of the root, so permissions only narrow
		for _, s := range g.States() {
			if s&^(c.Root&PermAll) != 0 {
				t.Fatalf("state %v is not a subset of root %v", s, c.Root)
			}
		}
	}
}

func popcount16(x uint16) int {
	n := 0
	for ; x != 0; x &= x - 1 {
		n++
	}
	return n
}

func TestRootContainedMatchesDefinition(t *testing.T) {
	c := DefaultConfig()
	c.Perm = map[string]PermSet{}
	if !c.RootContained() {
		t.Error("no labels: contained")
	}
	c.Perm = map[string]PermSet{"x": PermAll}
	if !c.RootContained() || !c.BuildCapGraph().Contained() {
		t.Error("label with the full alphabet: contained")
	}
	c.Perm = map[string]PermSet{"x": PermAll, "y": PermK | PermC}
	if c.RootContained() {
		t.Error("label missing W and S: not contained")
	}
	c.Root = PermK
	if !c.RootContained() {
		t.Error("root K inside both labels: contained")
	}
}

// The claim RootContained supports: when it fails, unrestricted absorption
// has a counterexample to confluence, here in its smallest form.
func TestRootNotContainedGoesWithTheAbsorptionCounterexample(t *testing.T) {
	c := DefaultConfig()
	c.Absorb = AbsAny
	c.Perm = map[string]PermSet{"x": PermC}
	if c.RootContained() {
		t.Fatal("setup: root is not contained")
	}
	nfs, ok := allNormalForms(&c, term.MustParse("<a>_x (K b c)"), 600, 40)
	if !ok || len(nfs) < 2 {
		t.Fatalf("expected two normal forms, got %d (complete %v)", len(nfs), ok)
	}
}

func TestReduceBatchEqualsSequentialAndKeepsOrder(t *testing.T) {
	c := DefaultConfig()
	var ts []*term.Term
	rng := rand.New(rand.NewSource(2))
	leaves := []string{"a", "b", "S", "K", "I", "B", "C", "W"}
	var gen func(d int) string
	gen = func(d int) string {
		if d == 0 || rng.Intn(4) == 0 {
			return leaves[rng.Intn(len(leaves))]
		}
		return "(" + gen(d-1) + ") (" + gen(d-1) + ")"
	}
	for i := 0; i < 200; i++ {
		ts = append(ts, term.MustParse(gen(4)))
	}
	got, err := c.ReduceBatch(context.Background(), ts, LeftmostOutermost, 200, 6)
	if err != nil {
		t.Fatal(err)
	}
	for i, tm := range ts {
		want, _ := c.Reduce(tm, LeftmostOutermost, 200)
		if got[i].Term.Digest() != want.Term.Digest() || got[i].Steps != want.Steps || got[i].Exhausted != want.Exhausted {
			t.Fatalf("term %d differs from the sequential result", i)
		}
	}
	if r, err := c.ReduceBatch(context.Background(), nil, LeftmostOutermost, 1, 0); r != nil || err != nil {
		t.Error("empty batch")
	}
	if _, err := c.ReduceBatch(context.Background(), ts, Strategy(99), 5, 0); err == nil {
		t.Error("invalid strategy accepted")
	}
	ctx, cancel := context.WithCancel(context.Background())
	cancel()
	if _, err := c.ReduceBatch(ctx, ts, LeftmostOutermost, 5, 4); err == nil {
		t.Error("cancelled context accepted")
	}
}
