package reduce

import (
	"context"
	"math/bits"
	"runtime"
	"sync"
	"sync/atomic"

	"github.com/standardgalactic/spherepop-kernel/term"
)

// RootContained reports whether the root permission is contained in the
// permission of every label in the configuration. When it is not, unrestricted
// absorption (mode any) and the unrestricted scope constructor are not
// confluent (Theorem 4.2 of the source essay, with the counterexamples of
// SPEC.md section 17). The converse is not claimed: containment is necessary
// for those two rules to be confluent and is not shown to be sufficient.
func (c *Config) RootContained() bool {
	for _, p := range c.Perm {
		if c.Root&^p&PermAll != 0 {
			return false
		}
	}
	return true
}

// CapGraph is the permission automaton of a configuration. A state is a
// permission set, one of the sixteen subsets of {W,K,C,S}. Entering a bracket
// labelled l moves from state m to m intersected with the permission of l. The
// graph records, for each state, which states can be reached by entering zero
// or more brackets. Because intersection never adds a permission, every
// reachable state is a subset of the state it came from, and the whole
// relation fits in sixteen 16-bit words.
type CapGraph struct {
	root    PermSet
	reach   [16]uint16 // reach[m] has bit m' set when m' is reachable from m
	step    [16]uint16 // one bracket entry
	labels  int
	contain bool
}

// BuildCapGraph computes the permission automaton of c.
func (c *Config) BuildCapGraph() CapGraph {
	g := CapGraph{root: c.Root & PermAll, labels: len(c.Perm), contain: c.RootContained()}
	var masks uint16 // set of distinct label permissions, one bit per mask value
	for _, p := range c.Perm {
		masks |= 1 << (p & PermAll)
	}
	for m := 0; m < 16; m++ {
		g.step[m] = 1 << uint(m) // reflexive: staying put is zero bracket entries
		for rest := masks; rest != 0; rest &= rest - 1 {
			l := bits.TrailingZeros16(rest)
			g.step[m] |= 1 << uint(m&l)
		}
		g.reach[m] = g.step[m]
	}
	// Warshall closure over the sixteen states.
	for k := 0; k < 16; k++ {
		for i := 0; i < 16; i++ {
			if g.reach[i]&(1<<uint(k)) != 0 {
				g.reach[i] |= g.reach[k]
			}
		}
	}
	return g
}

// Reachable returns the set of states reachable from m, as a mask with bit s
// set when state s is reachable.
func (g CapGraph) Reachable(m PermSet) uint16 { return g.reach[m&PermAll] }

// CanReach reports whether state to can be in force somewhere below a position
// where state from is in force.
func (g CapGraph) CanReach(from, to PermSet) bool {
	return g.reach[from&PermAll]&(1<<uint(to&PermAll)) != 0
}

// States returns the permission sets that can be in force anywhere in a term
// run from the root, in increasing numeric order.
func (g CapGraph) States() []PermSet {
	var out []PermSet
	for s := PermSet(0); s < 16; s++ {
		if g.CanReach(g.root, s) {
			out = append(out, s)
		}
	}
	return out
}

// Contained reports RootContained for the configuration the graph was built
// from.
func (g CapGraph) Contained() bool { return g.contain }

// Dropped returns the permissions that are in src and not in dst.
func Dropped(src, dst PermSet) PermSet { return src &^ dst & PermAll }

// ReduceBatch reduces independent terms on a pool of workers and returns the
// results in input order. Each reduction is an ordinary Reduce, which reads
// the configuration and shares nothing with the others, so the results equal
// those of reducing the terms one after another. workers below one means one
// worker per processor. When reductions fail, the error of the lowest
// numbered failing term is returned and no results are.
func (c *Config) ReduceBatch(ctx context.Context, terms []*term.Term, strat Strategy, fuel uint64, workers int) ([]Result, error) {
	n := len(terms)
	if n == 0 {
		return nil, nil
	}
	if workers < 1 {
		workers = runtime.GOMAXPROCS(0)
	}
	if workers > n {
		workers = n
	}
	results := make([]Result, n)
	errs := make([]error, n)
	var next atomic.Int64
	var wg sync.WaitGroup
	for k := 0; k < workers; k++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			for {
				i := int(next.Add(1)) - 1
				if i >= n {
					return
				}
				if err := ctx.Err(); err != nil {
					errs[i] = err
					continue
				}
				results[i], errs[i] = c.Reduce(terms[i], strat, fuel)
			}
		}()
	}
	wg.Wait()
	for _, err := range errs {
		if err != nil {
			return nil, err
		}
	}
	return results, nil
}
