package supervised

import (
	"github.com/standardgalactic/spherepop-kernel/reduce"
	"github.com/standardgalactic/spherepop-kernel/term"
)

// Candidate is a step the worker proposes: a rule whose shape matches at a path.
type Candidate struct {
	Path term.Path
	Rule string
}

// Worker proposes steps. It looks at shape only and never at permissions.
// Its memo records subterms with no matching shape anywhere, which is a fact
// about structure and so holds across steps.
type Worker struct {
	quiet map[term.Digest]struct{}
}

// NewWorker returns a worker with an empty memo.
func NewWorker() *Worker { return &Worker{quiet: map[term.Digest]struct{}{}} }

type walk struct {
	w          *Worker
	outer      bool
	rightFirst bool
	path       []byte
	count      int
	yield      func(Candidate) bool
}

// Candidates calls yield with every shape-matching step of t in the order the
// strategy considers them, until yield returns true.
func (w *Worker) Candidates(t *term.Term, strat reduce.Strategy, yield func(Candidate) bool) {
	s := &walk{w: w, yield: yield}
	s.outer = strat == reduce.LeftmostOutermost || strat == reduce.RightmostOutermost
	s.rightFirst = strat == reduce.RightmostOutermost || strat == reduce.RightmostInnermost
	s.visit(t)
}

func (s *walk) visit(t *term.Term) bool {
	if t.IsLeaf() {
		return false
	}
	if _, ok := s.w.quiet[t.Digest()]; ok {
		return false
	}
	before := s.count
	var stop bool
	if s.outer {
		stop = s.here(t) || s.kids(t)
	} else {
		stop = s.kids(t) || s.here(t)
	}
	if !stop && s.count == before {
		s.w.quiet[t.Digest()] = struct{}{}
	}
	return stop
}

func (s *walk) here(t *term.Term) bool {
	r := shape(t)
	if r == "" {
		return false
	}
	s.count++
	return s.yield(Candidate{Path: term.Path(s.path), Rule: r})
}

func (s *walk) down(step byte, t *term.Term) bool {
	s.path = append(s.path, step)
	stop := s.visit(t)
	s.path = s.path[:len(s.path)-1]
	return stop
}

func (s *walk) kids(t *term.Term) bool {
	switch t.Kind() {
	case term.KindApp:
		if s.rightFirst {
			return s.down(term.StepArg, t.Arg()) || s.down(term.StepFun, t.Fun())
		}
		return s.down(term.StepFun, t.Fun()) || s.down(term.StepArg, t.Arg())
	case term.KindBracket:
		return s.down(term.StepBody, t.Body())
	}
	return false
}
