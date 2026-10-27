// Package viz maps reduction steps onto three display parameters and serves
// them over plain net/http. The map is a pure function of the step, so what a
// viewer should show for a step can be computed without a browser, checked in
// a test, and reproduced by any other implementation from the numbers below.
//
// All values are integers. The projection involves no floating point, so two
// implementations cannot disagree in the last digit.
//
// The assignment of hues to rules is conventional. It is a table and is not
// derived from anything about the rules; a viewer that wants other colors
// changes the table and nothing else.
package viz

import (
	"encoding/json"
	"fmt"
	"hash/fnv"
	"math/bits"
	"net/http"

	"github.com/standardgalactic/spherepop-kernel/reduce"
	"github.com/standardgalactic/spherepop-kernel/term"
)

// ComplexitySaturation is the number of application circles at which
// complexity reaches its maximum of 1000.
const ComplexitySaturation = 64

// IntensityMin and IntensityMax bound intensity, in thousandths.
const (
	IntensityMin = 150
	IntensityMax = 1000
)

// Event is what the projection reads from one step.
type Event struct {
	Rule     reduce.RuleID  `json:"rule"`
	Perm     reduce.PermSet `json:"perm"`      // permission in force at the redex
	TermSize int            `json:"term_size"` // application circles in the term after the step
	Digest   string         `json:"digest"`    // digest of the term after the step
}

// State is the projection of an Event.
type State struct {
	Event      Event `json:"event"`
	Hue        int   `json:"hue"`        // degrees, 0 to 359
	Intensity  int   `json:"intensity"`  // thousandths, IntensityMin to IntensityMax
	Complexity int   `json:"complexity"` // thousandths, 0 to 1000
}

var hues = map[reduce.RuleID]int{
	reduce.RuleI:   174,
	reduce.RuleK:   330,
	reduce.RuleS:   145,
	reduce.RuleB:   48,
	reduce.RuleC:   28,
	reduce.RuleW:   275,
	reduce.RuleSc:  195,
	reduce.RuleAbs: 120,
}

// hueOf returns the table hue of a rule, and for a rule that is not in the
// table the FNV-1a 32 bit hash of its name modulo 360.
func hueOf(r reduce.RuleID) int {
	if h, ok := hues[r]; ok {
		return h
	}
	f := fnv.New32a()
	f.Write([]byte(r))
	return int(f.Sum32() % 360)
}

// intensityOf scales with the number of permissions in force. With n of the
// four permissions held it is 150 + 850*n/4 thousandths, rounded half up, so an
// empty permission gives 150 and a full one gives 1000.
func intensityOf(p reduce.PermSet) int {
	n := bits.OnesCount8(uint8(p & reduce.PermAll))
	return (4*IntensityMin + 850*n + 2) / 4
}

// complexityOf rises linearly with the term size and saturates.
func complexityOf(size int) int {
	if size < 0 {
		size = 0
	}
	if size >= ComplexitySaturation {
		return 1000
	}
	return size * 1000 / ComplexitySaturation
}

// Map projects an event. It is deterministic and has no side effects.
func Map(ev Event) State {
	if ev.TermSize < 0 {
		ev.TermSize = 0
	}
	return State{
		Event:      ev,
		Hue:        hueOf(ev.Rule),
		Intensity:  intensityOf(ev.Perm),
		Complexity: complexityOf(ev.TermSize),
	}
}

// FromRun reduces t under c one step at a time, up to fuel steps, and returns
// the event of every step in order. The reducer is the only authority on which
// step is taken and what it does; this function only observes.
func FromRun(c reduce.Config, t *term.Term, strat reduce.Strategy, fuel uint64) ([]Event, error) {
	c.Trace = true
	var out []Event
	cur := t
	for i := uint64(0); i < fuel; i++ {
		res, err := c.Reduce(cur, strat, 1)
		if err != nil {
			return out, err
		}
		if len(res.Trace) == 0 {
			break
		}
		st := res.Trace[0]
		perm, err := c.EffectivePerm(cur, st.Path)
		if err != nil {
			return out, err
		}
		out = append(out, Event{Rule: st.Rule, Perm: perm, TermSize: res.Term.Size(), Digest: st.After.String()})
		cur = res.Term
	}
	return out, nil
}

// Project maps every event.
func Project(evs []Event) []State {
	out := make([]State, len(evs))
	for i, e := range evs {
		out[i] = Map(e)
	}
	return out
}

// Handler serves a fixed sequence of states:
//
//	GET /states   the whole sequence as a JSON array
//	GET /state    the last state, or the one at ?i=N
//	GET /events   the sequence as server-sent events, one per state, then close
//
// The responses depend only on the states given, so the same run always gives
// byte-identical output.
func Handler(states []State) http.Handler {
	mux := http.NewServeMux()
	mux.HandleFunc("/states", func(w http.ResponseWriter, r *http.Request) {
		w.Header().Set("Content-Type", "application/json")
		json.NewEncoder(w).Encode(states)
	})
	mux.HandleFunc("/state", func(w http.ResponseWriter, r *http.Request) {
		if len(states) == 0 {
			http.Error(w, "no steps", http.StatusNotFound)
			return
		}
		i := len(states) - 1
		if q := r.URL.Query().Get("i"); q != "" {
			var n int
			if _, err := fmt.Sscanf(q, "%d", &n); err != nil || n < 0 || n >= len(states) || fmt.Sprint(n) != q {
				http.Error(w, "step index out of range", http.StatusBadRequest)
				return
			}
			i = n
		}
		w.Header().Set("Content-Type", "application/json")
		json.NewEncoder(w).Encode(states[i])
	})
	mux.HandleFunc("/events", func(w http.ResponseWriter, r *http.Request) {
		w.Header().Set("Content-Type", "text/event-stream")
		w.Header().Set("Cache-Control", "no-cache")
		for i, s := range states {
			b, _ := json.Marshal(s)
			fmt.Fprintf(w, "id: %d\nevent: step\ndata: %s\n\n", i, b)
		}
		if f, ok := w.(http.Flusher); ok {
			f.Flush()
		}
	})
	return mux
}
