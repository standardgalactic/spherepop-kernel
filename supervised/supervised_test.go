package supervised

import (
	"errors"
	"testing"

	"github.com/standardgalactic/spherepop-kernel/reduce"
	"github.com/standardgalactic/spherepop-kernel/term"
)

var testTerms = []string{
	"K a b", "W K a", "<K a b>_p", "<W K a>_q c", "<K a b>_p (W K z)",
	"sc_p (K a b)", "sc_q (W K a)", "<<K a b>_q>_p (K c d)", "C K a b", "S K K <W K a>_r",
}

func testSpec() reduce.ConfigSpec {
	c := reduce.Config{
		Root:   reduce.PermW | reduce.PermK | reduce.PermC,
		Perm:   map[string]reduce.PermSet{"p": reduce.PermK | reduce.PermC, "q": reduce.PermW, "r": 0},
		Gated:  reduce.PermW | reduce.PermK | reduce.PermC,
		Absorb: reduce.AbsS,
		Sc:     reduce.ScSettled,
	}
	return c.Spec()
}

func TestAgreesWithReducerOnSmallTerms(t *testing.T) {
	spec := testSpec()
	cfg, err := spec.Config()
	if err != nil {
		t.Fatal(err)
	}
	for _, src := range testTerms {
		start := term.MustParse(src)
		for _, st := range []reduce.Strategy{reduce.LeftmostOutermost, reduce.LeftmostInnermost, reduce.RightmostInnermost, reduce.RightmostOutermost} {
			want, err := cfg.Reduce(start, st, 40)
			if err != nil {
				t.Fatal(err)
			}
			got, audit, err := Run(spec, start, st, 40)
			if err != nil {
				t.Fatal(err)
			}
			if got.Steps != want.Steps || got.Exhausted != want.Exhausted || !term.Equal(got.Term, want.Term) {
				t.Fatalf("%s under %s: supervised %s (%d steps, exhausted %v), reducer %s (%d, %v)",
					src, st, got.Term, got.Steps, got.Exhausted, want.Term, want.Steps, want.Exhausted)
			}
			for _, o := range []Options{{}, {RequireStrategy: true, Fuel: 40}} {
				if err := CheckLog(audit, o); err != nil {
					t.Fatalf("%s under %s: CheckLog: %v", src, st, err)
				}
				if err := CheckReplay(audit, o); err != nil {
					t.Fatalf("%s under %s: CheckReplay %+v: %v", src, st, o, err)
				}
			}
		}
	}
}

func TestReplayRejectsAForbiddenStepThatTheLogCalledAllowed(t *testing.T) {
	spec := testSpec()
	start := term.MustParse("<K a b>_q")
	_, audit, err := Run(spec, start, reduce.LeftmostOutermost, 10)
	if err != nil {
		t.Fatal(err)
	}
	if len(audit.Entries) != 1 || audit.Entries[0].Decision != "deny" {
		t.Fatalf("want one refusal, got %+v", audit.Entries)
	}
	flat := flatConfig(start)
	next, err := flat.Apply(start, term.Path("B"), reduce.RuleK)
	if err != nil {
		t.Fatal(err)
	}
	forged := audit
	e := &forged.Entries[0]
	e.Decision, e.After = "allow", next.Digest().String()
	forged.Final, forged.FinalDigest = next.String(), next.Digest().String()
	if err := Seal(&forged); err != nil {
		t.Fatal(err)
	}
	if err := CheckLog(forged, Options{}); err != nil {
		t.Fatalf("a log-only check should accept the forgery, got %v", err)
	}
	if err := CheckReplay(forged, Options{}); !errors.Is(err, ErrDecision) {
		t.Fatalf("replay should reject with ErrDecision, got %v", err)
	}
}

func TestOmittedRefusalNeedsStrategyReplay(t *testing.T) {
	spec := testSpec()
	start := term.MustParse("<K a b>_q (W K z)")
	_, audit, err := Run(spec, start, reduce.LeftmostOutermost, 10)
	if err != nil {
		t.Fatal(err)
	}
	cut := audit
	cut.Entries = append([]Entry{}, audit.Entries[1:]...)
	for i := range cut.Entries {
		cut.Entries[i].Seq = i
	}
	if err := Seal(&cut); err != nil {
		t.Fatal(err)
	}
	if err := CheckReplay(cut, Options{}); err != nil {
		t.Fatalf("without the strategy the omission is invisible, got %v", err)
	}
	if err := CheckReplay(cut, Options{RequireStrategy: true}); !errors.Is(err, ErrStrategy) {
		t.Fatalf("strategy replay should reject, got %v", err)
	}
}
