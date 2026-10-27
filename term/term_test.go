package term

import (
	"errors"
	"testing"
)

func TestParsePrintRoundTrip(t *testing.T) {
	for _, src := range []string{
		"x", "S", "S K K x", "f (g x) y", "<K a b>_x", "<f>_x y", "sc_x (K a)",
		"f (<g (h x)>_ab1 y) z",
	} {
		a, err := Parse(src)
		if err != nil {
			t.Fatalf("%q: %v", src, err)
		}
		b, err := Parse(a.String())
		if err != nil || !Equal(a, b) {
			t.Fatalf("%q printed as %q does not round trip (%v)", src, a, err)
		}
	}
	if got := MustParse("((a b) c)").String(); got != "a b c" {
		t.Errorf("left association not canonical: %q", got)
	}
}

func TestParseErrors(t *testing.T) {
	for _, src := range []string{"", "(", ")", "a )", "<a>", "<a>_", "<a b", "Z", "sc_", "sc_x-y", "a $"} {
		_, err := Parse(src)
		var se *SyntaxError
		if !errors.As(err, &se) {
			t.Errorf("%q: want SyntaxError, got %v", src, err)
		}
	}
}

func TestDigestIsStructural(t *testing.T) {
	a := MustParse("f (g x)")
	b := App(Atom("f"), App(Atom("g"), Atom("x")))
	if a.Digest() != b.Digest() || !Equal(a, b) {
		t.Fatal("equal structures have different digests")
	}
	// Kind and label are part of the address.
	if Atom("K").Digest() == Const("K").Digest() {
		t.Error("atom and constant collide")
	}
	if Scope("x").Digest() == Bracket("x", Atom("a")).Digest() {
		t.Error("scope and bracket collide")
	}
	if Bracket("x", Atom("a")).Digest() == Bracket("y", Atom("a")).Digest() {
		t.Error("labels do not affect the digest")
	}
	// Application is not associative.
	if MustParse("a (b c)").Digest() == MustParse("a b c").Digest() {
		t.Error("application grouping ignored")
	}
}

func TestDigestStringRoundTrip(t *testing.T) {
	d := MustParse("S K K").Digest()
	back, err := ParseDigest(d.String())
	if err != nil || back != d {
		t.Fatalf("digest round trip failed: %v", err)
	}
	if _, err := ParseDigest("abcd"); err == nil {
		t.Error("short digest accepted")
	}
}

func TestSizeAndLeaves(t *testing.T) {
	x := MustParse("S K K x")
	if x.Size() != 3 || x.Leaves() != 4 {
		t.Errorf("size %d leaves %d", x.Size(), x.Leaves())
	}
	if MustParse("<K a b>_x").Size() != 2 {
		t.Error("bracket should add no circle")
	}
}

func TestSpine(t *testing.T) {
	h, args := MustParse("f a (g b) c").Spine()
	if h.Name() != "f" || len(args) != 3 || args[1].String() != "g b" {
		t.Fatalf("spine %s %v", h, args)
	}
	// A spine does not cross a bracket.
	h, n := MustParse("<f a>_x b").Head()
	if h.Kind() != KindBracket || n != 1 {
		t.Fatalf("head %s after %d", h, n)
	}
}

func TestPathsAndReplace(t *testing.T) {
	x := MustParse("f (<g a>_x b)")
	sub, err := x.At("RLB")
	if err != nil || sub.String() != "g a" {
		t.Fatalf("At: %v %v", sub, err)
	}
	y, err := x.Replace("RLB", Atom("z"))
	if err != nil || y.String() != "f (<z>_x b)" {
		t.Fatalf("Replace: %v %v", y, err)
	}
	if x.String() != "f (<g a>_x b)" {
		t.Error("Replace mutated its input")
	}
	// Sharing off the path.
	if y.Fun() != x.Fun() {
		t.Error("untouched sibling was rebuilt")
	}
	for _, p := range []Path{"B", "LLL", "RRR"} {
		if _, err := x.At(p); !errors.Is(err, ErrBadPath) {
			t.Errorf("At(%q): %v", p, err)
		}
		if _, err := x.Replace(p, Atom("z")); !errors.Is(err, ErrBadPath) {
			t.Errorf("Replace(%q): %v", p, err)
		}
	}
}

func TestSubstAndDefs(t *testing.T) {
	x := MustParse("f x (<x>_l x)")
	y := Subst(x, map[string]*Term{"x": MustParse("K a")})
	if y.String() != "f (K a) (<K a>_l (K a))" {
		t.Fatalf("subst %s", y)
	}
	if Subst(x, map[string]*Term{"q": Atom("r")}) != x {
		t.Error("unchanged subst should return the same node")
	}
	d, err := ParseWith("id a", Defs{"id": MustParse("S K K")})
	if err != nil || d.String() != "S K K a" {
		t.Fatalf("defs: %v %v", d, err)
	}
}

func TestDistinctNodesAndLabels(t *testing.T) {
	w := MustParse("S (S K K) (S K K)")
	if w.DistinctNodes() >= w.Size()+w.Leaves() {
		t.Errorf("sharing not detected: %d nodes", w.DistinctNodes())
	}
	got := MustParse("<a>_y (sc_x b) <c>_y").Labels()
	if len(got) != 2 || got[0] != "x" || got[1] != "y" {
		t.Errorf("labels %v", got)
	}
}

func TestSizeSaturates(t *testing.T) {
	x := Atom("a")
	for i := 0; i < 80; i++ {
		x = App(x, x) // doubles each time; shares memory
	}
	if x.Size() <= 0 || x.Leaves() <= 0 {
		t.Fatalf("size overflowed: %d %d", x.Size(), x.Leaves())
	}
}

func TestNumeralAtoms(t *testing.T) {
	x := MustParse("effect (door 3) open")
	if x.String() != "effect (door 3) open" {
		t.Fatalf("round trip %q", x)
	}
	n := MustParse("3")
	if n.Kind() != KindAtom || n.Name() != "3" {
		t.Fatalf("numeral should be an atom named 3: %v", n)
	}
	if MustParse("007").Digest() == MustParse("7").Digest() {
		t.Error("distinct spellings must stay distinct terms")
	}
	for _, bad := range []string{"3a", "12_x", "3'"} {
		if _, err := Parse(bad); err == nil {
			t.Errorf("%q accepted", bad)
		}
	}
	// Existing digests are unchanged by the extension: a numeral is an
	// ordinary atom.
	if Atom("3").Digest() != MustParse("3").Digest() {
		t.Error("numeral digest differs from Atom(\"3\")")
	}
}

func naiveFlags(t *Term) uint8 {
	var f uint8
	switch t.Kind() {
	case KindConst:
		f = constFlag(t.Name())
	case KindScope:
		f = FlagScope
	case KindApp:
		f = naiveFlags(t.Fun()) | naiveFlags(t.Arg())
	case KindBracket:
		f = naiveFlags(t.Body()) | FlagBracket
	}
	return f
}

// The structural flags are a pure function of structure, and they take no part
// in the digest: two terms with the same shape and names have the same digest
// whatever their flags, and the flags follow the shape.
func TestFlagsFollowStructureAndDoNotChangeDigests(t *testing.T) {
	cases := map[string]uint8{
		"a":           0,
		"K":           FlagK,
		"K a (S b)":   FlagK | FlagS,
		"<I>_x":       FlagI | FlagBracket,
		"sc_x (B C)":  FlagScope | FlagB | FlagC,
		"W W":         FlagW,
		"<<a>_y>_x":   FlagBracket,
		"z (K)":       FlagK,
		"I B C K W S": FlagI | FlagB | FlagC | FlagK | FlagW | FlagS,
	}
	for src, want := range cases {
		tm := MustParse(src)
		if tm.Flags() != want || naiveFlags(tm) != want {
			t.Errorf("%s: flags %08b, want %08b", src, tm.Flags(), want)
		}
	}
	// a constant whose name merely contains a letter is not that combinator
	if Const("KK").Flags() != 0 || Const("k").Flags() != 0 || Atom("K").Flags() != 0 {
		t.Error("flags set for a name that is not exactly W, K, C, S, I or B, or for an atom")
	}
}
