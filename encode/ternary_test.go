package encode

import (
	"math/rand"
	"strings"
	"testing"

	"github.com/standardgalactic/spherepop-kernel/term"
)

func randTerm(r *rand.Rand, depth int) *term.Term {
	names := []string{"a", "b", "x1", "é", "", "long_name_with_more_than_eight_bytes"}
	consts := []string{"I", "K", "S", "B", "C", "W", "Z", "KK"}
	labels := []string{"x", "y", "", "lbl"}
	k := r.Intn(8)
	if depth <= 0 {
		k = r.Intn(3)
	}
	switch k {
	case 0:
		return term.Atom(names[r.Intn(len(names))])
	case 1:
		return term.Const(consts[r.Intn(len(consts))])
	case 2:
		return term.Scope(labels[r.Intn(len(labels))])
	case 3, 4, 5:
		return term.App(randTerm(r, depth-1), randTerm(r, depth-1))
	}
	return term.Bracket(labels[r.Intn(len(labels))], randTerm(r, depth-1))
}

func TestTernaryRoundTripIsDigestExact(t *testing.T) {
	r := rand.New(rand.NewSource(7))
	for i := 0; i < 3000; i++ {
		orig := randTerm(r, 6)
		frame, err := EncodeTernary(orig)
		if err != nil {
			t.Fatal(err)
		}
		got, err := DecodeTernary(frame)
		if err != nil {
			t.Fatalf("%s: %v", orig, err)
		}
		if got.Digest() != orig.Digest() {
			t.Fatalf("digest changed for %s", orig)
		}
		again, _ := EncodeTernary(got)
		if string(again) != string(frame) {
			t.Fatalf("encoding is not canonical for %s", orig)
		}
	}
}

func TestSixCombinatorsUseFourTrits(t *testing.T) {
	for _, n := range []string{"I", "K", "S", "B", "C", "W"} {
		if got := len(EncodeTrits(term.Const(n))); got != 4 {
			t.Errorf("%s uses %d trits, want 4", n, got)
		}
	}
	if got := len(EncodeTrits(term.App(term.Const("K"), term.Const("I")))); got != 10 {
		t.Errorf("K I uses %d trits, want 10", got)
	}
}

// Every single-trit change of a canonical stream either fails to decode or
// decodes to a different term, and a frame with any single byte changed is
// rejected.
func TestTernaryRejectsEveryNoncanonicalSpelling(t *testing.T) {
	long := EncodeTrits(term.Const("K"))
	// long form of a standard combinator
	forged := []Trit{TritPos, TritZero, TritZero, TritZero}
	forged = appendName(forged, "K")
	if _, err := DecodeTrits(forged); err == nil {
		t.Error("long form of K accepted")
	}
	manual := []Trit{TritPos, TritNeg} // atom
	// length 0 spelled as two groups: (0,0,+1) then (0,0,-1)
	manual = append(manual, TritNeg, TritNeg, TritPos, TritNeg, TritNeg, TritNeg)
	if _, err := DecodeTrits(manual); err == nil {
		t.Error("non-minimal length accepted")
	}
	if _, err := DecodeTrits(append(long, TritZero)); err == nil {
		t.Error("trailing trit accepted")
	}
	r := rand.New(rand.NewSource(3))
	orig := randTerm(r, 5)
	frame, _ := EncodeTernary(orig)
	for i := range frame {
		for _, d := range []byte{1, 0x80} {
			m := append([]byte(nil), frame...)
			m[i] ^= d
			if got, err := DecodeTernary(m); err == nil && got.Digest() != orig.Digest() {
				t.Fatalf("byte %d changed to a different valid term", i)
			} else if err == nil {
				t.Fatalf("byte %d changed but frame still accepted", i)
			}
		}
	}
	for n := 0; n < len(frame); n++ {
		if _, err := DecodeTernary(frame[:n]); err == nil {
			t.Fatalf("truncation to %d accepted", n)
		}
	}
	if _, err := DecodeTernary(append(append([]byte(nil), frame...), 0)); err == nil {
		t.Error("trailing byte accepted")
	}
}

func TestPaddingAndBase243Digits(t *testing.T) {
	if _, err := UnpackTrits([]byte{243}, 5); err == nil {
		t.Error("byte 243 accepted")
	}
	// one trit, nonzero second digit in the padding
	if _, err := UnpackTrits([]byte{1 + 3}, 1); err == nil {
		t.Error("nonzero padding accepted")
	}
	if _, err := UnpackTrits([]byte{1, 2}, 5); err == nil {
		t.Error("extra payload byte accepted")
	}
	if _, err := UnpackTrits(nil, 1); err == nil {
		t.Error("short payload accepted")
	}
	all := make([]Trit, 0, 64)
	for i := 0; i < 64; i++ {
		all = append(all, Trit(i%3)-1)
	}
	p, _ := PackTrits(all)
	back, err := UnpackTrits(p, len(all))
	if err != nil || len(back) != len(all) {
		t.Fatal(err)
	}
	for i := range all {
		if back[i] != all[i] {
			t.Fatalf("trit %d changed", i)
		}
	}
}

func TestDecoderLimits(t *testing.T) {
	// A long chain of applications stays within the depth limit and decodes.
	deep := term.Const("I")
	for i := 0; i < 2000; i++ {
		deep = term.App(term.Const("K"), deep)
	}
	frame, _ := EncodeTernary(deep)
	if got, err := DecodeTernary(frame); err != nil || got.Digest() != deep.Digest() {
		t.Fatalf("deep term: %v", err)
	}
	// A stream that nests beyond the limit is rejected without exhausting memory.
	var ts []Trit
	for i := 0; i <= MaxTernaryDepth+1; i++ {
		ts = append(ts, TritPos, TritPos)
	}
	if _, err := DecodeTrits(ts); err == nil || !strings.Contains(err.Error(), "nesting") {
		t.Fatalf("depth limit not enforced: %v", err)
	}
}

func TestTritWord(t *testing.T) {
	a, _ := PackWord([]Trit{1, -1, 0, 1})
	b, _ := PackWord([]Trit{1, 1, 1, -1})
	if a.Sum() != 1 {
		t.Errorf("sum = %d", a.Sum())
	}
	if got := Dot(a, b); got != 1*1+(-1)*1+0+1*(-1) {
		t.Errorf("dot = %d", got)
	}
	if _, err := PackWord(make([]Trit, 65)); err == nil {
		t.Error("65 trits accepted")
	}
	if _, err := PackWord([]Trit{2}); err == nil {
		t.Error("invalid trit accepted")
	}
}

func byteTrits(v byte) []Trit {
	var out []Trit
	x := uint32(v)
	for k := 0; k < 6; k++ {
		out = append(out, Trit(x%3)-1)
		x /= 3
	}
	return out
}

func TestNameFieldsRejectInvalidTrits(t *testing.T) {
	atom := []Trit{TritPos, TritNeg}
	// A zero continuation trit is neither stop nor continue. Followed by a
	// group that would make a valid length of nine and nine bytes of name, a
	// decoder that treated it as "continue" would accept the stream.
	z := append([]Trit(nil), atom...)
	z = append(z, TritNeg, TritNeg, TritZero, TritZero, TritNeg, TritNeg)
	for i := 0; i < 9; i++ {
		z = append(z, byteTrits('a')...)
	}
	if _, err := DecodeTrits(z); err == nil {
		t.Error("zero continuation trit accepted")
	}
	// A name of one byte whose six trits spell 728, above 255.
	one := append(append([]Trit(nil), atom...), TritZero, TritNeg, TritNeg)
	for i := 0; i < 6; i++ {
		one = append(one, TritPos)
	}
	if _, err := DecodeTrits(one); err == nil {
		t.Error("byte value above 255 accepted")
	}
	// The same stream with a valid byte decodes, so the two rejections above
	// are about the trits and not the shape.
	ok := append(append([]Trit(nil), atom...), TritZero, TritNeg, TritNeg)
	ok = append(ok, byteTrits('a')...)
	if got, err := DecodeTrits(ok); err != nil || got.Name() != "a" {
		t.Errorf("valid stream rejected: %v", err)
	}
}
