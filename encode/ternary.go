package encode

import (
	"crypto/sha256"
	"encoding/binary"
	"errors"
	"fmt"
	"math/bits"

	"github.com/standardgalactic/spherepop-kernel/term"
)

// This file is a compact balanced-ternary transport encoding of terms (SPQT,
// version 1). It is an auxiliary codec for storage and transmission. Term
// digests, traces and logs do not use it and SPEC.md section 18 does not
// depend on it: a term decoded from a frame is accepted only if it re-encodes
// to the same frame, so the frame is a second spelling of the same term and
// never a second meaning.
//
// The stream is Polish prefix, packed five trits to a byte. It is canonical:
// every term has exactly one frame, and a decoder rejects every other spelling.

// Trit is a balanced ternary digit, -1, 0 or +1.
type Trit int8

// The three trit values.
const (
	TritNeg  Trit = -1
	TritZero Trit = 0
	TritPos  Trit = 1
)

// ErrBadTernary reports a stream or frame that is not the canonical encoding
// of a term.
var ErrBadTernary = errors.New("encode: malformed ternary stream")

// Limits that keep a decoder from being driven to unbounded work by a short
// frame.
const (
	MaxTernaryTrits = 1 << 24
	MaxTernaryDepth = 100000
	maxNameBytes    = 1 << 20
)

var ternaryMagic = [5]byte{'S', 'P', 'Q', 'T', 1}

// checkBytes is the length of the integrity check in a frame, the first bytes
// of SHA-256 over the header and payload.
const checkBytes = 4

func bad(format string, a ...any) error {
	return fmt.Errorf("%w: %s", ErrBadTernary, fmt.Sprintf(format, a...))
}

// Node tags, two trits each.
//
//	app      (+1,+1)  then function, argument
//	combinator (+1, 0) then a two-trit code, or (0,0) and a name for any other constant
//	atom     (+1,-1)  then name
//	bracket  (-1,+1)  then label, body
//	scope    (-1,-1)  then label
//
// The six standard combinators have short codes. A constant with any other
// name uses the long form, and the long form is invalid for the six names so
// that each term has one encoding.
var combCode = map[string][2]Trit{
	"I": {TritNeg, TritNeg},
	"K": {TritNeg, TritZero},
	"S": {TritNeg, TritPos},
	"B": {TritZero, TritNeg},
	"C": {TritZero, TritPos},
	"W": {TritPos, TritNeg},
}

func combByCode(a, b Trit) (string, bool) {
	for n, c := range combCode {
		if c[0] == a && c[1] == b {
			return n, true
		}
	}
	return "", false
}

// appendName writes a name as a length and then six trits per byte. The length
// is a sequence of groups of three trits, two digits of a base-nine number
// least significant group first and a continuation trit that is +1 when
// another group follows. The last group of a length above eight is never zero,
// so the length has one spelling.
func appendName(dst []Trit, s string) []Trit {
	n := uint64(len(s))
	for {
		chunk := n % 9
		n /= 9
		cont := TritNeg
		if n > 0 {
			cont = TritPos
		}
		dst = append(dst, Trit(chunk%3)-1, Trit(chunk/3)-1, cont)
		if n == 0 {
			break
		}
	}
	for i := 0; i < len(s); i++ {
		v := uint32(s[i])
		for k := 0; k < 6; k++ {
			dst = append(dst, Trit(v%3)-1)
			v /= 3
		}
	}
	return dst
}

// EncodeTrits returns the canonical trit stream of t.
func EncodeTrits(t *term.Term) []Trit {
	var dst []Trit
	var walk func(*term.Term)
	walk = func(u *term.Term) {
		switch u.Kind() {
		case term.KindApp:
			dst = append(dst, TritPos, TritPos)
			walk(u.Fun())
			walk(u.Arg())
		case term.KindConst:
			dst = append(dst, TritPos, TritZero)
			if c, ok := combCode[u.Name()]; ok {
				dst = append(dst, c[0], c[1])
			} else {
				dst = append(dst, TritZero, TritZero)
				dst = appendName(dst, u.Name())
			}
		case term.KindAtom:
			dst = append(dst, TritPos, TritNeg)
			dst = appendName(dst, u.Name())
		case term.KindBracket:
			dst = append(dst, TritNeg, TritPos)
			dst = appendName(dst, u.Label())
			walk(u.Body())
		case term.KindScope:
			dst = append(dst, TritNeg, TritNeg)
			dst = appendName(dst, u.Label())
		}
	}
	walk(t)
	return dst
}

type tritReader struct {
	src []Trit
	pos int
}

func (r *tritReader) next() (Trit, error) {
	if r.pos >= len(r.src) {
		return 0, bad("stream ends at trit %d", r.pos)
	}
	t := r.src[r.pos]
	r.pos++
	if t < -1 || t > 1 {
		return 0, bad("invalid trit %d at %d", t, r.pos-1)
	}
	return t, nil
}

func (r *tritReader) name() (string, error) {
	var length, mul uint64 = 0, 1
	for group := 0; ; group++ {
		d0, err := r.next()
		if err != nil {
			return "", err
		}
		d1, err := r.next()
		if err != nil {
			return "", err
		}
		cont, err := r.next()
		if err != nil {
			return "", err
		}
		chunk := uint64(d0+1) + 3*uint64(d1+1)
		if cont == TritZero {
			return "", bad("zero continuation trit in a name length at %d", r.pos-1)
		}
		length += chunk * mul
		if cont == TritNeg {
			if group > 0 && chunk == 0 {
				return "", bad("name length is not minimal at %d", r.pos-3)
			}
			break
		}
		mul *= 9
		if mul > maxNameBytes*9 {
			return "", bad("name length is too large")
		}
	}
	if length > maxNameBytes {
		return "", bad("name of %d bytes exceeds the limit", length)
	}
	buf := make([]byte, length)
	for i := range buf {
		var v, pow uint32 = 0, 1
		for k := 0; k < 6; k++ {
			t, err := r.next()
			if err != nil {
				return "", err
			}
			v += uint32(t+1) * pow
			pow *= 3
		}
		if v > 255 {
			return "", bad("byte value %d above 255", v)
		}
		buf[i] = byte(v)
	}
	return string(buf), nil
}

func (r *tritReader) term(depth int) (*term.Term, error) {
	if depth > MaxTernaryDepth {
		return nil, bad("nesting deeper than %d", MaxTernaryDepth)
	}
	a, err := r.next()
	if err != nil {
		return nil, err
	}
	b, err := r.next()
	if err != nil {
		return nil, err
	}
	switch {
	case a == TritPos && b == TritPos:
		f, err := r.term(depth + 1)
		if err != nil {
			return nil, err
		}
		x, err := r.term(depth + 1)
		if err != nil {
			return nil, err
		}
		return term.App(f, x), nil
	case a == TritPos && b == TritZero:
		c0, err := r.next()
		if err != nil {
			return nil, err
		}
		c1, err := r.next()
		if err != nil {
			return nil, err
		}
		if c0 == TritZero && c1 == TritZero {
			n, err := r.name()
			if err != nil {
				return nil, err
			}
			if _, short := combCode[n]; short {
				return nil, bad("constant %q must use its short code", n)
			}
			return term.Const(n), nil
		}
		n, ok := combByCode(c0, c1)
		if !ok {
			return nil, bad("unknown combinator code (%d,%d)", c0, c1)
		}
		return term.Const(n), nil
	case a == TritPos && b == TritNeg:
		n, err := r.name()
		if err != nil {
			return nil, err
		}
		return term.Atom(n), nil
	case a == TritNeg && b == TritPos:
		l, err := r.name()
		if err != nil {
			return nil, err
		}
		body, err := r.term(depth + 1)
		if err != nil {
			return nil, err
		}
		return term.Bracket(l, body), nil
	case a == TritNeg && b == TritNeg:
		l, err := r.name()
		if err != nil {
			return nil, err
		}
		return term.Scope(l), nil
	}
	return nil, bad("unknown node tag (%d,%d)", a, b)
}

// DecodeTrits parses a trit stream. The stream must be exactly the canonical
// encoding of one term.
func DecodeTrits(trits []Trit) (*term.Term, error) {
	if len(trits) > MaxTernaryTrits {
		return nil, bad("%d trits exceeds the limit", len(trits))
	}
	r := &tritReader{src: trits}
	t, err := r.term(0)
	if err != nil {
		return nil, err
	}
	if r.pos != len(trits) {
		return nil, bad("%d trailing trits", len(trits)-r.pos)
	}
	return t, nil
}

// PackTrits packs trits five to a byte, as a base-243 number with the first
// trit least significant. Unused places in the last byte are zero digits.
func PackTrits(trits []Trit) ([]byte, error) {
	out := make([]byte, (len(trits)+4)/5)
	for i := 0; i < len(trits); i += 5 {
		var acc, pow uint16 = 0, 1
		for j := 0; j < 5 && i+j < len(trits); j++ {
			t := trits[i+j]
			if t < -1 || t > 1 {
				return nil, bad("invalid trit %d at %d", t, i+j)
			}
			acc += uint16(t+1) * pow
			pow *= 3
		}
		out[i/5] = byte(acc)
	}
	return out, nil
}

// UnpackTrits reads count trits. A byte of 243 or more, a short payload, extra
// bytes, or a nonzero digit in the unused places of the last byte is an error.
func UnpackTrits(packed []byte, count int) ([]Trit, error) {
	if count < 0 || count > MaxTernaryTrits {
		return nil, bad("trit count %d out of range", count)
	}
	if len(packed) != (count+4)/5 {
		return nil, bad("%d payload bytes for %d trits", len(packed), count)
	}
	out := make([]Trit, count)
	for i := 0; i < count; i += 5 {
		b := packed[i/5]
		if b >= 243 {
			return nil, bad("byte %d at %d is not a base-243 digit group", b, i/5)
		}
		v := b
		for j := 0; j < 5; j++ {
			d := v % 3
			v /= 3
			if i+j < count {
				out[i+j] = Trit(d) - 1
			} else if d != 0 {
				return nil, bad("nonzero padding in the last byte")
			}
		}
	}
	return out, nil
}

// EncodeTernary returns the SPQT frame of t: the magic and version, the trit
// count as an unsigned varint, the packed trits, and a four byte check that is
// a prefix of the SHA-256 of everything before it.
func EncodeTernary(t *term.Term) ([]byte, error) {
	trits := EncodeTrits(t)
	packed, err := PackTrits(trits)
	if err != nil {
		return nil, err
	}
	var vb [binary.MaxVarintLen64]byte
	vn := binary.PutUvarint(vb[:], uint64(len(trits)))
	out := make([]byte, 0, len(ternaryMagic)+vn+len(packed)+checkBytes)
	out = append(out, ternaryMagic[:]...)
	out = append(out, vb[:vn]...)
	out = append(out, packed...)
	sum := sha256.Sum256(out)
	return append(out, sum[:checkBytes]...), nil
}

// DecodeTernary parses an SPQT frame. It accepts a frame only if re-encoding
// the decoded term gives the same bytes.
func DecodeTernary(frame []byte) (*term.Term, error) {
	if len(frame) < len(ternaryMagic)+1+checkBytes || string(frame[:len(ternaryMagic)]) != string(ternaryMagic[:]) {
		return nil, bad("missing SPQT version 1 header")
	}
	body, check := frame[:len(frame)-checkBytes], frame[len(frame)-checkBytes:]
	sum := sha256.Sum256(body)
	if string(sum[:checkBytes]) != string(check) {
		return nil, bad("integrity check mismatch")
	}
	count, vn := binary.Uvarint(body[len(ternaryMagic):])
	if vn <= 0 || count > MaxTernaryTrits {
		return nil, bad("invalid trit count")
	}
	var tmp [binary.MaxVarintLen64]byte
	if binary.PutUvarint(tmp[:], count) != vn {
		return nil, bad("trit count is not minimal")
	}
	trits, err := UnpackTrits(body[len(ternaryMagic)+vn:], int(count))
	if err != nil {
		return nil, err
	}
	return DecodeTrits(trits)
}

// TritWord packs up to 64 trits into two bit planes, so that sums and inner
// products cost a few bitwise operations and population counts.
type TritWord struct {
	Pos uint64 // bit i set when trit i is +1
	Neg uint64 // bit i set when trit i is -1
}

// PackWord packs the first 64 trits of ts. It returns an error for more than
// 64 trits or an invalid trit.
func PackWord(ts []Trit) (TritWord, error) {
	var w TritWord
	if len(ts) > 64 {
		return w, bad("%d trits do not fit a 64 trit word", len(ts))
	}
	for i, t := range ts {
		switch t {
		case TritPos:
			w.Pos |= 1 << uint(i)
		case TritNeg:
			w.Neg |= 1 << uint(i)
		case TritZero:
		default:
			return w, bad("invalid trit %d at %d", t, i)
		}
	}
	return w, nil
}

// Sum is the sum of the trits.
func (w TritWord) Sum() int { return bits.OnesCount64(w.Pos) - bits.OnesCount64(w.Neg) }

// Dot is the inner product of two words.
func Dot(a, b TritWord) int {
	same := (a.Pos & b.Pos) | (a.Neg & b.Neg)
	opp := (a.Pos & b.Neg) | (a.Neg & b.Pos)
	return bits.OnesCount64(same) - bits.OnesCount64(opp)
}
