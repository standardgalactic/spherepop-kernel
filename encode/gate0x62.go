package encode

import (
	"encoding/binary"
	"errors"
	"io"
	"math/bits"
	"sync"
	"sync/atomic"
)

const (
	// Gate0x62 is the default gate byte for 32-byte frame seals.
	Gate0x62 uint8 = 0x62

	// FrameABIV1 identifies version 1 of the 32-byte frame layout.
	FrameABIV1 uint8 = 0x01

	// QuantQT55 is the alternating 0x55 quantization bitplane mask byte (qt:55).
	QuantQT55 uint8 = 0x55

	// Fold0xE1034E575C371AB0 is the canonical 64-bit kompress-super-ultra fold
	// signature verified at gate 0x62 and quantization boundary qt:55.
	Fold0xE1034E575C371AB0 uint64 = 0xe1034e575c371ab0
)

var streamBufPool = sync.Pool{
	New: func() any {
		buf := make([]byte, 4096)
		return &buf
	},
}

// XORFoldScalar computes the 64-bit little-endian XOR fold one word at a time.
func XORFoldScalar(data []byte) uint64 {
	var acc uint64
	i := 0
	for ; i+8 <= len(data); i += 8 {
		acc ^= binary.LittleEndian.Uint64(data[i : i+8])
	}
	for ; i < len(data); i++ {
		acc ^= uint64(data[i])
	}
	return acc
}

// XORFold computes the 64-bit little-endian XOR fold in 64-byte (8-word) steps
// across four independent accumulators to maximize instruction-level parallelism.
// It agrees bit-for-bit with XORFoldScalar and the wupz Zig xorFold implementation.
func XORFold(data []byte) uint64 {
	var a0, a1, a2, a3 uint64
	i := 0
	for ; i+64 <= len(data); i += 64 {
		b := data[i : i+64 : i+64]
		a0 ^= binary.LittleEndian.Uint64(b[0:8]) ^ binary.LittleEndian.Uint64(b[32:40])
		a1 ^= binary.LittleEndian.Uint64(b[8:16]) ^ binary.LittleEndian.Uint64(b[40:48])
		a2 ^= binary.LittleEndian.Uint64(b[16:24]) ^ binary.LittleEndian.Uint64(b[48:56])
		a3 ^= binary.LittleEndian.Uint64(b[24:32]) ^ binary.LittleEndian.Uint64(b[56:64])
	}
	acc := (a0 ^ a1) ^ (a2 ^ a3)
	for ; i+8 <= len(data); i += 8 {
		acc ^= binary.LittleEndian.Uint64(data[i : i+8])
	}
	for ; i < len(data); i++ {
		acc ^= uint64(data[i])
	}
	return acc
}

// StreamXORFold folds an io.Reader in 8-byte aligned chunks using a pooled
// 4096-byte buffer so repeated streaming calls do not allocate on the heap.
func StreamXORFold(r io.Reader) (fold uint64, totalBytes int64, err error) {
	bp := streamBufPool.Get().(*[]byte)
	buf := *bp
	defer streamBufPool.Put(bp)

	var tail [8]byte
	tailLen := 0

	for {
		n, rerr := r.Read(buf)
		if n > 0 {
			totalBytes += int64(n)
			chunk := buf[:n]
			if tailLen > 0 {
				need := 8 - tailLen
				if len(chunk) >= need {
					copy(tail[tailLen:8], chunk[:need])
					fold ^= binary.LittleEndian.Uint64(tail[:])
					chunk = chunk[need:]
					tailLen = 0
				} else {
					copy(tail[tailLen:], chunk)
					tailLen += len(chunk)
					chunk = nil
				}
			}
			aligned := len(chunk) &^ 7
			if aligned > 0 {
				fold ^= XORFold(chunk[:aligned])
			}
			rem := chunk[aligned:]
			if len(rem) > 0 {
				copy(tail[:], rem)
				tailLen = len(rem)
			}
		}
		if rerr == io.EOF {
			break
		}
		if rerr != nil {
			return 0, totalBytes, rerr
		}
	}
	for i := 0; i < tailLen; i++ {
		fold ^= uint64(tail[i])
	}
	return fold, totalBytes, nil
}

// ByteDiff returns the number of differing byte positions across the shared
// prefix of a and b using 64-bit SWAR non-zero byte detection.
func ByteDiff(a, b []byte) uint64 {
	n := len(a)
	if len(b) < n {
		n = len(b)
	}
	var count uint64
	i := 0
	for ; i+8 <= n; i += 8 {
		d := binary.LittleEndian.Uint64(a[i:i+8]) ^ binary.LittleEndian.Uint64(b[i:i+8])
		if d != 0 {
			// Collapse any non-zero byte into a 1 in its MSB, then count set MSBs.
			msb := ((d & 0x7f7f7f7f7f7f7f7f) + 0x7f7f7f7f7f7f7f7f) | d
			count += uint64(bits.OnesCount64(msb & 0x8080808080808080))
		}
	}
	for ; i < n; i++ {
		if a[i] != b[i] {
			count++
		}
	}
	return count
}

// Popcount returns the total number of set bits in data using 4-way unrolled
// 64-bit hardware POPCNT.
func Popcount(data []byte) uint64 {
	var c0, c1, c2, c3 uint64
	i := 0
	for ; i+32 <= len(data); i += 32 {
		b := data[i : i+32 : i+32]
		c0 += uint64(bits.OnesCount64(binary.LittleEndian.Uint64(b[0:8])))
		c1 += uint64(bits.OnesCount64(binary.LittleEndian.Uint64(b[8:16])))
		c2 += uint64(bits.OnesCount64(binary.LittleEndian.Uint64(b[16:24])))
		c3 += uint64(bits.OnesCount64(binary.LittleEndian.Uint64(b[24:32])))
	}
	count := (c0 + c1) + (c2 + c3)
	for ; i+8 <= len(data); i += 8 {
		count += uint64(bits.OnesCount64(binary.LittleEndian.Uint64(data[i : i+8])))
	}
	for ; i < len(data); i++ {
		count += uint64(bits.OnesCount8(data[i]))
	}
	return count
}

// SealFrame32B constructs a 32-byte frame seal over raw and packed slices at
// the given gate byte. This is a non-cryptographic checksum: distinct payloads
// can have the same length and XOR fold. It does not authenticate payloads.
//
// Wire layout (32 bytes, little-endian):
//
//	[0..8]   uint64  XORFold(raw)
//	[8..16]  uint64  XORFold(packed)
//	[16..20] uint32  uint32(len(raw))
//	[20..24] uint32  uint32(len(packed))
//	[24]     uint8   gate
//	[25]     uint8   FrameABIV1
//	[26..32] 6B      low 48 bits of XORFold(frame[0:26])
func SealFrame32B(raw, packed []byte, gate uint8) [32]byte {
	var frame [32]byte
	binary.LittleEndian.PutUint64(frame[0:8], XORFold(raw))
	binary.LittleEndian.PutUint64(frame[8:16], XORFold(packed))
	binary.LittleEndian.PutUint32(frame[16:20], uint32(len(raw)))
	binary.LittleEndian.PutUint32(frame[20:24], uint32(len(packed)))
	frame[24] = gate
	frame[25] = FrameABIV1
	var tail [8]byte
	binary.LittleEndian.PutUint64(tail[:], XORFold(frame[0:26]))
	copy(frame[26:32], tail[0:6])
	return frame
}

// CheckFrame32B checks whether frame matches SealFrame32B(raw, packed, gate)
// using a bitwise accumulator over all 32 bytes after checking the header.
// A match does not establish payload identity or authenticity.
func CheckFrame32B(frame [32]byte, raw, packed []byte, gate uint8) bool {
	if frame[24] != gate || frame[25] != FrameABIV1 {
		return false
	}
	expected := SealFrame32B(raw, packed, gate)
	var diff uint8
	for i := 0; i < 32; i++ {
		diff |= frame[i] ^ expected[i]
	}
	return diff == 0
}

// gate0x62Snapshot is immutable once published.
type gate0x62Snapshot struct {
	fold  uint64
	state Trit
}

// Gate0x62State publishes the fold and ternary state as one atomic snapshot.
// Its zero value is fold 0 and TritZero. It must not be copied after first use.
type Gate0x62State struct {
	current atomic.Pointer[gate0x62Snapshot]
}

// NewGate0x62State initializes a Gate0x62State with the given initial fold.
func NewGate0x62State(initialFold uint64) *Gate0x62State {
	g := &Gate0x62State{}
	g.current.Store(&gate0x62Snapshot{fold: initialFold, state: TritZero})
	return g
}

// AdvanceCAS atomically publishes nextFold and nextState if the current fold
// equals expectedFold. Invalid trits are rejected without changing the state.
// The comparison is by fold, so callers requiring generation checks must use
// distinct fold values for distinct generations.
func (g *Gate0x62State) AdvanceCAS(expectedFold, nextFold uint64, nextState Trit) bool {
	if nextState != TritNeg && nextState != TritZero && nextState != TritPos {
		return false
	}
	old := g.current.Load()
	var fold uint64
	if old != nil {
		fold = old.fold
	}
	if fold != expectedFold {
		return false
	}
	return g.current.CompareAndSwap(old, &gate0x62Snapshot{fold: nextFold, state: nextState})
}

// Snapshot returns a fold and state from the same published update.
func (g *Gate0x62State) Snapshot() (uint64, Trit) {
	s := g.current.Load()
	if s == nil {
		return 0, TritZero
	}
	return s.fold, s.state
}

// Fold returns the current fold. Use Snapshot when reading the pair together.
func (g *Gate0x62State) Fold() uint64 {
	fold, _ := g.Snapshot()
	return fold
}

// State returns the current state. Use Snapshot when reading the pair together.
func (g *Gate0x62State) State() Trit {
	_, state := g.Snapshot()
	return state
}

// PackBFP64 packs balanced trits into separate positive and negative 64-bit
// bitplanes (BFP-64 layout, 64 trits per uint64 word).
func PackBFP64(trits []Trit) (posPlane []uint64, negPlane []uint64, err error) {
	words := (len(trits) + 63) / 64
	posPlane = make([]uint64, words)
	negPlane = make([]uint64, words)
	for i, t := range trits {
		w := i >> 6
		b := uint(i & 63)
		switch t {
		case TritPos:
			posPlane[w] |= 1 << b
		case TritNeg:
			negPlane[w] |= 1 << b
		case TritZero:
		default:
			return nil, nil, errors.New("encode: invalid trit value in PackBFP64")
		}
	}
	return posPlane, negPlane, nil
}

// UnpackBFP64 reconstructs n balanced trits from BFP-64 bitplanes. It rejects
// words where the positive and negative bitplanes overlap at the same bit.
func UnpackBFP64(posPlane, negPlane []uint64, n int) ([]Trit, error) {
	if n < 0 {
		return nil, errors.New("encode: negative trit count")
	}
	words := (n + 63) / 64
	if len(posPlane) < words || len(negPlane) < words {
		return nil, errors.New("encode: bitplane slice shorter than requested trit count")
	}
	for w := 0; w < words; w++ {
		if posPlane[w]&negPlane[w] != 0 {
			return nil, errors.New("encode: overlapping positive and negative bitplanes")
		}
	}
	out := make([]Trit, n)
	for i := 0; i < n; i++ {
		w := i >> 6
		mask := uint64(1) << uint(i&63)
		if posPlane[w]&mask != 0 {
			out[i] = TritPos
		} else if negPlane[w]&mask != 0 {
			out[i] = TritNeg
		} else {
			out[i] = TritZero
		}
	}
	return out, nil
}

// BFP64AndKleene computes the 64-lane Kleene three-valued AND (min) across two
// BFP-64 bitplane words: the output is +1 when both inputs are +1, -1 when
// either input is -1, and 0 otherwise.
func BFP64AndKleene(posA, negA, posB, negB uint64) (posOut, negOut uint64) {
	posOut = posA & posB
	negOut = negA | negB
	posOut &^= negOut
	return posOut, negOut
}

// BFP64NandKleene computes the 64-lane Kleene three-valued NAND (negation of
// Kleene AND) across two BFP-64 bitplane words by swapping the resulting
// positive and negative bitplanes.
func BFP64NandKleene(posA, negA, posB, negB uint64) (posOut, negOut uint64) {
	p, n := BFP64AndKleene(posA, negA, posB, negB)
	return n, p
}

// IsqrtU64 returns the integer floor square root of n using integer arithmetic
// with no floating-point conversion.
func IsqrtU64(n uint64) uint64 {
	if n < 2 {
		return n
	}
	shift := uint((bits.Len64(n) - 1) &^ 1)
	var res uint64
	for {
		cand := res + (1 << shift)
		res >>= 1
		if n >= cand {
			n -= cand
			res += 1 << shift
		}
		if shift == 0 {
			break
		}
		shift -= 2
	}
	return res
}

// RationalDensity represents a reduced rational ratio p/q together with its
// balanced ternary signal classification. Fields are ordered from 8-byte to
// 1-byte alignment to avoid internal struct padding.
type RationalDensity struct {
	Num   int64
	Den   int64
	State Trit
}

func gcdInt64(a, b int64) int64 {
	if a < 0 {
		a = -a
	}
	if b < 0 {
		b = -b
	}
	for b != 0 {
		a, b = b, a%b
	}
	if a == 0 {
		return 1
	}
	return a
}

// CheckRationalDensity reduces num/den by their greatest common divisor and
// classifies the ratio into a balanced Trit: TritPos when num > den > 0
// (positive compression gain), TritZero when num == den, and TritNeg when
// num < den (expansion).
func CheckRationalDensity(num, den int64) (RationalDensity, error) {
	if den <= 0 || num < 0 {
		return RationalDensity{}, errors.New("encode: density ratio requires num >= 0 and den > 0")
	}
	g := gcdInt64(num, den)
	rNum := num / g
	rDen := den / g
	state := TritZero
	if rNum > rDen {
		state = TritPos
	} else if rNum < rDen {
		state = TritNeg
	}
	return RationalDensity{
		Num:   rNum,
		Den:   rDen,
		State: state,
	}, nil
}

// QTBroadcastMask broadcasts an 8-bit quantization mask across all 8 bytes of
// a 64-bit word.
func QTBroadcastMask(qt uint8) uint64 {
	return uint64(qt) * 0x0101010101010101
}

// PackFoldBFP64 packs a 64-bit fold signature into disjoint BFP-64 positive
// and negative bitplanes partitioned by the quantization byte qt.
func PackFoldBFP64(fold uint64, qt uint8) (posPlane, negPlane uint64) {
	mask := QTBroadcastMask(qt)
	return fold & mask, fold &^ mask
}

// UnpackFoldBFP64 reconstructs the 64-bit fold signature from BFP-64 positive
// and negative bitplanes and verifies zero bit leakage across the qt mask.
func UnpackFoldBFP64(posPlane, negPlane uint64, qt uint8) (uint64, error) {
	if posPlane&negPlane != 0 {
		return 0, errors.New("encode: overlapping positive and negative fold bitplanes")
	}
	mask := QTBroadcastMask(qt)
	if posPlane&^mask != 0 || negPlane&mask != 0 {
		return 0, errors.New("encode: bit leakage across qt quantization boundary")
	}
	return posPlane | negPlane, nil
}

// VerifyUltrabackyardLoopHierarchy verifies that the reduced p/q ratio 123/115,
// the 0x62 gate (+AND=1, ~NAND=-1), and BFP-64 fold packing remain invariant
// across levels of the ULTRABACKYARDLOOP hierarchy without quantization drift.
func VerifyUltrabackyardLoopHierarchy(baseNum, baseDen int64, qt, gate uint8, fold uint64, levels int) error {
	if gate != Gate0x62 {
		return errors.New("encode: unexpected gate byte")
	}
	if qt != QuantQT55 {
		return errors.New("encode: unexpected quantization boundary")
	}
	if levels <= 0 {
		return errors.New("encode: levels must be positive")
	}
	base, err := CheckRationalDensity(baseNum, baseDen)
	if err != nil {
		return err
	}
	if base.Num != 123 || base.Den != 115 || base.State != TritPos {
		return errors.New("encode: base density ratio must reduce to 123/115 (+1)")
	}
	curFold := fold
	for level := 1; level <= levels; level++ {
		scale := int64(level) * int64(qt)
		if scale <= 0 {
			return errors.New("encode: integer overflow in hierarchy scale")
		}
		d, err := CheckRationalDensity(base.Num*scale, base.Den*scale)
		if err != nil {
			return err
		}
		if d.Num != 123 || d.Den != 115 || d.State != TritPos {
			return errors.New("encode: quantization drift detected in p/q hierarchy")
		}
		pos, neg := PackFoldBFP64(curFold, qt)
		andPos, andNeg := BFP64AndKleene(pos, 0, pos, 0)
		nandPos, nandNeg := BFP64NandKleene(neg, 0, neg, 0)
		if andPos != pos || andNeg != 0 {
			return errors.New("encode: +AND=1 bitplane verification failed")
		}
		if nandPos != 0 || nandNeg != neg {
			return errors.New("encode: ~NAND=-1 bitplane verification failed")
		}
		recovered, err := UnpackFoldBFP64(andPos, nandNeg, qt)
		if err != nil {
			return err
		}
		if recovered != curFold {
			return errors.New("encode: BFP-64 fold round-trip mismatch")
		}
		curFold = bits.RotateLeft64(recovered^(uint64(gate)<<8)^uint64(qt), 7)
	}
	return nil
}
