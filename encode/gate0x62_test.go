package encode

import (
	"bytes"
	"sync"
	"testing"
)

func TestXORFoldMatchesScalarAndStreamAcrossLengths(t *testing.T) {
	buf := make([]byte, 1088)
	var x uint64 = 0x9E3779B97F4A7C15
	for i := range buf {
		x = x*6364136223846793005 + 1442695040888963407
		buf[i] = byte(x >> 33)
	}
	for n := 0; n <= len(buf); n++ {
		got := XORFold(buf[:n])
		want := XORFoldScalar(buf[:n])
		if got != want {
			t.Fatalf("len=%d: XORFold=%#x want=%#x", n, got, want)
		}
		streamFold, total, err := StreamXORFold(bytes.NewReader(buf[:n]))
		if err != nil {
			t.Fatalf("len=%d: StreamXORFold err=%v", n, err)
		}
		if total != int64(n) || streamFold != want {
			t.Fatalf("len=%d: StreamXORFold=(%#x,%d) want=(%#x,%d)", n, streamFold, total, want, n)
		}
	}
}

func TestSealAndCheckFrame32BAt0x62Gate(t *testing.T) {
	raw := bytes.Repeat([]byte{0x62}, 3761)
	packed := bytes.Repeat([]byte{0x33}, 3314)
	raw[0] = 0x74
	packed[0] = 0x5c

	frame := SealFrame32B(raw, packed, Gate0x62)
	if frame[24] != Gate0x62 {
		t.Fatalf("gate byte = %#x, want %#x", frame[24], Gate0x62)
	}
	if frame[25] != FrameABIV1 {
		t.Fatalf("abi byte = %#x, want %#x", frame[25], FrameABIV1)
	}
	if !CheckFrame32B(frame, raw, packed, Gate0x62) {
		t.Fatal("CheckFrame32B rejected valid 32B frame")
	}

	spiked := frame
	spiked[31] ^= 0x01
	if CheckFrame32B(spiked, raw, packed, Gate0x62) {
		t.Fatal("CheckFrame32B accepted frame with flipped seal bit")
	}
}

func TestGate0x62StateConcurrentCAS(t *testing.T) {
	g := NewGate0x62State(0x2d7b7a560c457f7f)
	var wg sync.WaitGroup
	winners := make(chan int, 16)
	for i := 0; i < 16; i++ {
		wg.Add(1)
		go func(id int) {
			defer wg.Done()
			if g.AdvanceCAS(0x2d7b7a560c457f7f, 0xcf197ec401952c21, TritPos) {
				winners <- id
			}
		}(i)
	}
	wg.Wait()
	close(winners)

	count := 0
	for range winners {
		count++
	}
	if count != 1 {
		t.Fatalf("AdvanceCAS winners = %d, want 1", count)
	}
	if g.Fold() != 0xcf197ec401952c21 || g.State() != TritPos {
		t.Fatalf("Gate0x62State = (%#x, %d), want (0xcf197ec401952c21, +1)", g.Fold(), g.State())
	}
}

func TestBFP64RoundTripAndKleeneGates(t *testing.T) {
	trits := make([]Trit, 197)
	for i := range trits {
		switch i % 3 {
		case 0:
			trits[i] = TritNeg
		case 1:
			trits[i] = TritZero
		case 2:
			trits[i] = TritPos
		}
	}
	pos, neg, err := PackBFP64(trits)
	if err != nil {
		t.Fatalf("PackBFP64: %v", err)
	}
	got, err := UnpackBFP64(pos, neg, len(trits))
	if err != nil {
		t.Fatalf("UnpackBFP64: %v", err)
	}
	for i := range trits {
		if got[i] != trits[i] {
			t.Fatalf("trit[%d] = %d, want %d", i, got[i], trits[i])
		}
	}

	// Verify +AND=1 and ~NAND=-1 on all-positive 64-trit bitplane words.
	const allOnes = ^uint64(0)
	andPos, andNeg := BFP64AndKleene(allOnes, 0, allOnes, 0)
	if andPos != allOnes || andNeg != 0 {
		t.Fatalf("BFP64AndKleene(+1,+1) = (%#x,%#x), want (allOnes,0)", andPos, andNeg)
	}
	nandPos, nandNeg := BFP64NandKleene(allOnes, 0, allOnes, 0)
	if nandPos != 0 || nandNeg != allOnes {
		t.Fatalf("BFP64NandKleene(+1,+1) = (%#x,%#x), want (0,allOnes)", nandPos, nandNeg)
	}

	pos[0] |= neg[0]
	if _, err := UnpackBFP64(pos, neg, len(trits)); err == nil {
		t.Fatal("UnpackBFP64 accepted overlapping bitplanes")
	}
}

func TestCheckRationalDensityAndIsqrtU64(t *testing.T) {
	d1, err := CheckRationalDensity(3761, 3314)
	if err != nil {
		t.Fatalf("3761/3314: %v", err)
	}
	if d1.Num != 3761 || d1.Den != 3314 || d1.State != TritPos {
		t.Fatalf("got %+v, want 3761/3314 TritPos", d1)
	}

	d2, err := CheckRationalDensity(123, 115)
	if err != nil {
		t.Fatalf("123/115: %v", err)
	}
	if d2.Num != 123 || d2.Den != 115 || d2.State != TritPos {
		t.Fatalf("got %+v, want 123/115 TritPos", d2)
	}

	for _, tc := range []struct {
		n    uint64
		want uint64
	}{
		{0, 0},
		{1, 1},
		{15, 3},
		{16, 4},
		{3761 * 3761, 3761},
		{1<<62 - 1, (1 << 31) - 1},
	} {
		if got := IsqrtU64(tc.n); got != tc.want {
			t.Fatalf("IsqrtU64(%d) = %d, want %d", tc.n, got, tc.want)
		}
	}
}

func TestFold0xE1034E575C371AB0AtQT55AndUltrabackyardLoop(t *testing.T) {
	pos, neg := PackFoldBFP64(Fold0xE1034E575C371AB0, QuantQT55)
	if pos&neg != 0 {
		t.Fatalf("PackFoldBFP64 planes overlap: pos=%#x neg=%#x", pos, neg)
	}
	got, err := UnpackFoldBFP64(pos, neg, QuantQT55)
	if err != nil {
		t.Fatalf("UnpackFoldBFP64: %v", err)
	}
	if got != Fold0xE1034E575C371AB0 {
		t.Fatalf("UnpackFoldBFP64 = %#x, want %#x", got, Fold0xE1034E575C371AB0)
	}
	if _, err := UnpackFoldBFP64(pos|0x02, neg, QuantQT55); err == nil {
		t.Fatal("UnpackFoldBFP64 accepted bit leakage across qt:55 mask")
	}
	if err := VerifyUltrabackyardLoopHierarchy(123, 115, QuantQT55, Gate0x62, Fold0xE1034E575C371AB0, 16); err != nil {
		t.Fatalf("VerifyUltrabackyardLoopHierarchy: %v", err)
	}
}

func TestByteDiffAndPopcountSWARMatchesScalar(t *testing.T) {
	a := make([]byte, 1089)
	b := make([]byte, 1089)
	var x uint64 = 0xe1034e575c371ab0
	for i := range a {
		x = x*6364136223846793005 + 1442695040888963407
		a[i] = byte(x >> 33)
		x = x*6364136223846793005 + 1442695040888963407
		b[i] = byte(x >> 33)
	}
	for n := 0; n <= len(a); n++ {
		var wantDiff uint64
		for i := 0; i < n; i++ {
			if a[i] != b[i] {
				wantDiff++
			}
		}
		if got := ByteDiff(a[:n], b[:n]); got != wantDiff {
			t.Fatalf("len=%d: ByteDiff=%d want=%d", n, got, wantDiff)
		}
	}
	if got := ByteDiff(a, a); got != 0 {
		t.Fatalf("ByteDiff(a, a) = %d, want 0", got)
	}
}

func BenchmarkXORFold64K(b *testing.B) {
	buf := bytes.Repeat([]byte{0x62, 0x55, 0xe1, 0x03, 0x4e, 0x57, 0x5c, 0x37}, 8192)
	b.SetBytes(int64(len(buf)))
	b.ResetTimer()
	var sink uint64
	for i := 0; i < b.N; i++ {
		sink ^= XORFold(buf)
	}
	if sink == 0xdeadbeef {
		b.Fatal(sink)
	}
}

func BenchmarkPopcount64K(b *testing.B) {
	buf := bytes.Repeat([]byte{0x62, 0x55, 0xe1, 0x03, 0x4e, 0x57, 0x5c, 0x37}, 8192)
	b.SetBytes(int64(len(buf)))
	b.ResetTimer()
	var sink uint64
	for i := 0; i < b.N; i++ {
		sink += Popcount(buf)
	}
	if sink == 0 {
		b.Fatal(sink)
	}
}

func BenchmarkByteDiff64K(b *testing.B) {
	a := bytes.Repeat([]byte{0x62, 0x55, 0xe1, 0x03, 0x4e, 0x57, 0x5c, 0x37}, 8192)
	c := bytes.Repeat([]byte{0x62, 0x5a, 0xe1, 0x03, 0x4e, 0x57, 0x5c, 0x38}, 8192)
	b.SetBytes(int64(len(a)))
	b.ResetTimer()
	var sink uint64
	for i := 0; i < b.N; i++ {
		sink += ByteDiff(a, c)
	}
	if sink == 0 {
		b.Fatal(sink)
	}
}

// Chained writers and concurrent readers must observe a state from the same
// generation as the fold, not a delayed store from an earlier writer.
func TestGate0x62StateChainedSnapshots(t *testing.T) {
	var g Gate0x62State
	const writers = 8
	const updates = 1000
	var wg sync.WaitGroup
	for i := 0; i < writers; i++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			for n := 0; n < updates; {
				fold, state := g.Snapshot()
				want := TritZero
				if fold != 0 {
					want = TritPos
					if fold%2 == 0 {
						want = TritNeg
					}
				}
				if state != want {
					t.Errorf("inconsistent snapshot: fold=%d state=%d want=%d", fold, state, want)
					return
				}
				nextState := TritPos
				if (fold+1)%2 == 0 {
					nextState = TritNeg
				}
				if g.AdvanceCAS(fold, fold+1, nextState) {
					n++
				}
			}
		}()
	}
	wg.Wait()
	fold, state := g.Snapshot()
	if fold != writers*updates || state != TritNeg {
		t.Fatalf("final snapshot=(%d,%d)", fold, state)
	}
	if g.AdvanceCAS(fold-1, fold+1, TritPos) || g.AdvanceCAS(fold, fold+1, Trit(2)) {
		t.Fatal("accepted stale fold or invalid trit")
	}
	if f, s := g.Snapshot(); f != fold || s != state {
		t.Fatal("rejected update changed the snapshot")
	}
}

func TestFrame32BIsOnlyAnXORChecksum(t *testing.T) {
	frame := SealFrame32B([]byte{0, 0}, nil, Gate0x62)
	// XOR cancellation is intentional in ABI v1, not evidence of authenticity.
	if !CheckFrame32B(frame, []byte{1, 1}, nil, Gate0x62) {
		t.Fatal("ABI v1 checksum behavior changed")
	}
}
