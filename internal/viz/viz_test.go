package viz

import (
	"bufio"
	"encoding/json"
	"net/http"
	"net/http/httptest"
	"strings"
	"testing"

	"github.com/standardgalactic/spherepop-kernel/reduce"
	"github.com/standardgalactic/spherepop-kernel/term"
)

func TestIntensityEndpointsAndMonotone(t *testing.T) {
	if got := intensityOf(0); got != 150 {
		t.Errorf("empty = %d", got)
	}
	if got := intensityOf(reduce.PermAll); got != 1000 {
		t.Errorf("full = %d", got)
	}
	want := []int{150, 363, 575, 788, 1000}
	for n, w := range want {
		var p reduce.PermSet
		for i := 0; i < n; i++ {
			p |= 1 << uint(i)
		}
		if got := intensityOf(p); got != w {
			t.Errorf("%d permissions: %d, want %d", n, got, w)
		}
	}
	// only the four permission bits count
	if intensityOf(0xF0) != 150 {
		t.Error("bits outside the alphabet counted")
	}
}

func TestComplexitySaturates(t *testing.T) {
	cases := map[int]int{-5: 0, 0: 0, 1: 15, 32: 500, 63: 984, 64: 1000, 1 << 40: 1000}
	for size, want := range cases {
		if got := complexityOf(size); got != want {
			t.Errorf("size %d: %d, want %d", size, got, want)
		}
	}
}

func TestHuesAreFixedAndInRange(t *testing.T) {
	want := map[reduce.RuleID]int{"I": 174, "K": 330, "S": 145, "B": 48, "C": 28, "W": 275, "Sc": 195, "Abs": 120}
	for r, h := range want {
		if got := hueOf(r); got != h {
			t.Errorf("%s: %d, want %d", r, got, h)
		}
	}
	for _, r := range []reduce.RuleID{"", "X", "unknown-rule", "é"} {
		if h := hueOf(r); h < 0 || h >= 360 {
			t.Errorf("fallback hue %d out of range for %q", h, r)
		}
		if hueOf(r) != hueOf(r) {
			t.Error("fallback not deterministic")
		}
	}
}

func TestFromRunObservesTheReducer(t *testing.T) {
	c := reduce.DefaultConfig()
	start, err := term.Parse("S K K a")
	if err != nil {
		t.Fatal(err)
	}
	evs, err := FromRun(c, start, reduce.LeftmostOutermost, 100)
	if err != nil {
		t.Fatal(err)
	}
	full, err := c.Reduce(start, reduce.LeftmostOutermost, 100)
	if err != nil {
		t.Fatal(err)
	}
	if uint64(len(evs)) != full.Steps {
		t.Fatalf("%d events for %d steps", len(evs), full.Steps)
	}
	for i, e := range evs {
		if e.Rule != full.Trace[i].Rule || e.Digest != full.Trace[i].After.String() {
			t.Fatalf("event %d differs from the reducer's trace", i)
		}
		if e.Perm != reduce.PermAll {
			t.Fatalf("event %d: root permission expected, got %v", i, e.Perm)
		}
	}
}

func TestPermissionNarrowsInsideBrackets(t *testing.T) {
	c := reduce.DefaultConfig()
	c.Perm = map[string]reduce.PermSet{"x": reduce.PermK}
	start, _ := term.Parse("<K a b>_x")
	evs, err := FromRun(c, start, reduce.LeftmostOutermost, 10)
	if err != nil || len(evs) != 1 {
		t.Fatalf("%v %v", evs, err)
	}
	if evs[0].Perm != reduce.PermK {
		t.Errorf("perm = %v, want K only", evs[0].Perm)
	}
	if got := Map(evs[0]).Intensity; got != intensityOf(reduce.PermK) {
		t.Errorf("intensity %d", got)
	}
}

func TestFromRunHonoursFuel(t *testing.T) {
	c := reduce.DefaultConfig()
	start, _ := term.Parse("W W W")
	evs, err := FromRun(c, start, reduce.LeftmostOutermost, 7)
	if err != nil || len(evs) != 7 {
		t.Fatalf("%d events, %v", len(evs), err)
	}
}

func TestMapIsPure(t *testing.T) {
	e := Event{Rule: "K", Perm: reduce.PermK | reduce.PermC, TermSize: 10}
	if Map(e) != Map(e) {
		t.Error("Map not deterministic")
	}
}

func TestHandlerServesIdenticalBytesForIdenticalRuns(t *testing.T) {
	c := reduce.DefaultConfig()
	start, _ := term.Parse("S K K a")
	evs, _ := FromRun(c, start, reduce.LeftmostOutermost, 100)
	srv := httptest.NewServer(Handler(Project(evs)))
	defer srv.Close()
	srv2 := httptest.NewServer(Handler(Project(evs)))
	defer srv2.Close()

	get := func(base, path string) (int, string) {
		resp, err := http.Get(base + path)
		if err != nil {
			t.Fatal(err)
		}
		defer resp.Body.Close()
		var sb strings.Builder
		sc := bufio.NewScanner(resp.Body)
		for sc.Scan() {
			sb.WriteString(sc.Text() + "\n")
		}
		return resp.StatusCode, sb.String()
	}
	for _, p := range []string{"/states", "/state", "/state?i=0", "/events"} {
		c1, b1 := get(srv.URL, p)
		c2, b2 := get(srv2.URL, p)
		if c1 != 200 || c1 != c2 || b1 != b2 {
			t.Errorf("%s: %d %d, equal=%v", p, c1, c2, b1 == b2)
		}
	}
	_, body := get(srv.URL, "/states")
	var got []State
	if err := json.Unmarshal([]byte(body), &got); err != nil || len(got) != len(evs) {
		t.Fatalf("states: %v, %d entries", err, len(got))
	}
	_, ev := get(srv.URL, "/events")
	if strings.Count(ev, "event: step") != len(evs) {
		t.Errorf("event stream has %d frames, want %d", strings.Count(ev, "event: step"), len(evs))
	}
	for _, bad := range []string{"/state?i=-1", "/state?i=99", "/state?i=01", "/state?i=x"} {
		if code, _ := get(srv.URL, bad); code != http.StatusBadRequest {
			t.Errorf("%s: status %d, want 400", bad, code)
		}
	}
	empty := httptest.NewServer(Handler(nil))
	defer empty.Close()
	if code, _ := get(empty.URL, "/state"); code != http.StatusNotFound {
		t.Errorf("empty /state: %d", code)
	}
}
