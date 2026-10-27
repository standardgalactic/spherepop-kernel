package main

import (
	"bytes"
	"os"
	"path/filepath"
	"strings"
	"testing"
)

func do(t *testing.T, stdin string, args ...string) (code int, out, errOut string) {
	t.Helper()
	var o, e bytes.Buffer
	code = run(args, strings.NewReader(stdin), &o, &e)
	return code, o.String(), e.String()
}

func TestReduceWithTrailingFlags(t *testing.T) {
	code, out, _ := do(t, "", "reduce", "S K K x", "--fuel", "100", "--trace")
	if code != exitOK {
		t.Fatalf("exit %d", code)
	}
	for _, want := range []string{"   0", "   1  S", "   2  K", "normal form in 2 steps (lo)"} {
		if !strings.Contains(out, want) {
			t.Errorf("output lacks %q:\n%s", want, out)
		}
	}
	if !strings.Contains(out, "\nx\n") {
		t.Errorf("result line missing:\n%s", out)
	}
}

func TestReduceExhaustedExitCode(t *testing.T) {
	code, out, _ := do(t, "", "reduce", "--fuel", "10", "--def", "w=S (S K K) (S K K)", "w w")
	if code != exitExhausted || !strings.Contains(out, "fuel exhausted after 10 steps") {
		t.Fatalf("exit %d, out %q", code, out)
	}
}

func TestRecordThenCheck(t *testing.T) {
	file := filepath.Join(t.TempDir(), "trace.json")
	if code, _, e := do(t, "", "reduce", "S K K x", "--out", file); code != exitOK {
		t.Fatalf("reduce exit %d: %s", code, e)
	}
	code, out, _ := do(t, "", "check", file, "--strategy")
	if code != exitOK || !strings.HasPrefix(out, "valid: 2 steps, final x (normal form)") {
		t.Fatalf("exit %d, out %q", code, out)
	}
	// Standard input works too.
	b, _ := os.ReadFile(file)
	if code, _, _ := do(t, string(b), "check", "-"); code != exitOK {
		t.Fatalf("stdin check exit %d", code)
	}
	// Tampering is reported and fails.
	bad := strings.Replace(string(b), `"rule": "K"`, `"rule": "I"`, 1)
	code, out, _ = do(t, bad, "check", "-")
	if code != exitFailure || !strings.HasPrefix(out, "invalid:") {
		t.Fatalf("tampered trace: exit %d, out %q", code, out)
	}
}

func TestScopedReduceFlags(t *testing.T) {
	code, out, _ := do(t, "", "reduce", "<K a b>_x", "--perm", "x=C")
	if code != exitOK || !strings.Contains(out, "<K a b>_x\nnormal form in 0 steps") {
		t.Fatalf("K should be stuck: exit %d, out %q", code, out)
	}
	code, out, _ = do(t, "", "reduce", "<K a b>_x", "--perm", "x=K")
	if code != exitOK || !strings.Contains(out, "<a>_x") {
		t.Fatalf("K should fire: exit %d, out %q", code, out)
	}
	// An unlabelled scope fails closed instead of guessing a permission.
	if code, _, e := do(t, "", "reduce", "<K a b>_x"); code != exitFailure || !strings.Contains(e, "label") {
		t.Fatalf("unknown label: exit %d, err %q", code, e)
	}
}

func TestUsageErrors(t *testing.T) {
	for _, args := range [][]string{
		{},
		{"nope"},
		{"reduce"},
		{"reduce", "a", "b"},
		{"reduce", "S K K", "--strategy", "zz"},
		{"reduce", "S K K", "--perm", "nolist"},
		{"reduce", "S K K", "--perm", "x=Q"},
		{"reduce", "S K K", "--absorb", "maybe"},
		{"reduce", "S K K", "--def", "bad"},
		{"reduce", "((", "--fuel", "1"},
		{"check"},
		{"test", "extra"},
	} {
		if code, _, _ := do(t, "", args...); code != exitUsage {
			t.Errorf("%v: exit %d, want %d", args, code, exitUsage)
		}
	}
	if code, _, _ := do(t, "", "check", filepath.Join(t.TempDir(), "missing.json")); code != exitFailure {
		t.Error("missing file should fail")
	}
}

func TestTestAndRulesCommands(t *testing.T) {
	code, out, _ := do(t, "", "test")
	if code != exitOK || !strings.Contains(out, "0 failed") || strings.Contains(out, "FAIL") {
		t.Fatalf("exit %d\n%s", code, out)
	}
	code, out, _ = do(t, "", "rules")
	if code != exitOK || !strings.Contains(out, "Abs") || !strings.Contains(out, "S f g x -> f x (g x)") {
		t.Fatalf("rules: exit %d\n%s", code, out)
	}
}

func TestSimAndCheckLog(t *testing.T) {
	file := filepath.Join(t.TempDir(), "log.json")
	code, out, e := do(t, "", "sim", "--entity", "loop=S (S K K) (S K K) (S (S K K) (S K K))",
		"--entity", "id=S K K x", "--budget", "3", "--ticks", "2", "--out", file)
	if code != exitOK {
		t.Fatalf("exit %d: %s", code, e)
	}
	for _, want := range []string{"tick 0   id           run  steps=2", "tick 1   id           skip", "loop         continues", "id           normal    x"} {
		if !strings.Contains(out, want) {
			t.Errorf("missing %q in:\n%s", want, out)
		}
	}
	code, out, _ = do(t, "", "checklog", file)
	if code != exitOK || !strings.HasPrefix(out, "valid: 4 scheduler events over 2 entities") {
		t.Fatalf("exit %d, out %q", code, out)
	}
	b, _ := os.ReadFile(file)
	bad := strings.Replace(string(b), `"budget": 3`, `"budget": 4`, 1)
	if code, out, _ := do(t, bad, "checklog", "-"); code != exitFailure || !strings.HasPrefix(out, "invalid:") {
		t.Fatalf("tampered log: exit %d, out %q", code, out)
	}
	for _, args := range [][]string{{"sim"}, {"sim", "--entity", "noequals"}, {"sim", "--entity", "a=((", "--ticks", "1"}, {"sim", "--entity", "a=K", "--sc", "maybe"}, {"checklog"}} {
		if code, _, _ := do(t, "", args...); code != exitUsage {
			t.Errorf("%v: exit %d", args, code)
		}
	}
}

func TestSimWorkersDoNotChangeTheLog(t *testing.T) {
	dir := t.TempDir()
	args := func(workers, file string) []string {
		return []string{"sim", "--entity", "a=S K K x", "--entity", "b=I (I (yield (K p q)))", "--entity", "c=W W W",
			"--entity", "d=K a b", "--budget", "2", "--ticks", "6", "--workers", workers, "--out", file}
	}
	var logs []string
	for _, w := range []string{"1", "3", "0"} {
		f := filepath.Join(dir, "log"+w+".json")
		if code, _, e := do(t, "", args(w, f)...); code != exitOK {
			t.Fatalf("workers %s: exit %d: %s", w, code, e)
		}
		b, _ := os.ReadFile(f)
		logs = append(logs, string(b))
	}
	if logs[0] != logs[1] || logs[0] != logs[2] {
		t.Fatal("the scheduler log depends on the number of workers")
	}
}

func TestCompile(t *testing.T) {
	code, out, _ := do(t, "", "compile", `\x y. x`)
	if code != exitOK || strings.TrimSpace(out) != "K" {
		t.Fatalf("exit %d, output %q", code, out)
	}
	// What compile prints must reduce to the expected result.
	code, out, _ = do(t, "", "compile", `(\x. x x) y`, "--def", "y=a")
	if code != exitOK {
		t.Fatalf("exit %d", code)
	}
	code, out, _ = do(t, "", "reduce", strings.TrimSpace(out))
	if code != exitOK || !strings.HasPrefix(out, "a a\n") {
		t.Fatalf("exit %d, output %q", code, out)
	}
	if code, _, _ := do(t, "", "compile", `\x.`); code != exitFailure {
		t.Fatalf("bad lambda gave exit %d", code)
	}
	if code, _, _ := do(t, "", "compile"); code != exitUsage {
		t.Fatalf("missing argument gave exit %d", code)
	}
}

func TestSettledScopeFlag(t *testing.T) {
	// Under the settled mode the Sc step waits for the inner Abs, and the
	// result is the same normal form as under the safe mode.
	for _, sc := range []string{"safe", "settled"} {
		code, out, _ := do(t, "", "reduce", "sc_x (<I>_x a)", "--absorb", "s", "--sc", sc, "--perm", "x=K")
		if code != exitOK || !strings.Contains(out, "<<a>_x>_x") {
			t.Fatalf("--sc %s: exit %d, output %q", sc, code, out)
		}
	}
	if code, _, _ := do(t, "", "reduce", "a", "--sc", "bogus"); code != exitUsage && code != exitFailure {
		t.Fatalf("bad scope mode gave exit %d", code)
	}
}

func headOf(t *testing.T, out string) string {
	t.Helper()
	for _, l := range strings.Split(out, "\n") {
		if rest, ok := strings.CutPrefix(l, "effects log head: "); ok {
			return strings.TrimSpace(rest)
		}
	}
	t.Fatalf("no head in output:\n%s", out)
	return ""
}

func TestArenaRunAndVerifyLogs(t *testing.T) {
	dir := t.TempDir()
	eff, sch := filepath.Join(dir, "e.jsonl"), filepath.Join(dir, "s.json")
	code, out, errOut := do(t, "", "arena", "../../examples/cruise.lam", "--frames", "40", "--effects", eff, "--sched", sch)
	if code != exitOK {
		t.Fatalf("exit %d: %s", code, errOut)
	}
	if !strings.Contains(out, "cell=b") || !strings.Contains(out, "committed=") {
		t.Fatalf("ship should reach cell b with committed effects:\n%s", out)
	}
	head := headOf(t, out)

	if code, out, _ := do(t, "", "checkeffects", eff, "--anchor", head); code != exitOK || !strings.Contains(out, "head matches the anchor") {
		t.Fatalf("checkeffects: exit %d, %q", code, out)
	}
	if code, out, _ := do(t, "", "checklog", sch); code != exitOK {
		t.Fatalf("checklog: exit %d, %q", code, out)
	}

	// Removing the tail leaves a valid chain, which only the anchor detects.
	b, _ := os.ReadFile(eff)
	lines := strings.SplitAfter(strings.TrimRight(string(b), "\n"), "\n")
	short := filepath.Join(dir, "short.jsonl")
	os.WriteFile(short, []byte(strings.Join(lines[:len(lines)-3], "")+"\n"), 0o644)
	if code, _, _ := do(t, "", "checkeffects", short); code != exitOK {
		t.Fatalf("a truncated chain should still verify bare, exit %d", code)
	}
	if code, _, _ := do(t, "", "checkeffects", short, "--anchor", head); code != exitFailure {
		t.Fatalf("a truncated log must fail against the anchor, exit %d", code)
	}
	// Changing a disposition breaks the chain.
	bad := filepath.Join(dir, "bad.jsonl")
	os.WriteFile(bad, []byte(strings.Replace(string(b), "committed", "denied", 1)), 0o644)
	if code, _, _ := do(t, "", "checkeffects", bad); code != exitFailure {
		t.Fatalf("a tampered log must fail, exit %d", code)
	}
}

func TestArenaIsReproducibleAndHonoursModes(t *testing.T) {
	_, a, _ := do(t, "", "arena", "../../examples/cruise.lam", "--frames", "30")
	_, b, _ := do(t, "", "arena", "../../examples/cruise.lam", "--frames", "30")
	if a != b {
		t.Fatalf("two runs differ:\n%s\n%s", a, b)
	}
	// The same behavior under the experimental configuration reaches the same state.
	_, c, _ := do(t, "", "arena", "../../examples/cruise.lam", "--frames", "30", "--absorb", "u", "--sc", "safe")
	// The world and the effects are the same. The log head differs, because
	// each entry cites the trace of the reduction that produced it and a trace
	// records its configuration; evidence follows the rules that were used.
	body := func(s string) string { return s[:strings.Index(s, "effects log head")] }
	if body(a) != body(c) {
		t.Fatalf("the experimental configuration changed the run:\n%s\n%s", a, c)
	}
	if headOf(t, a) == headOf(t, c) {
		t.Fatal("the log head should record which configuration produced the traces")
	}
}

func TestArenaStatefulExample(t *testing.T) {
	code, out, errOut := do(t, "", "arena", "../../examples/stateful.lam", "--registers", "--frames", "60")
	if code != exitOK || !strings.Contains(out, "reg=1") || !strings.Contains(out, "cell=b") {
		t.Fatalf("exit %d: %s%s", code, out, errOut)
	}
	// Without the register argument the program is applied to too few
	// arguments, never reaches a normal form with effects, and the ship stays.
	_, out, _ = do(t, "", "arena", "../../examples/stateful.lam", "--frames", "20")
	if !strings.Contains(out, "cell=a") {
		t.Fatalf("a program given too few observations should not act:\n%s", out)
	}
}

func TestArenaUsageErrors(t *testing.T) {
	for _, args := range [][]string{
		{"arena"},
		{"arena", "x.lam", "y.lam"},
		{"arena", "../../examples/cruise.lam", "--strategy", "zz"},
		{"arena", "../../examples/cruise.lam", "--sc", "zz"},
		{"checkeffects"},
	} {
		if code, _, _ := do(t, "", args...); code != exitUsage {
			t.Errorf("%v: exit %d, want %d", args, code, exitUsage)
		}
	}
	if code, _, _ := do(t, "", "arena", "/nonexistent.lam"); code != exitFailure {
		t.Errorf("a missing file should fail, got %d", code)
	}
	if code, _, _ := do(t, `\x.`, "arena", "-"); code != exitFailure {
		t.Errorf("a bad program should fail, got %d", code)
	}
}

func TestHostDefaultIsSettledAndOverridable(t *testing.T) {
	// The default must equal an explicit request for the settled pair.
	_, a, _ := do(t, "", "arena", "../../examples/cruise.lam", "--frames", "10")
	_, b, _ := do(t, "", "arena", "../../examples/cruise.lam", "--frames", "10", "--absorb", "s", "--sc", "settled")
	if a != b {
		t.Fatalf("the arena default is not settled/s:\n%s\n%s", a, b)
	}
	// And the sim default likewise: a term whose Sc argument has a pending Abs
	// waits under the host default and does not under safe.
	_, d, _ := do(t, "", "sim", "--entity", "e=sc_x (<I>_x a)", "--ticks", "1", "--budget", "1", "--perm", "x=K")
	_, s, _ := do(t, "", "sim", "--entity", "e=sc_x (<I>_x a)", "--ticks", "1", "--budget", "1", "--perm", "x=K", "--sc", "safe", "--absorb", "u")
	if d == s {
		t.Fatalf("sim default behaved like safe/u:\n%s", d)
	}
}

func TestArenaSchemaFeedsCheckEffects(t *testing.T) {
	dir := t.TempDir()
	eff := filepath.Join(dir, "fx.jsonl")
	if code, _, errs := do(t, "", "arena", "../../examples/cruise.lam", "--frames", "6", "--effects", eff); code != exitOK {
		t.Fatalf("arena: %d %s", code, errs)
	}
	code, schema, _ := do(t, "", "arena-schema")
	if code != exitOK || !strings.Contains(schema, `"door"`) {
		t.Fatalf("arena-schema: %d %q", code, schema)
	}
	sf := filepath.Join(dir, "schema.json")
	if err := os.WriteFile(sf, []byte(schema), 0o600); err != nil {
		t.Fatal(err)
	}
	if code, out, _ := do(t, "", "checkeffects", eff, "--schema", sf); code != exitOK {
		t.Fatalf("checkeffects with schema file: %d %s", code, out)
	}
	empty := filepath.Join(dir, "empty.json")
	os.WriteFile(empty, []byte(`{"targets":{}}`), 0o600)
	if code, _, _ := do(t, "", "checkeffects", eff, "--schema", empty); code != exitFailure {
		t.Fatalf("an empty schema accepted committed requests: %d", code)
	}
}
