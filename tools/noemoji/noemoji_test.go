package main

import (
	"os"
	"path/filepath"
	"testing"
)

func TestStrip(t *testing.T) {
	cases := []struct{ in, want string }{
		{"## \U0001F680 Quick start", "## Quick start"},
		{"# \u2728\uFE0F Features \u2728", "# Features"},
		{"- \u2705 done", "- done"},
		{"fast \U0001F525 and small", "fast and small"},
		{"family \U0001F468\u200D\U0001F469\u200D\U0001F467 here", "family here"},
		{"flag \U0001F1E8\U0001F1E6", "flag"},
		{"1\uFE0F\u20E3 first", "1 first"},
		{"  indented \U0001F600 text", "  indented text"},
		{"\U0001F600", ""},
		{"plain text, math ∞ ⟦x⟧ and (c) ©", "plain text, math ∞ ⟦x⟧ and (c) ©"},
		{"arrows → and ≤ stay", "arrows → and ≤ stay"},
		{"zero\u200Dwidth joiner alone stays", "zero\u200Dwidth joiner alone stays"},
	}
	for _, c := range cases {
		got, _ := strip(c.in)
		if got != c.want {
			t.Errorf("strip(%q) = %q, want %q", c.in, got, c.want)
		}
	}
}

func TestStripReportsChange(t *testing.T) {
	if _, ch := strip("no emoji here"); ch {
		t.Error("unchanged line reported as changed")
	}
	if _, ch := strip("one \U0001F680"); !ch {
		t.Error("changed line not reported")
	}
}

func TestScanFixRemovesEmojiAndLeavesBinaryAlone(t *testing.T) {
	dir := t.TempDir()
	md := filepath.Join(dir, "README.md")
	bin := filepath.Join(dir, "img.bin")
	os.WriteFile(md, []byte("# \U0001F680 Title\n\nbody\n- \u2705 item\n"), 0o644)
	binData := []byte{0, 1, 2, 0xF0, 0x9F, 0x9A, 0x80}
	os.WriteFile(bin, binData, 0o644)

	found, err := Scan([]string{dir}, false)
	if err != nil || len(found) != 2 {
		t.Fatalf("check mode: found %d, err %v", len(found), err)
	}
	if b, _ := os.ReadFile(md); string(b) != "# \U0001F680 Title\n\nbody\n- \u2705 item\n" {
		t.Fatal("check mode modified the file")
	}
	if _, err := Scan([]string{dir}, true); err != nil {
		t.Fatal(err)
	}
	b, _ := os.ReadFile(md)
	if string(b) != "# Title\n\nbody\n- item\n" {
		t.Fatalf("fixed file = %q", b)
	}
	if again, _ := Scan([]string{dir}, false); len(again) != 0 {
		t.Fatalf("emoji remain after fix: %v", again)
	}
	if got, _ := os.ReadFile(bin); string(got) != string(binData) {
		t.Fatal("binary file was modified")
	}
}

// TestRepositoryHasNoEmoji is the check that keeps the tree clean.
func TestRepositoryHasNoEmoji(t *testing.T) {
	found, err := Scan([]string{"../.."}, false)
	if err != nil {
		t.Fatal(err)
	}
	for _, f := range found {
		t.Errorf("%s:%d contains emoji: %s", f.Path, f.Line, f.Text)
	}
}
