// Package main implements noemoji, which finds and removes emoji from text
// files. The repository keeps its prose, code and documentation free of emoji
// and decorative pictographs; this tool is both the check and the cleaner.
//
//	noemoji [-fix] [paths...]
//
// Without -fix it lists every offending line and exits 1 if there are any.
// With -fix it rewrites the files, removing the emoji and the whitespace the
// removal leaves behind, and exits 0. With no paths it scans the current
// directory. Directories named .git are skipped, binary files are skipped, and
// a file whose path appears in the allow list below is left alone.
package main

import (
	"bytes"
	"flag"
	"fmt"
	"io/fs"
	"os"
	"path/filepath"
	"strings"
	"unicode/utf8"
)

// allow lists slash-separated path prefixes that may contain emoji, for
// example test data that exercises Unicode handling on purpose. It is empty
// because nothing in the tree needs it.
var allow = []string{}

func isEmoji(r rune) bool {
	switch {
	case r >= 0x1F000 && r <= 0x1FAFF: // pictographs, emoticons, transport, flags, symbols
		return true
	case r >= 0x2600 && r <= 0x27BF: // miscellaneous symbols and dingbats
		return true
	case r >= 0x2B50 && r <= 0x2B55, r == 0x2B1B, r == 0x2B1C:
		return true
	case r >= 0x231A && r <= 0x231B, r >= 0x23E9 && r <= 0x23FA:
		return true
	case r == 0x2934, r == 0x2935, r == 0x3030, r == 0x303D, r == 0x3297, r == 0x3299:
		return true
	case r == 0x20E3: // combining keycap
		return true
	}
	return false
}

func isGlue(r rune) bool { return r == 0xFE0F || r == 0xFE0E || r == 0x200D }

// strip returns line without emoji, and whether it changed. Variation
// selectors and joiners are removed only where they belong to an emoji
// sequence, so ordinary text that uses them is untouched. Spaces left on
// either side of a removal collapse to one, and a heading marker keeps a single
// space before its text.
func strip(line string) (string, bool) {
	rs := []rune(line)
	out := make([]rune, 0, len(rs))
	changed := false
	for i := 0; i < len(rs); i++ {
		r := rs[i]
		drop := isEmoji(r)
		if !drop && isGlue(r) {
			prevEmoji := i > 0 && (isEmoji(rs[i-1]) || isGlue(rs[i-1]))
			nextEmoji := i+1 < len(rs) && (isEmoji(rs[i+1]) || rs[i+1] == 0x20E3)
			drop = prevEmoji || nextEmoji
		}
		if !drop {
			out = append(out, r)
			continue
		}
		changed = true
		if len(out) > 0 && out[len(out)-1] == ' ' && i+1 < len(rs) && rs[i+1] == ' ' {
			i++
		}
	}
	if !changed {
		return line, false
	}
	s := string(out)
	s = strings.TrimRight(s, " \t")
	s = strings.TrimLeft(s, " \t")
	if len(s) < len(line) && strings.HasPrefix(strings.TrimLeft(line, " \t"), "#") {
		// "## <emoji> Title" becomes "## Title".
		t := strings.TrimLeft(s, "#")
		s = s[:len(s)-len(t)] + " " + strings.TrimLeft(t, " ")
		s = strings.TrimRight(s, " ")
	}
	if ind := leadingSpace(line); ind != "" && s != "" {
		s = ind + s
	}
	return s, true
}

func leadingSpace(s string) string {
	return s[:len(s)-len(strings.TrimLeft(s, " \t"))]
}

func allowed(path string) bool {
	p := filepath.ToSlash(path)
	for _, a := range allow {
		if strings.HasPrefix(p, a) {
			return true
		}
	}
	return false
}

func isText(b []byte) bool { return !bytes.Contains(b, []byte{0}) && utf8.Valid(b) }

// Finding is one offending line.
type Finding struct {
	Path string
	Line int
	Text string
}

// Scan reports every line under the given roots that contains emoji. When fix
// is set it rewrites those files and still returns what it found.
func Scan(roots []string, fix bool) ([]Finding, error) {
	var found []Finding
	for _, root := range roots {
		err := filepath.WalkDir(root, func(path string, d fs.DirEntry, err error) error {
			if err != nil {
				return err
			}
			if d.IsDir() {
				if d.Name() == ".git" {
					return filepath.SkipDir
				}
				return nil
			}
			if !d.Type().IsRegular() || allowed(path) {
				return nil
			}
			b, err := os.ReadFile(path)
			if err != nil {
				return err
			}
			if !isText(b) {
				return nil
			}
			lines := strings.Split(string(b), "\n")
			dirty := false
			for i, ln := range lines {
				ns, ch := strip(ln)
				if !ch {
					continue
				}
				dirty = true
				found = append(found, Finding{Path: path, Line: i + 1, Text: ln})
				lines[i] = ns
			}
			if fix && dirty {
				return os.WriteFile(path, []byte(strings.Join(lines, "\n")), 0o644)
			}
			return nil
		})
		if err != nil {
			return found, err
		}
	}
	return found, nil
}

func main() {
	fix := flag.Bool("fix", false, "rewrite files, removing emoji")
	flag.Parse()
	roots := flag.Args()
	if len(roots) == 0 {
		roots = []string{"."}
	}
	found, err := Scan(roots, *fix)
	if err != nil {
		fmt.Fprintln(os.Stderr, "noemoji:", err)
		os.Exit(2)
	}
	for _, f := range found {
		fmt.Printf("%s:%d: %s\n", f.Path, f.Line, strings.TrimSpace(f.Text))
	}
	if len(found) > 0 && !*fix {
		fmt.Fprintf(os.Stderr, "noemoji: %d line(s) contain emoji; run with -fix to remove them\n", len(found))
		os.Exit(1)
	}
}
