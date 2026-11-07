package main

import (
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"reflect"

	"github.com/standardgalactic/spherepop-kernel/reduce"
	"github.com/standardgalactic/spherepop-kernel/supervised"
	"github.com/standardgalactic/spherepop-kernel/term"
	"github.com/standardgalactic/spherepop-kernel/trace"
)

const mutFuel = 14

type base struct {
	spec  reduce.ConfigSpec
	cfg   reduce.Config
	start *term.Term
	strat reduce.Strategy
	doc   trace.Document
	audit supervised.Audit
}

// tsum, sealT and friends recompute the scoped design's hash chain from the
// published definition, so the harness can forge records a tamperer who
// re-chains would produce without touching the trace package.
func tsum(parts ...[]byte) string { return sumHex(parts...) }

func sealT(d *trace.Document) {
	b, _ := json.Marshal(d.Config)
	prev := tsum([]byte(trace.Format), []byte(d.StartDigest), []byte(tsum([]byte("spherepop-config/1"), b)))
	for i := range d.Steps {
		s := &d.Steps[i]
		s.Link = tsum([]byte(prev), []byte(s.Rule), []byte(s.Path), []byte(s.After))
		prev = s.Link
	}
	d.Head = prev
}

func copyT(d trace.Document) trace.Document {
	d.Steps = append([]trace.StepRecord{}, d.Steps...)
	return d
}

func copyA(a supervised.Audit) supervised.Audit {
	a.Entries = append([]supervised.Entry{}, a.Entries...)
	return a
}

func renumber(a *supervised.Audit) {
	for i := range a.Entries {
		a.Entries[i].Seq = i
	}
}

func idx(a supervised.Audit, decision string) []int {
	var out []int
	for i, e := range a.Entries {
		if e.Decision == decision {
			out = append(out, i)
		}
	}
	return out
}

func flip(s string) string {
	if s == "" {
		return "0"
	}
	c := byte('0')
	if s[0] == '0' {
		c = '1'
	}
	return string(c) + s[1:]
}

func otherRule(r reduce.RuleID) reduce.RuleID {
	for _, c := range []reduce.RuleID{reduce.RuleI, reduce.RuleB, reduce.RuleC, reduce.RuleK, reduce.RuleW, reduce.RuleS} {
		if c != r {
			return c
		}
	}
	return r
}

func flatOf(start *term.Term) reduce.Config {
	c := reduce.Config{Root: reduce.PermAll, Absorb: reduce.AbsAny, Sc: reduce.ScAny, Perm: map[string]reduce.PermSet{}}
	for _, l := range start.Labels() {
		c.Perm[l] = reduce.PermAll
	}
	return c
}

// buildBases picks n runs, one per configuration spread over the corpus, each
// the first run with at least three accepted steps and a refusal.
func buildBases(n int) ([]base, error) {
	cfgs := configs()
	terms := append(handTerms(), randomTerms(2, 60, 5)...)
	var out []base
	used := map[int]bool{}
	for k := 0; k < n; k++ {
		for ci := k * len(cfgs) / n; ci < len(cfgs) && len(out) == k; ci++ {
			if used[ci] {
				continue
			}
			nc := cfgs[ci]
			for _, start := range terms {
				for _, st := range strategies {
					res, audit, err := supervised.Run(nc.spec, start, st, mutFuel)
					if err != nil {
						return nil, err
					}
					if res.Steps < 3 || res.Refused < 1 {
						continue
					}
					_, doc, err := trace.Record(nc.cfg, start, st, mutFuel)
					if err != nil {
						return nil, err
					}
					used[ci] = true
					out = append(out, base{nc.spec, nc.cfg, start, st, doc, audit})
					goto next
				}
			}
		}
	next:
		if len(out) != k+1 {
			return nil, fmt.Errorf("no base run for slot %d", k)
		}
	}
	return out, nil
}

type verdict struct{ nT, trace, nA, log, replay int }

type row struct {
	name, class string
	strict      bool
	t           func(b base, d *trace.Document) bool
	a           func(b base, a *supervised.Audit) bool
}

func (r row) judge(bases []base) verdict {
	var v verdict
	for _, b := range bases {
		if r.t != nil {
			d := copyT(b.doc)
			if r.t(b, &d) {
				v.nT++
				if _, err := trace.Check(d, trace.Options{RequireStrategy: r.strict, Fuel: mutFuel}); err != nil {
					v.trace++
				}
			}
		}
		if r.a != nil {
			a := copyA(b.audit)
			if r.a(b, &a) {
				v.nA++
				if supervised.CheckLog(a, supervised.Options{Fuel: mutFuel}) != nil {
					v.log++
				}
				if supervised.CheckReplay(a, supervised.Options{RequireStrategy: r.strict, Fuel: mutFuel}) != nil {
					v.replay++
				}
			}
		}
	}
	return v
}

// prefixState returns the term after the first k entries of a.
func prefixState(a supervised.Audit, k int) *term.Term {
	cur := term.MustParse(a.Start)
	flat := flatOf(cur)
	for _, e := range a.Entries[:k] {
		if e.Decision == "allow" {
			var err error
			if cur, err = flat.Apply(cur, term.Path(e.Path), reduce.RuleID(e.Rule)); err != nil {
				panic(err)
			}
		}
	}
	return cur
}

// forged builds the record of a worker that ignores the policy from the
// first refusal on: it takes the refused step anyway and carries on under a
// flat configuration. The records are self-consistent.
func forgedT(b base) (trace.Document, bool) {
	di := idx(b.audit, "deny")
	if len(di) == 0 {
		return trace.Document{}, false
	}
	k := 0
	for _, e := range b.audit.Entries[:di[0]] {
		if e.Decision == "allow" {
			k++
		}
	}
	cur := b.start
	for _, s := range b.doc.Steps[:k] {
		cur, _ = b.cfg.Apply(cur, term.Path(s.Path), s.Rule)
	}
	flat := flatOf(b.start)
	e := b.audit.Entries[di[0]]
	next, err := flat.Apply(cur, term.Path(e.Path), reduce.RuleID(e.Rule))
	if err != nil {
		return trace.Document{}, false
	}
	flat.Trace = true
	rest, err := flat.Reduce(next, b.strat, mutFuel-uint64(k)-1)
	if err != nil {
		return trace.Document{}, false
	}
	d := copyT(b.doc)
	d.Steps = append(d.Steps[:k:k], trace.StepRecord{Rule: reduce.RuleID(e.Rule), Path: e.Path, After: next.Digest().String()})
	for _, s := range rest.Trace {
		d.Steps = append(d.Steps, trace.StepRecord{Rule: s.Rule, Path: string(s.Path), After: s.After.String()})
	}
	d.Final, d.FinalDigest, d.Exhausted = rest.Term.String(), rest.Term.Digest().String(), rest.Exhausted
	sealT(&d)
	return d, true
}

func forgedA(b base, a *supervised.Audit) bool {
	di := idx(b.audit, "deny")
	if len(di) == 0 {
		return false
	}
	cur := prefixState(b.audit, di[0])
	flat := flatOf(b.start)
	e := b.audit.Entries[di[0]]
	next, err := flat.Apply(cur, term.Path(e.Path), reduce.RuleID(e.Rule))
	if err != nil {
		return false
	}
	k := 0
	for _, x := range b.audit.Entries[:di[0]] {
		if x.Decision == "allow" {
			k++
		}
	}
	flat.Trace = true
	rest, err := flat.Reduce(next, b.strat, mutFuel-uint64(k)-1)
	if err != nil {
		return false
	}
	a.Entries = append(a.Entries[:di[0]:di[0]], supervised.Entry{Rule: e.Rule, Path: e.Path, Decision: "allow", Mask: e.Mask, After: next.Digest().String()})
	for _, s := range rest.Trace {
		a.Entries = append(a.Entries, supervised.Entry{Rule: string(s.Rule), Path: string(s.Path), Decision: "allow", Mask: ".", After: s.After.String()})
	}
	renumber(a)
	a.Final, a.FinalDigest, a.Exhausted = rest.Term.String(), rest.Term.Digest().String(), rest.Exhausted
	_ = supervised.Seal(a)
	return true
}

// loosened is a configuration that permits more than the agreed one.
func loosened(spec reduce.ConfigSpec) reduce.ConfigSpec {
	s := spec
	s.Root = reduce.PermAll.Names()
	s.Perm = map[string][]string{}
	for l := range spec.Perm {
		s.Perm[l] = reduce.PermAll.Names()
	}
	s.Absorb, s.Sc = "any", "any"
	return s
}

func looseCfg(b base) (reduce.ConfigSpec, reduce.Config) {
	s := loosened(b.spec)
	c, _ := s.Config()
	return s, c
}

func loosenT(b base, d *trace.Document) bool {
	_, c := looseCfg(b)
	_, doc, err := trace.Record(c, b.start, b.strat, mutFuel)
	if err != nil || doc.Head == b.doc.Head {
		return false
	}
	*d = doc
	return true
}

func loosenA(b base, a *supervised.Audit) bool {
	s, _ := looseCfg(b)
	_, audit, err := supervised.Run(s, b.start, b.strat, mutFuel)
	if err != nil || audit.Head == b.audit.Head {
		return false
	}
	*a = audit
	return true
}

var opposite = map[reduce.Strategy]reduce.Strategy{
	reduce.LeftmostOutermost: reduce.RightmostInnermost, reduce.RightmostInnermost: reduce.LeftmostOutermost,
	reduce.RightmostOutermost: reduce.LeftmostInnermost, reduce.LeftmostInnermost: reduce.RightmostOutermost,
}

func offStratT(b base, d *trace.Document) bool {
	_, doc, err := trace.Record(b.cfg, b.start, opposite[b.strat], mutFuel)
	if err != nil || reflect.DeepEqual(doc.Steps, b.doc.Steps) {
		return false
	}
	doc.Strategy = b.strat.String()
	*d = doc
	return true
}

func offStratA(b base, a *supervised.Audit) bool {
	_, audit, err := supervised.Run(b.spec, b.start, opposite[b.strat], mutFuel)
	if err != nil {
		return false
	}
	same := len(audit.Entries) == len(b.audit.Entries)
	for i := 0; same && i < len(audit.Entries); i++ {
		x, y := audit.Entries[i], b.audit.Entries[i]
		same = x.Rule == y.Rule && x.Path == y.Path && x.Decision == y.Decision
	}
	if same {
		return false
	}
	audit.Strategy = b.strat.String()
	_ = supervised.Seal(&audit)
	*a = audit
	return true
}

func rows() []row {
	rec := func(sealed bool, mt func(*trace.Document) bool, ma func(*supervised.Audit) bool) (func(base, *trace.Document) bool, func(base, *supervised.Audit) bool) {
		return func(_ base, d *trace.Document) bool {
				if !mt(d) {
					return false
				}
				if sealed {
					sealT(d)
				}
				return true
			}, func(_ base, a *supervised.Audit) bool {
				if !ma(a) {
					return false
				}
				renumber(a)
				if sealed {
					_ = supervised.Seal(a)
				}
				return true
			}
	}
	first := func(a *supervised.Audit) int { return idx(*a, "allow")[0] }
	swapT := func(d *trace.Document) bool { d.Steps[0], d.Steps[1] = d.Steps[1], d.Steps[0]; return true }
	swapA := func(a *supervised.Audit) bool {
		ai := idx(*a, "allow")
		a.Entries[ai[0]], a.Entries[ai[1]] = a.Entries[ai[1]], a.Entries[ai[0]]
		return true
	}
	delT := func(d *trace.Document) bool { d.Steps = append(d.Steps[:0:0], d.Steps[1:]...); return true }
	delA := func(a *supervised.Audit) bool {
		i := first(a)
		a.Entries = append(a.Entries[:i:i], a.Entries[i+1:]...)
		return true
	}
	dupT := func(d *trace.Document) bool {
		d.Steps = append(d.Steps[:1:1], append([]trace.StepRecord{d.Steps[0]}, d.Steps[1:]...)...)
		return true
	}
	dupA := func(a *supervised.Audit) bool {
		i := first(a)
		a.Entries = append(a.Entries[:i+1:i+1], append([]supervised.Entry{a.Entries[i]}, a.Entries[i+1:]...)...)
		return true
	}
	lastT := func(d *trace.Document) bool { d.Steps = d.Steps[:len(d.Steps)-1]; return true }
	lastA := func(a *supervised.Audit) bool {
		ai := idx(*a, "allow")
		i := ai[len(ai)-1]
		a.Entries = append(a.Entries[:i:i], a.Entries[i+1:]...)
		return true
	}
	var rs []row
	add := func(name, class string, sealed bool, mt func(*trace.Document) bool, ma func(*supervised.Audit) bool) {
		t, a := rec(sealed, mt, ma)
		rs = append(rs, row{name: name, class: class, t: t, a: a})
	}
	// Tampering that leaves the chain broken.
	add("link altered", "unsealed", false,
		func(d *trace.Document) bool { d.Steps[0].Link = flip(d.Steps[0].Link); return true },
		func(a *supervised.Audit) bool { a.Entries[0].Link = flip(a.Entries[0].Link); return true })
	add("result digest altered", "unsealed", false,
		func(d *trace.Document) bool { d.Steps[0].After = flip(d.Steps[0].After); return true },
		func(a *supervised.Audit) bool { a.Entries[0].After = flip(a.Entries[0].After); return true })
	add("rule altered", "unsealed", false,
		func(d *trace.Document) bool { d.Steps[0].Rule = otherRule(d.Steps[0].Rule); return true },
		func(a *supervised.Audit) bool {
			i := first(a)
			a.Entries[i].Rule = string(otherRule(reduce.RuleID(a.Entries[i].Rule)))
			return true
		})
	add("path altered", "unsealed", false,
		func(d *trace.Document) bool { d.Steps[0].Path += "L"; return true },
		func(a *supervised.Audit) bool { a.Entries[0].Path += "L"; return true })
	add("head altered", "unsealed", false,
		func(d *trace.Document) bool { d.Head = flip(d.Head); return true },
		func(a *supervised.Audit) bool { a.Head = flip(a.Head); return true })
	add("two accepted steps swapped", "unsealed", false, swapT, swapA)
	add("an accepted step deleted", "unsealed", false, delT, delA)
	add("an accepted step duplicated", "unsealed", false, dupT, dupA)
	add("last accepted step dropped", "unsealed", false, lastT, lastA)
	// Tampering by someone who re-chains: only a replay can notice.
	add("rule changed", "sealed", true,
		func(d *trace.Document) bool { d.Steps[0].Rule = otherRule(d.Steps[0].Rule); return true },
		func(a *supervised.Audit) bool {
			i := first(a)
			a.Entries[i].Rule = string(otherRule(reduce.RuleID(a.Entries[i].Rule)))
			return true
		})
	add("path made invalid", "sealed", true,
		func(d *trace.Document) bool { d.Steps[0].Path = "Z"; return true },
		func(a *supervised.Audit) bool { a.Entries[first(a)].Path = "Z"; return true })
	add("result digest wrong", "sealed", true,
		func(d *trace.Document) bool { d.Steps[0].After = flip(d.Steps[0].After); return true },
		func(a *supervised.Audit) bool {
			a.Entries[first(a)].After = flip(a.Entries[first(a)].After)
			return true
		})
	add("final text changed", "sealed", true,
		func(d *trace.Document) bool { d.Final = "zz"; return true },
		func(a *supervised.Audit) bool { a.Final = "zz"; return true })
	add("final digest changed", "sealed", true,
		func(d *trace.Document) bool { d.FinalDigest = flip(d.FinalDigest); return true },
		func(a *supervised.Audit) bool { a.FinalDigest = flip(a.FinalDigest); return true })
	add("exhaustion flag flipped", "sealed", true,
		func(d *trace.Document) bool { d.Exhausted = !d.Exhausted; return true },
		func(a *supervised.Audit) bool { a.Exhausted = !a.Exhausted; return true })
	add("fuel below the steps taken", "sealed", true,
		func(d *trace.Document) bool { d.Fuel = uint64(len(d.Steps)) - 1; return true },
		func(a *supervised.Audit) bool { a.Fuel = uint64(len(idx(*a, "allow"))) - 1; return true })
	add("an accepted step deleted", "sealed", true, delT, delA)
	add("an accepted step duplicated", "sealed", true, dupT, dupA)
	add("two accepted steps swapped", "sealed", true, swapT, swapA)
	// Records that break the policy or the strategy.
	rs = append(rs, row{name: "forbidden step forged as accepted", class: "policy",
		t: func(b base, d *trace.Document) bool {
			f, ok := forgedT(b)
			*d = f
			return ok
		}, a: forgedA})
	rs = append(rs, row{name: "policy loosened, honest run under it", class: "policy", t: loosenT, a: loosenA})
	rs = append(rs, row{name: "steps not those of the claimed strategy", class: "strategy", strict: true, t: offStratT, a: offStratA})
	// Tampering with what only the audit log contains.
	aud := func(name string, strict bool, f func(b base, a *supervised.Audit) bool) {
		rs = append(rs, row{name: name, class: "audit only", strict: strict, a: func(b base, a *supervised.Audit) bool {
			if !f(b, a) {
				return false
			}
			renumber(a)
			_ = supervised.Seal(a)
			return true
		}})
	}
	delRefusal := func(_ base, a *supervised.Audit) bool {
		di := idx(*a, "deny")
		if len(di) == 0 {
			return false
		}
		a.Entries = append(a.Entries[:di[0]:di[0]], a.Entries[di[0]+1:]...)
		return true
	}
	aud("refusal entry deleted", false, delRefusal)
	aud("refusal entry deleted, strategy required", true, delRefusal)
	aud("acceptance recorded as a refusal", false, func(b base, a *supervised.Audit) bool {
		i := first(a)
		before := prefixState(*a, i)
		a.Entries = a.Entries[:i+1]
		a.Entries[i].Decision, a.Entries[i].After = "deny", before.Digest().String()
		a.Final, a.FinalDigest, a.Exhausted = before.String(), before.Digest().String(), false
		return true
	})
	aud("mask altered", false, func(_ base, a *supervised.Audit) bool {
		if a.Entries[0].Mask == "WKC" {
			a.Entries[0].Mask = "W"
		} else {
			a.Entries[0].Mask = "WKC"
		}
		return true
	})
	aud("refusal inserted for a permitted step", false, func(_ base, a *supervised.Audit) bool {
		i := first(a)
		e := a.Entries[i]
		ins := supervised.Entry{Rule: e.Rule, Path: e.Path, Decision: "deny", Mask: e.Mask, After: prefixState(*a, i).Digest().String()}
		a.Entries = append(a.Entries[:i:i], append([]supervised.Entry{ins}, a.Entries[i:]...)...)
		return true
	})
	return rs
}

func runMutate() error {
	bases, err := buildBases(12)
	if err != nil {
		return err
	}
	// The harness must reproduce honest records exactly and every checker
	// must accept them.
	bad := 0
	for _, b := range bases {
		d := copyT(b.doc)
		sealT(&d)
		a := copyA(b.audit)
		_ = supervised.Seal(&a)
		strict := supervised.Options{RequireStrategy: true, Fuel: mutFuel}
		if _, err := trace.Check(b.doc, trace.Options{RequireStrategy: true, Fuel: mutFuel}); err != nil ||
			supervised.CheckLog(b.audit, strict) != nil || supervised.CheckReplay(b.audit, strict) != nil ||
			!reflect.DeepEqual(d, b.doc) || !reflect.DeepEqual(a, b.audit) {
			bad++
		}
	}
	fmt.Println("mutation matrix")
	fmt.Printf("  base runs: %d (one per configuration spread over the corpus, the first run with at least 3 accepted steps and a refusal, fuel %d)\n", len(bases), mutFuel)
	fmt.Printf("  honest base records rejected, or sealed differently by the harness: %d\n", bad)
	fmt.Printf("  %-44s %-11s %3s  %-7s %-7s %-7s  (rejected / applicable)\n", "mutation", "class", "n", "trace", "log", "replay")
	for _, r := range rows() {
		v := r.judge(bases)
		n, tr := v.nA, "-"
		if r.t != nil {
			tr = fmt.Sprintf("%d/%d", v.trace, v.nT)
			n = v.nT
		}
		lg, rp := "-", "-"
		if r.a != nil {
			lg, rp = fmt.Sprintf("%d/%d", v.log, v.nA), fmt.Sprintf("%d/%d", v.replay, v.nA)
		}
		fmt.Printf("  %-44s %-11s %3d  %-7s %-7s %-7s\n", r.name, r.class, n, tr, lg, rp)
	}
	// A host that compares the recorded configuration with the one it agreed
	// rejects a loosened-policy record under either design.
	rejected, total := 0, 0
	for _, b := range bases {
		var d trace.Document
		var a supervised.Audit
		if loosenT(b, &d) && loosenA(b, &a) {
			total++
			if !reflect.DeepEqual(d.Config, b.spec) && !reflect.DeepEqual(a.Config, b.spec) {
				rejected++
			}
		}
	}
	fmt.Printf("  host comparison of the recorded configuration with the agreed one rejects %d of %d loosened-policy records (the same comparison serves both designs)\n", rejected, total)
	return nil
}

func sumHex(parts ...[]byte) string {
	h := sha256.New()
	for _, p := range parts {
		h.Write(p)
		h.Write([]byte{0})
	}
	return hex.EncodeToString(h.Sum(nil))
}
