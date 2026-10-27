// Command spherepop reduces SpherePOP terms, records and checks traces, and
// runs the conformance vectors. It depends only on the term, reduce and trace
// packages: no engine, renderer or network is involved.
package main

import (
	"flag"
	"fmt"
	"io"
	"os"
	"strings"

	"github.com/standardgalactic/spherepop-kernel/internal/vectors"
	"github.com/standardgalactic/spherepop-kernel/lambda"
	"github.com/standardgalactic/spherepop-kernel/reduce"
	"github.com/standardgalactic/spherepop-kernel/sched"
	"github.com/standardgalactic/spherepop-kernel/term"
	"github.com/standardgalactic/spherepop-kernel/trace"
)

// Exit codes. They are part of the command's interface.
const (
	exitOK        = 0 // success; for reduce, a normal form was reached
	exitFailure   = 1 // invalid trace, failed vector, or other error
	exitUsage     = 2 // bad command line
	exitExhausted = 3 // reduce stopped because fuel ran out
)

func main() { os.Exit(run(os.Args[1:], os.Stdin, os.Stdout, os.Stderr)) }

const usage = `usage: spherepop <command> [arguments]

commands:
  reduce TERM   reduce a term     (--fuel N --strategy lo|li|ri|ro --trace --out FILE
                                   --perm LABEL=K,C --root W,K,C,S --absorb off|any|nf|s|u --sc any|safe|settled --def NAME=TERM)
  check FILE    verify a trace    (--strategy to also require the claimed strategy, --max-steps N)
  compile       turn a lambda expression into a combinator term (--def NAME=TERM)
  sim           run several terms on a fixed per-tick budget
                (--entity ID=TERM... --budget N --ticks T --strategy lo|li|ri|ro --out FILE,
                 plus the reduce configuration flags; the defaults here are the host's, --absorb s --sc settled)
  arena FILE    run a lambda-syntax behavior in the built-in arena
                (--frames N --budget N --registers --effects FILE --sched FILE -v
                 plus --strategy, --absorb, --sc, --def)
  arena-schema      print the arena effect schema as JSON
  checkeffects FILE verify an effects log (--anchor HEAD, --schema FILE)
  checklog FILE verify a scheduler log
  test          run the conformance vectors
  rules         print the rule table

exit status: 0 success, 1 failure, 2 usage, 3 reduce ran out of fuel
`

func run(args []string, stdin io.Reader, stdout, stderr io.Writer) int {
	if len(args) == 0 {
		fmt.Fprint(stderr, usage)
		return exitUsage
	}
	switch args[0] {
	case "reduce":
		return cmdReduce(args[1:], stdout, stderr)
	case "check":
		return cmdCheck(args[1:], stdin, stdout, stderr)
	case "compile":
		return cmdCompile(args[1:], stdout, stderr)
	case "sim":
		return cmdSim(args[1:], stdout, stderr)
	case "arena":
		return cmdArena(args[1:], stdin, stdout, stderr)
	case "arena-schema":
		return cmdArenaSchema(stdout, stderr)
	case "checkeffects":
		return cmdCheckEffects(args[1:], stdin, stdout, stderr)
	case "checklog":
		return cmdCheckLog(args[1:], stdin, stdout, stderr)
	case "test":
		return cmdTest(args[1:], stdout, stderr)
	case "rules":
		return cmdRules(stdout)
	case "help", "-h", "--help":
		fmt.Fprint(stdout, usage)
		return exitOK
	}
	fmt.Fprintf(stderr, "spherepop: unknown command %q\n\n%s", args[0], usage)
	return exitUsage
}

// parseInterspersed lets flags follow positional arguments, so
// `reduce 'S K K x' --fuel 100` works as well as `reduce --fuel 100 'S K K x'`.
func parseInterspersed(fs *flag.FlagSet, args []string) ([]string, error) {
	var pos []string
	for {
		if err := fs.Parse(args); err != nil {
			return nil, err
		}
		args = fs.Args()
		if len(args) == 0 {
			return pos, nil
		}
		pos = append(pos, args[0])
		args = args[1:]
	}
}

type listFlag []string

func (l *listFlag) String() string     { return strings.Join(*l, " ") }
func (l *listFlag) Set(v string) error { *l = append(*l, v); return nil }

func cmdReduce(args []string, stdout, stderr io.Writer) int {
	fs := flag.NewFlagSet("reduce", flag.ContinueOnError)
	fs.SetOutput(stderr)
	fuel := fs.Uint64("fuel", 1000, "maximum number of steps")
	strat := fs.String("strategy", "lo", "lo, li, ri or ro")
	showTrace := fs.Bool("trace", false, "print every step")
	out := fs.String("out", "", "write the trace document to this file")
	root := fs.String("root", "W,K,C,S", "permissions at the root chain")
	absorb := fs.String("absorb", "u", "absorption mode: off, any, nf, s or u")
	sc := fs.String("sc", "any", "scope-constructor mode: any (essay), safe (experimental) or settled (proved confluent with --absorb s)")
	var perms, defs listFlag
	fs.Var(&perms, "perm", "LABEL=K,C permissions of a label (repeatable)")
	fs.Var(&defs, "def", "NAME=TERM abbreviation (repeatable)")
	pos, err := parseInterspersed(fs, args)
	if err != nil {
		return exitUsage
	}
	if len(pos) != 1 {
		fmt.Fprintln(stderr, "spherepop reduce: expected exactly one TERM argument")
		return exitUsage
	}
	s, ok := reduce.ParseStrategy(*strat)
	if !ok {
		fmt.Fprintf(stderr, "spherepop reduce: unknown strategy %q (want lo, li, ri or ro)\n", *strat)
		return exitUsage
	}
	cfg, err := buildConfig(*root, *absorb, perms)
	if err == nil {
		cfg.Sc, err = reduce.ParseScopeMode(*sc)
	}
	if err != nil {
		fmt.Fprintf(stderr, "spherepop reduce: %v\n", err)
		return exitUsage
	}
	dm := term.Defs{}
	for _, d := range defs {
		name, src, ok := strings.Cut(d, "=")
		if !ok || name == "" {
			fmt.Fprintf(stderr, "spherepop reduce: --def wants NAME=TERM, got %q\n", d)
			return exitUsage
		}
		if dm[name], err = term.ParseWith(src, dm); err != nil {
			fmt.Fprintf(stderr, "spherepop reduce: --def %s: %v\n", name, err)
			return exitUsage
		}
	}
	start, err := term.ParseWith(pos[0], dm)
	if err != nil {
		fmt.Fprintf(stderr, "spherepop reduce: %v\n", err)
		return exitUsage
	}

	res, doc, err := trace.Record(cfg, start, s, *fuel)
	if err != nil {
		fmt.Fprintf(stderr, "spherepop reduce: %v\n", err)
		return exitFailure
	}
	if *showTrace {
		printSteps(stdout, cfg, start, res)
	}
	if *out != "" {
		b, err := trace.Marshal(doc)
		if err == nil {
			err = os.WriteFile(*out, b, 0o644)
		}
		if err != nil {
			fmt.Fprintf(stderr, "spherepop reduce: %v\n", err)
			return exitFailure
		}
	}
	if res.Exhausted {
		fmt.Fprintf(stdout, "fuel exhausted after %d steps: %s\n", res.Steps, res.Term)
		return exitExhausted
	}
	fmt.Fprintf(stdout, "%s\n", res.Term)
	fmt.Fprintf(stdout, "normal form in %d steps (%s)\n", res.Steps, s)
	return exitOK
}

func buildConfig(root, absorb string, perms []string) (reduce.Config, error) {
	cfg := reduce.DefaultConfig()
	var err error
	if cfg.Root, err = reduce.ParsePermSet(splitList(root)); err != nil {
		return cfg, err
	}
	if cfg.Absorb, err = reduce.ParseAbsorption(absorb); err != nil {
		return cfg, err
	}
	for _, p := range perms {
		label, list, ok := strings.Cut(p, "=")
		if !ok || label == "" {
			return cfg, fmt.Errorf("--perm wants LABEL=K,C, got %q", p)
		}
		set, err := reduce.ParsePermSet(splitList(list))
		if err != nil {
			return cfg, err
		}
		if cfg.Perm == nil {
			cfg.Perm = map[string]reduce.PermSet{}
		}
		cfg.Perm[label] = set
	}
	return cfg, nil
}

func splitList(s string) []string {
	var out []string
	for _, f := range strings.Split(s, ",") {
		if f = strings.TrimSpace(f); f != "" {
			out = append(out, f)
		}
	}
	return out
}

func printSteps(w io.Writer, cfg reduce.Config, start *term.Term, res reduce.Result) {
	fmt.Fprintf(w, "   0  %-4s %-6s %s\n", "", "", start)
	cur := start
	for i, st := range res.Trace {
		next, err := cfg.Apply(cur, st.Path, st.Rule)
		if err != nil { // cannot happen for a trace the reducer just produced
			fmt.Fprintf(w, "internal error replaying step %d: %v\n", i+1, err)
			return
		}
		p := string(st.Path)
		if p == "" {
			p = "root"
		}
		fmt.Fprintf(w, "%4d  %-4s %-6s %s\n", i+1, st.Rule, p, next)
		cur = next
	}
}

func cmdCheck(args []string, stdin io.Reader, stdout, stderr io.Writer) int {
	fs := flag.NewFlagSet("check", flag.ContinueOnError)
	fs.SetOutput(stderr)
	strict := fs.Bool("strategy", false, "also require every step to follow the claimed strategy")
	fuel := fs.Uint64("fuel", 0, "require the trace to state exactly this fuel budget (0 means accept the stated one)")
	maxSteps := fs.Int("max-steps", 0, "reject traces with more steps than this (0 means no limit)")
	pos, err := parseInterspersed(fs, args)
	if err != nil {
		return exitUsage
	}
	if len(pos) != 1 {
		fmt.Fprintln(stderr, "spherepop check: expected exactly one FILE argument (or - for standard input)")
		return exitUsage
	}
	var b []byte
	if pos[0] == "-" {
		b, err = io.ReadAll(stdin)
	} else {
		b, err = os.ReadFile(pos[0])
	}
	if err != nil {
		fmt.Fprintf(stderr, "spherepop check: %v\n", err)
		return exitFailure
	}
	doc, err := trace.Unmarshal(b)
	if err == nil {
		var rep trace.Report
		if rep, err = trace.Check(doc, trace.Options{RequireStrategy: *strict, MaxSteps: *maxSteps, Fuel: *fuel}); err == nil {
			status := "not a normal form"
			if rep.Normal {
				status = "normal form"
			}
			fmt.Fprintf(stdout, "valid: %d steps, final %s (%s)\n", rep.Steps, rep.Final, status)
			return exitOK
		}
	}
	fmt.Fprintf(stdout, "invalid: %v\n", err)
	return exitFailure
}

func cmdTest(args []string, stdout, stderr io.Writer) int {
	if len(args) != 0 {
		fmt.Fprintln(stderr, "spherepop test: takes no arguments")
		return exitUsage
	}
	passed, failed := vectors.Run(stdout)
	fmt.Fprintf(stdout, "\n%d passed, %d failed\n", passed, failed)
	if failed > 0 {
		return exitFailure
	}
	return exitOK
}

func cmdCompile(args []string, stdout, stderr io.Writer) int {
	fs := flag.NewFlagSet("compile", flag.ContinueOnError)
	fs.SetOutput(stderr)
	var defs listFlag
	fs.Var(&defs, "def", "NAME=TERM abbreviation (repeatable)")
	pos, err := parseInterspersed(fs, args)
	if err != nil {
		return exitUsage
	}
	if len(pos) != 1 {
		fmt.Fprintln(stderr, "spherepop compile: expected exactly one EXPRESSION argument")
		return exitUsage
	}
	dm := term.Defs{}
	for _, d := range defs {
		name, src, ok := strings.Cut(d, "=")
		if !ok || name == "" {
			fmt.Fprintf(stderr, "spherepop compile: --def wants NAME=TERM, got %q\n", d)
			return exitUsage
		}
		t, err := term.ParseWith(src, dm)
		if err != nil {
			fmt.Fprintf(stderr, "spherepop compile: --def %s: %v\n", name, err)
			return exitUsage
		}
		dm[name] = t
	}
	t, err := lambda.Compile(pos[0], dm)
	if err != nil {
		fmt.Fprintf(stderr, "spherepop compile: %v\n", err)
		return exitFailure
	}
	fmt.Fprintln(stdout, t)
	return exitOK
}

func cmdRules(stdout io.Writer) int {
	for _, r := range reduce.Rules() {
		kind := "contraction"
		if r.Kind == reduce.Boundary {
			kind = "boundary"
		}
		fmt.Fprintf(stdout, "%-4s %-11s %s\n", r.ID, kind, r.Doc)
	}
	return exitOK
}

func cmdSim(args []string, stdout, stderr io.Writer) int {
	fs := flag.NewFlagSet("sim", flag.ContinueOnError)
	fs.SetOutput(stderr)
	budget := fs.Uint64("budget", 10, "reduction steps granted to each unfinished entity per tick")
	ticks := fs.Int("ticks", 10, "number of ticks")
	strat := fs.String("strategy", "lo", "lo, li, ri or ro")
	out := fs.String("out", "", "write the scheduler log to this file")
	workers := fs.Int("workers", 1, "reduce entities on this many workers each tick; the log is identical for any value (0 means one per processor)")
	root := fs.String("root", "W,K,C,S", "permissions at the root chain")
	absorb := fs.String("absorb", "s", "absorption mode: off, any, nf, s (game-host default) or u")
	sc := fs.String("sc", "settled", "scope-constructor mode: settled (game-host default), safe or any (research modes)")
	var ents, perms listFlag
	fs.Var(&ents, "entity", "ID=TERM entity (repeatable)")
	fs.Var(&perms, "perm", "LABEL=K,C permissions of a label (repeatable)")
	pos, err := parseInterspersed(fs, args)
	if err != nil {
		return exitUsage
	}
	if len(pos) != 0 || len(ents) == 0 || *ticks < 0 {
		fmt.Fprintln(stderr, "spherepop sim: want at least one --entity ID=TERM and no other arguments")
		return exitUsage
	}
	s, ok := reduce.ParseStrategy(*strat)
	if !ok {
		fmt.Fprintf(stderr, "spherepop sim: unknown strategy %q\n", *strat)
		return exitUsage
	}
	cfg, err := buildConfig(*root, *absorb, perms)
	if err == nil {
		cfg.Sc, err = reduce.ParseScopeMode(*sc)
	}
	if err != nil {
		fmt.Fprintf(stderr, "spherepop sim: %v\n", err)
		return exitUsage
	}
	var inits []sched.Init
	for _, e := range ents {
		id, src, ok := strings.Cut(e, "=")
		if !ok || id == "" {
			fmt.Fprintf(stderr, "spherepop sim: --entity wants ID=TERM, got %q\n", e)
			return exitUsage
		}
		t, err := term.Parse(src)
		if err != nil {
			fmt.Fprintf(stderr, "spherepop sim: entity %s: %v\n", id, err)
			return exitUsage
		}
		inits = append(inits, sched.Init{ID: id, Term: t})
	}
	w, err := sched.New(cfg, sched.Policy{Strategy: s, Budget: *budget}, inits)
	if err != nil {
		fmt.Fprintf(stderr, "spherepop sim: %v\n", err)
		return exitUsage
	}
	for i := 0; i < *ticks; i++ {
		before := len(w.Log().Events)
		var err error
		if *workers == 1 {
			err = w.Tick()
		} else {
			err = w.TickParallel(*workers)
		}
		if err != nil {
			fmt.Fprintf(stderr, "spherepop sim: %v\n", err)
			return exitFailure
		}
		for _, ev := range w.Log().Events[before:] {
			if ev.Decision == sched.Skip {
				fmt.Fprintf(stdout, "tick %-3d %-12s skip\n", ev.Tick, ev.Entity)
				continue
			}
			fmt.Fprintf(stdout, "tick %-3d %-12s run  steps=%d\n", ev.Tick, ev.Entity, len(ev.Slice.Steps))
		}
	}
	fmt.Fprintln(stdout)
	for _, st := range w.States() {
		status := "continues"
		if st.Normal {
			status = "normal"
		}
		fmt.Fprintf(stdout, "%-12s %-9s %s\n", st.ID, status, st.Term)
	}
	if *out != "" {
		b, err := sched.Marshal(w.Log())
		if err == nil {
			err = os.WriteFile(*out, b, 0o644)
		}
		if err != nil {
			fmt.Fprintf(stderr, "spherepop sim: %v\n", err)
			return exitFailure
		}
	}
	return exitOK
}

func cmdCheckLog(args []string, stdin io.Reader, stdout, stderr io.Writer) int {
	fs := flag.NewFlagSet("checklog", flag.ContinueOnError)
	fs.SetOutput(stderr)
	pos, err := parseInterspersed(fs, args)
	if err != nil {
		return exitUsage
	}
	if len(pos) != 1 {
		fmt.Fprintln(stderr, "spherepop checklog: expected exactly one FILE argument (or - for standard input)")
		return exitUsage
	}
	var b []byte
	if pos[0] == "-" {
		b, err = io.ReadAll(stdin)
	} else {
		b, err = os.ReadFile(pos[0])
	}
	if err != nil {
		fmt.Fprintf(stderr, "spherepop checklog: %v\n", err)
		return exitFailure
	}
	l, err := sched.Unmarshal(b)
	if err == nil {
		err = sched.CheckLog(l)
	}
	if err != nil {
		fmt.Fprintf(stdout, "invalid: %v\n", err)
		return exitFailure
	}
	fmt.Fprintf(stdout, "valid: %d scheduler events over %d entities\n", len(l.Events), len(l.Initial))
	return exitOK
}
