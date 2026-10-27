# spherepop-kernel

An independently executable reduction language in Go, built to be hosted inside a game but never to depend on one. The kernel reduces terms of the circle calculus: SK-style combinators extended with brackets and a scope constructor, where the permission to contract a term depends on the chain of brackets around it. Everything runs from the command line with no engine, graphics or network.

The design rests on keeping three things apart. A term is a structural object, a reduction step is an application of an explicit rule that a checker can verify on its own, and a host such as a game entity is only one place a reduction can run. Matching final hashes proves nothing about validity, so every run can emit a trace that an independent check replays step by step against the rule table. Computation, evidence and acceptance are separate objects with separate code.

## Try it

```
go build -o spherepop ./cmd/spherepop

spherepop reduce 'S K K x'                      # x, in 2 steps
spherepop reduce 'S K K x' --out trace.json     # also write a trace document
spherepop check trace.json                      # replay it: "valid: 2 steps, final x"
spherepop compile '\x y. x'                     # K
spherepop sim --entity a='K x y' --entity b='I z' --ticks 2 --budget 5
spherepop rules                                 # the rule table
spherepop test                                  # conformance vectors

spherepop arena examples/cruise.lam --frames 40 --effects fx.jsonl --sched sched.json
spherepop checkeffects fx.jsonl --anchor HEAD   # HEAD is the "effects log head" the run printed
spherepop checklog sched.json
```

The `arena` command compiles a behavior written in lambda syntax, runs it as the program of a ship in a small built-in world for a number of frames, and writes two logs that the checkers verify independently. A log with its tail removed passes the chain check and fails against the head you held outside it, which is the reason the head is printed.

Reduction takes `--strategy lo|li|ri|ro`, a `--fuel` bound, and the permission configuration flags `--root`, `--perm LABEL=K,C`, `--absorb` and `--sc`. A run that exhausts its fuel exits with status 3 and says so; it never presents a partial term as a result. Exit statuses are 0 for success, 1 for failure, 2 for usage errors and 3 for exhausted fuel.

## What is in it

| Package | Role |
|---|---|
| `term` | Immutable, hash-consed terms, paths, the parser, cached structural flags |
| `reduce` | The rule table, permissions, redex finding, strategies, the single authority `Apply`, the permission automaton `CapGraph`, batch reduction on a worker pool |
| `trace` | Trace documents with a hash chain, and an independent checker |
| `sched` | A deterministic fuel-bounded scheduler, with suspension and a parallel tick that gives the same log, and a checker for its log |
| `effects` | The host boundary: typed requests, schema, authorization, an append-only disposition log |
| `encode` | Church-style data, canonical balanced-ternary transport encoding (SPQT), 32-byte `0x62`-gate XOR checksums, `BFP-64` bitplanes (`+AND=1`, `~NAND=-1`, `qt:55`), checked `p/q` density ratios, and 4-way unrolled `XORFold` / `Popcount` / SWAR `ByteDiff` |
| `driver` | Persistent programs: observe, evaluate, extract effects, commit, repeat |
| `lambda` | A front end that compiles `\x y. body` to combinators |
| `arena` | A small headless example world: cells, door-gated portals, ships, host-held memory |
| `internal/viz` | An integer projection of reduction steps to hue, intensity and complexity, served over `net/http` |
| `tools/verify-py`, `conformance` | An independent verifier in Python and a shared corpus of 455 cases |
| `tools/noemoji` | The check, and the cleaner, that keep emoji out of the tree |
| `cmd/spherepop` | The command line |

The packages depend downward only. `term` knows nothing about reduction, `reduce` knows nothing about hosts, and `arena` is an example host, not part of the language.

## How a game would use it

A program is a term that takes the world's observations as arguments and reduces to a normal form listing the effects it proposes, for example `effects (effect (door 1) open)`. Effects are inert data during reduction. Only after a normal form does the host read them, check each one against a schema and an authorizer, apply the ones that pass, and record a disposition for every one, including refusals. Three relations stay distinct: reduction of the term, extraction of effects from the normal form, and the host's transition on the world. The scheduler's only powers are ordering entities deterministically, giving each a fixed step budget, and continuing unfinished terms, and its log separates its own decisions from reduction steps. `SPEC.md` section 14 onward describes this in full, and `arena/arena_test.go` runs a behavior written in lambda syntax through a door to a goal cell.

## Status of the mathematics

The reducer implements the combinators with permission-gated contraction and two boundary rules, absorption (`Abs`) and scope (`Sc`). Their side conditions decide whether the system is confluent, and the repository is explicit about which claims are proved and which are not.

With `--absorb s --sc settled`, where both boundary rules fire only on arguments that contain no steps at all, confluence is proved for every permission structure, non-terminating terms included. The proof is `notes/settled-scope.tex`, and a bounded search of tens of millions of parallel-reduction pairs agrees with it. The scheduler, `sim` and `arena` use this pair by default. The `safe` scope mode is an experimental alternative and is not proved. The proof route fails at one identified pattern, `sc_x (<I>_x a)`, and local confluence of the full relation still held in every case searched, so it is unrefuted and unproven. The reducer's default `--absorb u` is likewise outside the theorem. The essay's unrestricted `Sc` is available as `--sc any` and is a research mode: it is known to be non-confluent when a label restricts the root permission.

## Cross-implementation verification

`SPEC.md` section 18 fixes every hashed byte and every verifier decision. `tools/verify-py/spherepop_verify.py` is a second verifier in Python that shares no code with the Go packages: it rebuilds term hashes, replays traces, checks scheduler and effects logs, and reads the same JSON under the same strictness rules. `conformance/` holds a corpus of about 400 valid, malformed, truncated and deliberately mutated records with the verdict and failure class each requires. `go test ./conformance` holds both verifiers to it, and `python3 conformance/crosscheck.py 500` has each implementation reduce random terms and check the other's traces.

```
python3 tools/verify-py/spherepop_verify.py trace trace.json --require-strategy
python3 tools/verify-py/spherepop_verify.py sched sched.json
spherepop arena-schema > schema.json
python3 tools/verify-py/spherepop_verify.py effects fx.jsonl --schema schema.json --anchor HEAD
go test -bench=. ./encode/...
```

Frame ABI v1 is a non-cryptographic XOR checksum. Equal-length payloads can collide, including raw bytes `00 00` and `01 01`; a passing frame check does not establish payload identity or authenticity. The ABI is retained for compatibility. `Gate0x62State` publishes an immutable fold/state pair atomically, allocating a new snapshot for each matching-fold CAS attempt; callers needing a consistent pair must call `Snapshot`, since separate `Fold` and `State` calls can span updates.

Suspension is a scheduler protocol and not a reduction rule: an entity whose term reaches the root form `yield k` is stopped there, recorded as suspended, and resumed at `k` on its next turn (`SPEC.md` section 17a). The traces keep their format, the scheduler log distinguishes suspension from fuel exhaustion and from a host re-arm, and both verifiers check it. A test shows that suspending and resuming reaches the same result as uninterrupted evaluation under every strategy and budget.

A verified effects log shows that the host recorded these dispositions in a chain, and that each request is consistent with the schema. It does not show that the authorizer decided correctly unless its policy and inputs are replayed. A verified scheduler log is only as checkable as the state and rules it records.

## Tests

`go test ./...` takes about a minute. Longer exhaustive searches, which enumerate every term up to a size bound and every permission assignment, are enabled by environment variables: `SPHEREPOP_SEARCH_LEAVES`, `SPHEREPOP_SEARCH_BRACKETS` and `SPHEREPOP_SEARCH_LABELS=2`. The largest reported runs take around twenty minutes. Each search has a positive control that must find a known failure, so a passing search cannot be an empty one.

## Not done

A proof for the `safe` and `u` modes is open, and the verifiers have not yet been reimplemented from the specification by anyone other than its author. `notes/claim-status.md` lists every claim with the evidence behind it and every open obligation.

## Specification

`SPEC.md` defines the term syntax and digests, the rules, permissions, absorption and scope modes, strategies, fuel, trace and log formats, the effects boundary and the frame loop. Where the specification and the code disagree, that is a bug in one of them.
