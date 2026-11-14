# SpherepopProof

A machine-checked formalization, in Lean 4 + mathlib, of the
settled-scope confluence theorem proved on paper in
`notes/settled-scope.tex`.

The theorem: for every permission structure and every gated set, the
system consisting of the combinator contractions, absorption
restricted to settled arguments (mode `s`), and the scope constructor
restricted to settled arguments (mode `settled`) has the diamond
property for parallel reduction `⇒`, and its ordinary reduction
relation `→` is therefore confluent, including non-terminating terms.

## Building

Requires [elan](https://github.com/leanprover/elan) with the toolchain
pinned in `lean-toolchain` (Lean 4 v4.27.0, mathlib v4.27.0).

```sh
cd proof/SpherepopProof
lake build
```

The umbrella module is `SpherepopProof.lean`; it imports every file.

## Structure

| File | Contents |
|---|---|
| `Term.lean` | Terms (`atom`, `const`, `scope`, `app`, `bracket`), constants, permissions, spine/apply helpers. |
| `Config.lean` | Reduction configuration, admissibility, `inner` permission masks, `Settled`/`SettledAt`, `RedexAt`. |
| `Par.lean` | Parallel reduction `ParAt` (`⇒`) and `ParList`, mirroring the `par` relation of the Go implementation. |
| `Step.lean` | Ordinary one-step reduction `StepAt` (`→`), mirroring `reduce.Apply`. |
| `Spine.lean` | Spine decomposition, `contractionHead?`, structural `size` and its lemmas. |
| `Settled.lean` | `settledB ↔ SettledAt`, settledness monotonicity, the frozen lemma. |
| `Star.lean` | `StepAtStar` (`→*`) and closure of contexts. |
| `ParStep.lean` | `ParList.length_eq`, `ParAt.stepStar` (`⇒ ⊆ →*`), `StepAt.subset_par` (`→ ⊆ ⇒`). |
| `Dev.lean` | Complete development `dev` (`t°`), fuel-based `devB`, and `ParAt.dev` (`t ⇒ t°`). |
| `Takahashi.lean` | The Takahashi property `ParAt.takahashi`: `t ⇒ u` implies `u ⇒ t°`. |
| `Confluence.lean` | `ParAt.diamond` (diamond for `⇒`) and `StepAt.confluent` (confluence of `→`). |

## What is and is not established

The Lean development proves confluence for the formalized model. The
model was written to match `reduce.Apply` (ordinary steps) and the
`par` relation of `reduce/parallel_test.go` (parallel steps), but the
correspondence between the Lean definitions and the Go code is by
construction and review, not machine-checked. No `sorry` or
`admit` remains in the proof files.
