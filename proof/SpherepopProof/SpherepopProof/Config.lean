/-
The permission structure and the settled predicate of SPEC.md sections 3
and 17. A configuration fixes a gated set of constants, a root permission
and a permission for every label. The effective permission of a position
is the root permission intersected with the permission of every bracket
label on the chain from the root to that position; it is carried as the
mask parameter `m` of the predicates below.

Everything here is propositional: `SettledAt` is an inductive and
`RedexAt` a predicate on redex kinds. The parallel reduction `ParAt`,
the single-step relation `StepAt` and the development `dev` of
`Par.lean`, `Step.lean` and `Dev.lean` are the objects the paper proves
things about; no computable shadow of them is needed for the proofs.
-/

import Mathlib
import SpherepopProof.Term

namespace Spherepop

open Term

/-- A permission is a set of constants. -/
abbrev Perm := Finset Const

/-- A configuration: the gated constants, the root permission, and the
permission of every label (a total function, as in the paper). -/
structure Config where
  gated : Finset Const
  root : Perm
  perm : Label → Perm

namespace Config

variable (cfg : Config)

/-- A gated constant may contract only when it lies in the mask; an
ungated one contracts everywhere. -/
def admissible (c : Const) (m : Perm) : Prop :=
  c ∈ cfg.gated → c ∈ m

/-- The effective permission inside a bracket labelled `l`, given the
permission `m` in force outside it. -/
def inner (l : Label) (m : Perm) : Perm := m ∩ cfg.perm l

/-- The head constant and spine arguments of `t` when `t` is a contraction
redex candidate: the spine head is a constant whose arity equals the
number of arguments. -/
def contractionHead? (t : Term) : Option (Const × List Term) :=
  let (h, args) := t.spine
  match h with
  | .const c =>
      if args.length = arity c then some (c, args) else none
  | _ => none

/-- `SettledAt cfg m t`: `t` contains no step of any kind at mask `m` or
at any smaller permission. This is the side condition of `Abs_s` and
`Sc_settled`; it is an inductive so proofs can invert it. The `app`
constructor requires that the function child is neither a bracket nor a
scope constructor and that no admissible contraction is rooted at the
node. -/
inductive SettledAt (cfg : Config) : Perm → Term → Prop where
  | atom {m : Perm} (a : String) : SettledAt cfg m (.atom a)
  | const {m : Perm} (c : Const) : SettledAt cfg m (.const c)
  | scope {m : Perm} (l : Label) : SettledAt cfg m (.scope l)
  | app {m : Perm} (f x : Term)
      (hf : ∀ l b, f ≠ .bracket l b) (hs : ∀ l, f ≠ .scope l)
      (hc : ∀ c args, contractionHead? (.app f x) = some (c, args) →
        ¬ admissible cfg c m)
      (h1 : SettledAt cfg m f) (h2 : SettledAt cfg m x) :
      SettledAt cfg m (.app f x)
  | bracket {m : Perm} (l : Label) (b : Term)
      (h : SettledAt cfg (inner cfg l m) b) :
      SettledAt cfg m (.bracket l b)

/-- `Settled cfg m t`: `t` is settled at mask `m`. -/
def Settled (t : Term) (m : Perm) : Prop := SettledAt cfg m t

/-- The kind of a root redex, mirroring `Redex` of `reduce/find.go`. -/
inductive RedexKind where
  | sc (l : Label) (a : Term)
  | abs (l : Label) (b v : Term)
  | contr (c : Const) (args : List Term)

/-- `MatchesRedex cfg m t k`: the redex kind `k` is the rule that `t`
presents at its root at mask `m`, with its side condition satisfied.
This is the propositional reading of `redexAt` of `reduce/find.go` in
the settled modes. -/
def MatchesRedex (t : Term) (m : Perm) (k : RedexKind) : Prop :=
  match k with
  | .sc l a =>
      t = .app (.scope l) a ∧ Settled cfg a m
  | .abs l b v =>
      t = .app (.bracket l b) v ∧ Settled cfg v m
  | .contr c args =>
      contractionHead? t = some (c, args) ∧ admissible cfg c m

/-- `RedexAt cfg m t`: `t` has a step at its root at mask `m`. -/
def RedexAt (t : Term) (m : Perm) : Prop := ∃ k, MatchesRedex cfg t m k

/-- The result of contracting a root redex, mirroring `Apply` of
`reduce/apply.go`. -/
def contractResult : RedexKind → Term
  | .sc l a => .bracket l a
  | .abs l b v => .bracket l (.app b v)
  | .contr c args => contractTemplate c args

end Config

end Spherepop
