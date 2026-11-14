/-
Parallel reduction `⇒` of SPEC.md section 17 and of the paper
`notes/settled-scope.tex`, mirroring the `par` function of
`reduce/parallel_test.go`: at every node the term either stays (through
congruence, with each child independently parallel-reduced) or, when the
node is a redex, contracts after its arguments have been parallel-reduced.
Every side condition is evaluated on the term before the step.

The three `contract*` constructors are the root-contraction half of `⇒`:
they say that the node is a redex at mask `m` and give the contraction
with the arguments parallel-reduced first (at the inner permission for
`Abs` and `Sc`, as in the Go implementation). `ParList` is the
pointwise lifting of `⇒` to the argument list of a contraction spine;
it is mutual with `ParAt` because a contraction's arguments are terms.
-/

import SpherepopProof.Config

namespace Spherepop

open Term

namespace Config

variable (cfg : Config)

mutual

/-- `ParAt cfg m t u`: `t ⇒ u` at the chain whose effective permission
is `m`. -/
inductive ParAt (cfg : Config) : Perm → Term → Term → Prop where
  | atom {m : Perm} (a : String) : ParAt cfg m (.atom a) (.atom a)
  | const {m : Perm} (c : Const) : ParAt cfg m (.const c) (.const c)
  | scope {m : Perm} (l : Label) : ParAt cfg m (.scope l) (.scope l)
  | app {m : Perm} (f f' x x' : Term)
      (hf : ParAt cfg m f f') (hx : ParAt cfg m x x') :
      ParAt cfg m (.app f x) (.app f' x')
  | bracket {m : Perm} (l : Label) (b b' : Term)
      (h : ParAt cfg (inner cfg l m) b b') :
      ParAt cfg m (.bracket l b) (.bracket l b')
  /-- `Sc`: `sc_l a ⇒ <a'>_l` with `a ⇒ a'` at the inner permission and
  `a` settled at `m`. -/
  | contract_sc {m : Perm} (l : Label) (a a' : Term)
      (h : ParAt cfg (inner cfg l m) a a') (hs : Settled cfg a m) :
      ParAt cfg m (.app (.scope l) a) (.bracket l a')
  /-- `Abs`: `<b>_l v ⇒ <b' v'>_l` with `b ⇒ b'` and `v ⇒ v'` at the
  inner permission and `v` settled at `m`. -/
  | contract_abs {m : Perm} (l : Label) (b v b' v' : Term)
      (hb : ParAt cfg (inner cfg l m) b b')
      (hv : ParAt cfg (inner cfg l m) v v')
      (hs : Settled cfg v m) :
      ParAt cfg m (.app (.bracket l b) v) (.bracket l (.app b' v'))
  /-- A contraction `t ⇒ ρ(a1' ... ak')` where `t`'s spine is headed by
  `c` with arguments `args`, each `ai ⇒ ai'` at mask `m`. -/
  | contract_contr {m : Perm} (t u : Term) (c : Const) (args args' : List Term)
      (hsp : contractionHead? t = some (c, args))
      (hadm : admissible cfg c m)
      (hpar : ParList cfg m args args')
      (hu : u = contractTemplate c args') :
      ParAt cfg m t u

/-- `ParList cfg m as bs`: `as` and `bs` have the same length and each
pair of elements is related by `⇒` at mask `m`. -/
inductive ParList (cfg : Config) : Perm → List Term → List Term → Prop where
  | nil {m : Perm} : ParList cfg m [] []
  | cons {m : Perm} (a a' : Term) (as as' : List Term)
      (h : ParAt cfg m a a') (t : ParList cfg m as as') :
      ParList cfg m (a :: as) (a' :: as')

end

/-- `⇒` is reflexive: every term parallel-reduces to itself, at every
permission. The mask is quantified inside so that the induction
hypothesis is available at the inner permission of a bracket. -/
theorem ParAt.refl (t : Term) : ∀ (m : Perm), ParAt cfg m t t := by
  induction t with
  | atom a => intro m; exact .atom (m := m) a
  | const c => intro m; exact .const (m := m) c
  | scope l => intro m; exact .scope (m := m) l
  | app f x ihf ihx =>
      intro m; exact .app f f x x (ihf m) (ihx m)
  | bracket l b ih =>
      intro m; exact .bracket l b b (ih (inner cfg l m))

/-- `ParList` is reflexive on equal lists. -/
theorem ParList.refl (as : List Term) (m : Perm) : ParList cfg m as as := by
  induction as with
  | nil => exact .nil (m := m)
  | cons a as ih => exact .cons a a as as (ParAt.refl cfg a m) ih

end Config

end Spherepop
