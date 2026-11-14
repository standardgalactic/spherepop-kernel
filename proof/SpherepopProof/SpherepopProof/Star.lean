/-
The reflexive-transitive closure of the single-step relation at an
arbitrary mask, with closure under term contexts. These are the
bookkeeping lemmas that let a parallel round be replayed as a sequence of
single steps (`ParAt.stepStar`) and that let single steps be lifted into
application spines.
-/

import SpherepopProof.Spine
import SpherepopProof.Step

namespace Spherepop

open Term

namespace Config

variable (cfg : Config)

/-- `StepAtStar cfg m t u`: `t →* u` at mask `m`. -/
abbrev StepAtStar (m : Perm) (t u : Term) : Prop :=
  Relation.ReflTransGen (StepAt cfg m) t u

/-- Transitivity of `→*`. -/
theorem StepAtStar.trans {m : Perm} {t u v : Term}
    (h1 : StepAtStar cfg m t u) (h2 : StepAtStar cfg m u v) : StepAtStar cfg m t v :=
  Relation.ReflTransGen.trans h1 h2

/-- `→*` is closed under the function-child context of an application. -/
theorem StepAtStar.appL {m : Perm} {f f' : Term} (x : Term)
    (h : StepAtStar cfg m f f') : StepAtStar cfg m (.app f x) (.app f' x) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hstar hstep ih =>
      exact StepAtStar.trans cfg ih
        (Relation.ReflTransGen.single (StepAt.appL x hstep))

/-- `→*` is closed under the argument-child context of an application. -/
theorem StepAtStar.appR {m : Perm} {x x' : Term} (f : Term)
    (h : StepAtStar cfg m x x') : StepAtStar cfg m (.app f x) (.app f x') := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hstar hstep ih =>
      exact StepAtStar.trans cfg ih
        (Relation.ReflTransGen.single (StepAt.appR f hstep))

/-- `→*` is closed under the bracket context. -/
theorem StepAtStar.bracket {m : Perm} {l : Label} {b b' : Term}
    (h : StepAtStar cfg (inner cfg l m) b b') :
    StepAtStar cfg m (.bracket l b) (.bracket l b') := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hstar hstep ih =>
      exact StepAtStar.trans cfg ih
        (Relation.ReflTransGen.single (StepAt.bracket _ _ _ hstep))

/-- `→*` in the head of an application spine lifts through `apply`. -/
theorem StepAtStar.apply_head {m : Perm} {g g' : Term} (as : List Term)
    (h : StepAtStar cfg m g g') : StepAtStar cfg m (apply g as) (apply g' as) := by
  induction as generalizing g g' with
  | nil => exact h
  | cons a as ih =>
      have h1 : StepAtStar cfg m (.app g a) (.app g' a) :=
        StepAtStar.appL cfg a h
      exact ih h1

end Config

end Spherepop
