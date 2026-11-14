/-
Single-step reduction `→` of SPEC.md section 4, mirroring `reduce.Apply`
and the congruence closure of `reduce.find`: a step is either a root
contraction of a redex at the current mask, or a step inside a function
child, an argument child, or a bracket body (where the mask shrinks by
the bracket's label permission).
-/

import SpherepopProof.Par

namespace Spherepop

open Term

namespace Config

variable (cfg : Config)

/-- `StepAt cfg m t u`: `t → u` at the chain whose effective permission
is `m`. -/
inductive StepAt (cfg : Config) : Perm → Term → Term → Prop where
  | appL (x : Term) (h : StepAt cfg m f f') :
      StepAt cfg m (.app f x) (.app f' x)
  | appR (f : Term) (h : StepAt cfg m x x') :
      StepAt cfg m (.app f x) (.app f x')
  | bracket (l : Label) (b b' : Term)
      (h : StepAt cfg (inner cfg l m) b b') :
      StepAt cfg m (.bracket l b) (.bracket l b')
  | root (t : Term) (k : RedexKind) (hk : MatchesRedex cfg t m k) :
      StepAt cfg m t (contractResult k)

/-- `Step cfg t u`: a single reduction step at the root permission. -/
def Step (t u : Term) : Prop := StepAt cfg cfg.root t u

/-- `StepStar cfg t u`: the reflexive-transitive closure of `Step`. -/
def StepStar (t u : Term) : Prop := Relation.ReflTransGen (Step cfg) t u

/-- `ParStar cfg t u`: the reflexive-transitive closure of `⇒` at the
root permission. -/
def ParStar (t u : Term) : Prop := Relation.ReflTransGen (ParAt cfg cfg.root) t u

end Config

end Spherepop
