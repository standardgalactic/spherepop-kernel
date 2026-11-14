/-
Confluence, the payoff of the Takahashi argument in
`notes/settled-scope.tex`: the diamond property of parallel reduction
`⇒` and confluence of ordinary reduction `→`.

`ParAt.diamond`: from `t ⇒ u₁` and `t ⇒ u₂`, the Takahashi property
gives `u₁ ⇒ t°` and `u₂ ⇒ t°`, so `t°` is a common parallel reduct.

`StepAt.confluent`: a single step is a parallel step
(`StepAt.subset_par`), so two steps `t → u₁`, `t → u₂` give parallel
steps, hence `uᵢ ⇒ t°`, and `ParAt.stepStar` turns each into an
ordinary `→*` to the common reduct `t°`.
-/

import SpherepopProof.Takahashi

namespace Spherepop

open Term
open Classical

namespace Config

variable (cfg : Config)

/-- Diamond property of parallel reduction `⇒`: two parallel reducts
of `t` have the complete development `t°` as a common reduct. -/
theorem ParAt.diamond {m : Perm} {t u₁ u₂ : Term}
    (h₁ : ParAt cfg m t u₁) (h₂ : ParAt cfg m t u₂) :
    ∃ v, ParAt cfg m u₁ v ∧ ParAt cfg m u₂ v :=
  ⟨Config.dev cfg m t, ParAt.takahashi cfg h₁, ParAt.takahashi cfg h₂⟩

/-- Confluence of ordinary reduction `→`: two single steps from `t`
join at `t°` through `→*`. -/
theorem StepAt.confluent {m : Perm} {t u₁ u₂ : Term}
    (h₁ : StepAt cfg m t u₁) (h₂ : StepAt cfg m t u₂) :
    ∃ v, StepAtStar cfg m u₁ v ∧ StepAtStar cfg m u₂ v :=
  ⟨Config.dev cfg m t,
    ParAt.stepStar cfg
      (ParAt.takahashi cfg (StepAt.subset_par cfg h₁)),
    ParAt.stepStar cfg
      (ParAt.takahashi cfg (StepAt.subset_par cfg h₂))⟩

end Config

end Spherepop
