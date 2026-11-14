/-
The two inclusions between the relations of the paper:

* `StepAt.subset_par`: every single step `t → u` is a parallel step
  `t ⇒ u` (identity parallel reduction on untouched arguments).
* `ParAt.stepStar`: every parallel step `t ⇒ u` is a sequence of single
  steps `t →* u`. For a root contraction the boundary cases are realised
  by contracting first and developing inside the bracket afterwards,
  where the inner permission is in force; for a contraction the spine
  arguments are developed in place at the same mask and the template is
  then contracted.

Both are needed for `→* = ⇒*` and hence for confluence.
-/

import SpherepopProof.Settled
import SpherepopProof.Star

namespace Spherepop

open Term

namespace Config

variable (cfg : Config)

/-- `ParList` preserves list length. -/
theorem ParList.length_eq {m : Perm} {as bs : List Term}
    (h : ParList cfg m as bs) : as.length = bs.length := by
  induction as generalizing bs with
  | nil =>
      cases h
      rfl
  | cons a as ih =>
      cases h with
      | cons _ _ _ _ ha htl =>
          have hlen := ih htl
          simp only [List.length_cons]
          omega

/-- `→ ⊆ ⇒`: a single step is a parallel step. -/
theorem StepAt.subset_par {m : Perm} {t u : Term}
    (h : StepAt cfg m t u) : ParAt cfg m t u := by
  induction h with
  | appL x hf ih =>
      exact .app _ _ _ _ ih (ParAt.refl cfg x _)
  | appR f hf ih =>
      exact .app _ _ _ _ (ParAt.refl cfg f _) ih
  | bracket l b b' hb ih =>
      exact .bracket l b b' ih
  | root t k hk =>
      cases k with
      | sc l a =>
          obtain ⟨rfl, hs⟩ := hk
          exact .contract_sc l a a (ParAt.refl cfg a _) hs
      | abs l b v =>
          obtain ⟨rfl, hs⟩ := hk
          exact .contract_abs l b v b v
            (ParAt.refl cfg b _) (ParAt.refl cfg v _) hs
      | contr c args =>
          obtain ⟨hsp, hadm⟩ := hk
          exact .contract_contr t _ c args args hsp hadm
            (ParList.refl cfg args _) rfl

/-- `⇒ ⊆ →*`: a parallel step is a sequence of single steps. Proved by
strong induction on the size of the source term, since a contraction's
spine arguments are not immediate subterms. -/
theorem ParAt.stepStar_aux : ∀ n : Nat, ∀ t : Term, size t ≤ n →
    ∀ {m : Perm} {u : Term}, ParAt cfg m t u → StepAtStar cfg m t u := by
  intro n
  induction n with
  | zero =>
      intro t ht m u hp
      exfalso
      have hpos := size_pos t
      omega
  | succ n ih =>
      intro t ht m u hp
      cases t with
      | atom a =>
          cases hp with
          | atom a' => exact Relation.ReflTransGen.refl
          | contract_contr t' u' c' args' args'' hsp hadm hpar hu =>
              simp [contractionHead?, spine] at hsp
      | const c =>
          cases hp with
          | const c' => exact Relation.ReflTransGen.refl
          | contract_contr t' u' c' args' args'' hsp hadm hpar hu =>
              obtain ⟨hspine, hlen⟩ := contractionHead?_eq hsp
              have hsp2 : (Term.const c, []) = (Term.const c', args') := by
                rw [← spine_const]; exact hspine
              have hargs : args' = [] := (congrArg Prod.snd hsp2).symm
              rw [hargs] at hlen
              have h0 : arity c' = 0 := by simpa using hlen.symm
              exact absurd h0 (arity_ne_zero c')
      | scope l =>
          cases hp with
          | scope l' => exact Relation.ReflTransGen.refl
          | contract_contr t' u' c' args' args'' hsp hadm hpar hu =>
              simp [contractionHead?, spine] at hsp
      | bracket l b =>
          cases hp with
          | bracket _ _ b' h =>
              have hbs : size b ≤ n := by
                simp only [size] at ht; omega
              exact StepAtStar.bracket cfg (ih b hbs h)
          | contract_contr t' u' c' args' args'' hsp hadm hpar hu =>
              simp [contractionHead?, spine] at hsp
      | app f x =>
          cases hp with
          | app _ f' _ x' hf hx =>
              have hfs : size f ≤ n := by
                simp only [size] at ht; omega
              have hxs : size x ≤ n := by
                simp only [size] at ht; omega
              have h1 := ih f hfs hf
              have h2 := ih x hxs hx
              exact StepAtStar.trans cfg (StepAtStar.appL cfg x h1) (StepAtStar.appR cfg f' h2)
          | contract_sc l a a' h hs =>
              -- `a` is identified with `x` by index unification
              have hxs : size x ≤ n := by
                simp only [size] at ht; omega
              have h1 : StepAtStar cfg (inner cfg l m) x a' := ih x hxs h
              have h2 : StepAtStar cfg m (.bracket l x) (.bracket l a') :=
                StepAtStar.bracket cfg h1
              have h3 : StepAt cfg m (.app (.scope l) x) (.bracket l x) :=
                StepAt.root _ (.sc l x) ⟨rfl, hs⟩
              exact StepAtStar.trans cfg (Relation.ReflTransGen.single h3) h2
          | contract_abs l b v b' v' hb hv hs =>
              -- `v` is identified with `x` by index unification
              have hbs : size b ≤ n := by
                simp only [size] at ht; omega
              have hxs : size x ≤ n := by
                simp only [size] at ht; omega
              have hb' := ih b hbs hb
              have hv' := ih x hxs hv
              have happ : StepAtStar cfg (inner cfg l m)
                  (.app b x) (.app b' v') :=
                StepAtStar.trans cfg (StepAtStar.appL cfg x hb')
                  (StepAtStar.appR cfg b' hv')
              have hbr : StepAtStar cfg m
                  (.bracket l (.app b x)) (.bracket l (.app b' v')) :=
                StepAtStar.bracket cfg happ
              have h3 : StepAt cfg m (.app (.bracket l b) x)
                  (.bracket l (.app b x)) :=
                StepAt.root _ (.abs l b x) ⟨rfl, hs⟩
              exact StepAtStar.trans cfg (Relation.ReflTransGen.single h3) hbr
          | contract_contr t' u' c args args' hsp hadm hpar hu =>
              obtain ⟨hspine, hlen⟩ := contractionHead?_eq hsp
              have htf : .app f x = apply (.const c) args := by
                have h0 := eq_apply_spine (.app f x)
                rw [hspine] at h0
                simpa using h0
              have hstar : StepAtStar cfg m
                  (apply (.const c) args) (apply (.const c) args') := by
                suffices hgen : ∀ (g : Term) (as bs : List Term),
                    (∀ a ∈ as, size a ≤ n) →
                    ParList cfg m as bs →
                    StepAtStar cfg m (apply g as) (apply g bs) by
                  apply hgen
                  · intro a ha
                    have ha_mem : a ∈ (f.app x).spine.2 := by
                      rw [hspine]; exact ha
                    have hlt := size_spine_arg_lt ha_mem
                    omega
                  · exact hpar
                intro g as bs hbound hpl
                induction as generalizing g bs with
                | nil =>
                    cases hpl with
                    | nil => exact Relation.ReflTransGen.refl
                | cons a as ihl =>
                    cases hpl with
                    | cons _ a2 _ as2 ha htl =>
                        have hae : size a ≤ n := hbound a (List.mem_cons_self)
                        have hsa : StepAtStar cfg m a a2 := ih a hae ha
                        have htailbound : ∀ b ∈ as, size b ≤ n :=
                          fun b hb => hbound b (List.mem_cons_of_mem a hb)
                        have htail := ihl (g.app a) as2 htailbound htl
                        have hhead := StepAtStar.apply_head cfg as2
                          (StepAtStar.appR cfg g hsa)
                        exact StepAtStar.trans cfg htail hhead
              have hlen' : args'.length = arity c := by
                have hll := ParList.length_eq cfg hpar
                omega
              have hhead : contractionHead? (apply (.const c) args') =
                  some (c, args') :=
                contractionHead?_apply_const c args' hlen'
              have hstep : StepAt cfg m (apply (.const c) args')
                  (contractTemplate c args') :=
                StepAt.root _ (.contr c args') ⟨hhead, hadm⟩
              have hstar' : StepAtStar cfg m (.app f x)
                  (contractTemplate c args') := by
                rw [htf]
                exact StepAtStar.trans cfg hstar
                  (Relation.ReflTransGen.single hstep)
              rw [hu]
              exact hstar'

/-- `ParAt.stepStar`: every parallel step is a sequence of single
steps. -/
theorem ParAt.stepStar {m : Perm} {t u : Term}
    (hp : ParAt cfg m t u) : StepAtStar cfg m t u := by
  have ht := ParAt.stepStar_aux cfg (size t) t (Nat.le_refl _) hp
  exact ht

end Config

end Spherepop
