/-
Lemmas about the settled predicate: monotonicity in the permission mask
(the "monotonicity" lemma of the paper), admissibility monotonicity, and
the frozen property: a settled term has no parallel reduct other than
itself (the "frozen" lemma). These are the stability properties on which
the whole Takahashi argument rests.
-/

import SpherepopProof.Spine
import SpherepopProof.Step

namespace Spherepop

open Term

namespace Config

variable (cfg : Config)

/-- `inner` is monotone in the outer mask: shrinking the mask shrinks the
permission inside every bracket. -/
theorem inner_subset_inner {l : Label} {m₁ m₂ : Perm} (h : m₁ ⊆ m₂) :
    inner cfg l m₁ ⊆ inner cfg l m₂ := by
  intro x hx
  simp only [inner, Finset.mem_inter] at hx ⊢
  exact ⟨h hx.1, hx.2⟩

/-- Admissibility is monotone in the mask: a contraction permitted at a
smaller mask is permitted at any larger one. -/
theorem admissible_mono {c : Const} {m₁ m₂ : Perm} (h : m₁ ⊆ m₂)
    (ha : admissible cfg c m₁) : admissible cfg c m₂ := by
  intro hg
  exact h (ha hg)

/-- Monotonicity (Lemma "monotonicity" of the paper): a term settled at
`m` is settled at every smaller mask `m' ⊆ m`. The target mask is
quantified inside so that the induction hypothesis applies inside
brackets, where the mask becomes `inner l m`. -/
theorem SettledAt.mono {t : Term} {m : Perm} (hs : SettledAt cfg m t) :
    ∀ {m' : Perm}, m' ⊆ m → SettledAt cfg m' t := by
  induction hs with
  | atom a => intro m' h; exact .atom a
  | const c => intro m' h; exact .const c
  | scope l => intro m' h; exact .scope l
  | app f x hf hs' hc h1 h2 ihf ihx =>
      intro m' h
      exact .app f x hf hs'
        (fun c args hch ha => hc c args hch (admissible_mono cfg h ha))
        (ihf h) (ihx h)
  | bracket l b hb ih =>
      intro m' h
      exact .bracket l b (ih (inner_subset_inner cfg h))

/-- Frozen (Lemma "frozen" of the paper): if `t` is settled at `m` and
`m' ⊆ m`, then `t ⇒ u` at `m'` forces `u = t`. The proof is by induction
on `t`; in each case the parallel derivation is decomposed with `cases`,
which needs no induction hypotheses of its own: every recursive need is
served by the induction hypothesis on the subterm. -/
theorem ParAt.eq_of_settled (t : Term) :
    ∀ {m m' : Perm} {u : Term}, m' ⊆ m →
      SettledAt cfg m t → ParAt cfg m' t u → u = t := by
  induction t with
  | atom a =>
      intro m m' u hsub hs hp
      cases hp with
      | atom a' => rfl
      | contract_contr t' u' c args args' hsp hadm hpar hu =>
          simp [contractionHead?, spine] at hsp
  | const c =>
      intro m m' u hsub hs hp
      cases hp with
      | const c' => rfl
      | contract_contr t' u' c' args' args'' hsp hadm hpar hu =>
          -- a bare constant has an empty spine: never a contraction
          obtain ⟨hspine, hlen⟩ := contractionHead?_eq hsp
          have hsp2 : (Term.const c, []) = (Term.const c', args') := by
            rw [← spine_const]; exact hspine
          have hargs : args' = [] := (congrArg Prod.snd hsp2).symm
          rw [hargs] at hlen
          have h0 : arity c' = 0 := by simpa using hlen.symm
          exact absurd h0 (arity_ne_zero c')
  | scope l =>
      intro m m' u hsub hs hp
      cases hp with
      | scope l' => rfl
      | contract_contr t' u' c args args' hsp hadm hpar hu =>
          simp [contractionHead?, spine] at hsp
  | bracket l b ihb =>
      intro m m' u hsub hs hp
      cases hs with
      | bracket l' b' hb' =>
          cases hp with
          | bracket l'' b'' b''' h =>
              -- l'' = l and b'' = b by index unification
              have hb'' : b''' = b := ihb
                (inner_subset_inner cfg hsub) hb' h
              rw [hb'']
          | contract_contr t' u' c args args' hsp hadm hpar hu =>
              -- a bracket's spine head is itself, never a constant
              simp [contractionHead?, spine] at hsp
  | app f x ihf ihx =>
      intro m m' u hsub hs hp
      cases hs with
      | app f' x' hfB hsB hcB h1 h2 =>
          -- index unification forces f' = f, x' = x in hs; h1 h2 are
          -- the settledness of the children at mask m
          cases hp with
          | app g g' y y' hg hy =>
              -- g = f, y = x by unification; need g' = f, y' = x
              have hg' : g' = f := ihf hsub h1 hg
              have hy' : y' = x := ihx hsub h2 hy
              rw [hg', hy']
          | contract_sc l a a' h hs' =>
              -- f = scope l, x = a: the settled app has scope head,
              -- contradicting hsB
              exact absurd rfl (hsB l)
          | contract_abs l b v b' v' hb hv hs' =>
              -- f = bracket l b: contradicts hfB
              exact absurd rfl (hfB l b)
          | contract_contr t' u' c args args' hsp hadm hpar hu =>
              -- admissible at m' and m' ⊆ m gives admissible at m,
              -- contradicting hcB
              exact absurd (admissible_mono cfg hsub hadm)
                (hcB c args hsp)

end Config

end Spherepop
