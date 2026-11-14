/-
The complete development `t°` of the paper `notes/settled-scope.tex`:
contract every redex of `t`, working from the arguments outwards. If the
root is a redex it is contracted after its arguments (at the inner
permission for `Abs` and `Sc`, at the same mask for a contraction) have
been developed; otherwise the development is the congruence of the
developed children.

The development is defined through `devB`, a fuel-bounded structural
recursion: `dev cfg m t` is `devB` run with `size t` units of fuel, which
is enough because every recursive call lands on a strict subterm
(`size_spine_arg_lt` covers spine arguments). `devB_eq_dev` shows that
any fuel above `size t` computes the same term, which is what lets the
proofs ignore the exact fuel passed down.

`ParAt.dev` is the first half of the Takahashi argument: `t ⇒ t°`.
-/

import SpherepopProof.ParStep

namespace Spherepop

open Term
open Classical

namespace Config

variable (cfg : Config)

/-- `devB cfg m n t`: one step of development of `t` at mask `m`, with
`n` units of fuel. Fuel `0` returns `t` untouched; otherwise the root
redex (if any) is contracted after developing the arguments, and
otherwise the children are developed. The recursion is on `n`, so it is
structural. -/
noncomputable def devB (cfg : Config) (m : Perm) : Nat → Term → Term
  | 0, t => t
  | n+1, t =>
      match t with
      | .app f x =>
          match f with
          | .scope l =>
              if RedexAt cfg (.app (.scope l) x) m then
                .bracket l (devB cfg (inner cfg l m) n x)
              else .app (.scope l) (devB cfg m n x)
          | .bracket l b =>
              if RedexAt cfg (.app (.bracket l b) x) m then
                .bracket l (.app (devB cfg (inner cfg l m) n b)
                  (devB cfg (inner cfg l m) n x))
              else .app (.bracket l (devB cfg (inner cfg l m) n b))
                (devB cfg m n x)
          | .atom a => .app (.atom a) (devB cfg m n x)
          | .const c =>
              match contractionHead? (.app (.const c) x) with
              | some (c', args) =>
                  if admissible cfg c' m then
                    contractTemplate c' (args.map (devB cfg m n))
                  else .app (.const c) (devB cfg m n x)
              | none => .app (.const c) (devB cfg m n x)
          | .app g y =>
              match contractionHead? (.app (.app g y) x) with
              | some (c', args) =>
                  if admissible cfg c' m then
                    contractTemplate c' (args.map (devB cfg m n))
                  else .app (devB cfg m n (.app g y)) (devB cfg m n x)
              | none => .app (devB cfg m n (.app g y)) (devB cfg m n x)
      | .bracket l b => .bracket l (devB cfg (inner cfg l m) n b)
      | _ => t

/-- Congruence of `ite` for two pairs of equal branches. -/
theorem ite_eq {c : Prop} [Decidable c] {α : Sort _} {a₁ a₂ b₁ b₂ : α}
    (ha : a₁ = a₂) (hb : b₁ = b₂) :
    (if c then a₁ else b₁) = (if c then a₂ else b₂) := by
  by_cases h : c
  · rw [if_pos h, if_pos h, ha]
  · rw [if_neg h, if_neg h, hb]

/-- Any fuel at least `size t` computes the canonical development
`devB cfg m (size t) t`. Proved by strong induction on `size t`; the
spine-argument case uses `size_spine_arg_lt` through the membership of
each argument in the spine. -/
theorem devB_eq_dev (cfg : Config) : ∀ N : Nat, ∀ m : Perm,
    ∀ fuel : Nat, ∀ t : Term, size t ≤ N → size t ≤ fuel →
    devB cfg m fuel t = devB cfg m (size t) t := by
  intro N
  induction N with
  | zero =>
      intro m fuel t hN hf
      have h := size_pos t
      omega
  | succ N ih =>
      intro m fuel t hN hf
      obtain ⟨k, hk⟩ : ∃ k, size t = k.succ :=
        ⟨size t - 1, by have h := size_pos t; omega⟩
      cases fuel with
      | zero => simp at hf; have h := size_pos t; omega
      | succ j =>
          rw [hk]
          cases t with
          | atom a => simp [devB]
          | const c => simp [devB]
          | scope l => simp [devB]
          | bracket l b =>
              simp only [size] at hk hN hf
              rw [devB.eq_7, devB.eq_7]
              rw [ih (inner cfg l m) j b (by omega) (by omega),
                  ih (inner cfg l m) k b (by omega) (by omega)]
          | app f x =>
              cases f with
              | scope l =>
                  simp only [size] at hk hN hf
                  have hxN : size x ≤ N := by omega
                  have hxj : size x ≤ j := by omega
                  have hxk : size x ≤ k := by omega
                  rw [devB.eq_2, devB.eq_2]
                  apply ite_eq
                  · rw [ih (inner cfg l m) j x hxN hxj,
                        ih (inner cfg l m) k x hxN hxk]
                  · rw [ih m j x hxN hxj, ih m k x hxN hxk]
              | bracket l b =>
                  simp only [size] at hk hN hf
                  have hbN : size b ≤ N := by omega
                  have hbj : size b ≤ j := by omega
                  have hbk : size b ≤ k := by omega
                  have hxN : size x ≤ N := by omega
                  have hxj : size x ≤ j := by omega
                  have hxk : size x ≤ k := by omega
                  rw [devB.eq_3, devB.eq_3]
                  apply ite_eq
                  · rw [ih (inner cfg l m) j b hbN hbj,
                        ih (inner cfg l m) k b hbN hbk,
                        ih (inner cfg l m) j x hxN hxj,
                        ih (inner cfg l m) k x hxN hxk]
                  · rw [ih (inner cfg l m) j b hbN hbj,
                        ih (inner cfg l m) k b hbN hbk,
                        ih m j x hxN hxj, ih m k x hxN hxk]
              | atom a =>
                  simp only [size] at hk hN hf
                  have hxN : size x ≤ N := by omega
                  have hxj : size x ≤ j := by omega
                  have hxk : size x ≤ k := by omega
                  rw [devB.eq_4, devB.eq_4]
                  rw [ih m j x hxN hxj, ih m k x hxN hxk]
              | const c =>
                  simp only [size] at hk hN hf
                  have hxN : size x ≤ N := by omega
                  have hxj : size x ≤ j := by omega
                  have hxk : size x ≤ k := by omega
                  rw [devB.eq_5, devB.eq_5]
                  cases hch : contractionHead? (.app (.const c) x) with
                  | none =>
                      dsimp only
                      rw [ih m j x hxN hxj, ih m k x hxN hxk]
                  | some p =>
                      obtain ⟨c', args⟩ := p
                      have hlt : ∀ a ∈ args, size a ≤ k := by
                        intro a ha
                        have hmem : a ∈ (Term.app (Term.const c) x).spine.2 := by
                          obtain ⟨hsp, -⟩ := contractionHead?_eq hch
                          rw [hsp]; simpa using ha
                        have h1 := size_spine_arg_lt hmem
                        simp only [size] at h1
                        omega
                      have hltj : ∀ a ∈ args, size a ≤ j := by
                        intro a ha
                        have hmem : a ∈ (Term.app (Term.const c) x).spine.2 := by
                          obtain ⟨hsp, -⟩ := contractionHead?_eq hch
                          rw [hsp]; simpa using ha
                        have h1 := size_spine_arg_lt hmem
                        simp only [size] at h1
                        omega
                      have hltN : ∀ a ∈ args, size a ≤ N := by
                        intro a ha
                        have hmem : a ∈ (Term.app (Term.const c) x).spine.2 := by
                          obtain ⟨hsp, -⟩ := contractionHead?_eq hch
                          rw [hsp]; simpa using ha
                        have h1 := size_spine_arg_lt hmem
                        simp only [size] at h1
                        omega
                      have hmap : ∀ as : List Term,
                          (∀ a ∈ as, size a ≤ k) → (∀ a ∈ as, size a ≤ j) →
                          (∀ a ∈ as, size a ≤ N) →
                          as.map (devB cfg m j) = as.map (devB cfg m k) := by
                        intro as
                        induction as with
                        | nil => intro _ _ _; rfl
                        | cons a as ihas =>
                            intro hbk' hbj' hbN'
                            rw [List.map_cons, List.map_cons]
                            rw [ihas (fun b hb => hbk' b (List.mem_cons_of_mem a hb))
                                (fun b hb => hbj' b (List.mem_cons_of_mem a hb))
                                (fun b hb => hbN' b (List.mem_cons_of_mem a hb))]
                            rw [ih m j a (hbN' a List.mem_cons_self)
                                (hbj' a List.mem_cons_self),
                                ih m k a (hbN' a List.mem_cons_self)
                                (hbk' a List.mem_cons_self)]
                      dsimp only
                      by_cases hadm : admissible cfg c' m
                      · rw [if_pos hadm, if_pos hadm,
                            hmap args hlt hltj hltN]
                      · rw [if_neg hadm, if_neg hadm]
                        rw [ih m j x hxN hxj, ih m k x hxN hxk]
              | app g y =>
                  simp only [size] at hk hN hf
                  have hgyN : size (Term.app g y) ≤ N := by
                    simp only [size]; omega
                  have hgyj : size (Term.app g y) ≤ j := by
                    simp only [size]; omega
                  have hgyk : size (Term.app g y) ≤ k := by
                    simp only [size]; omega
                  have hxN : size x ≤ N := by omega
                  have hxj : size x ≤ j := by omega
                  have hxk : size x ≤ k := by omega
                  rw [devB.eq_6, devB.eq_6]
                  cases hch : contractionHead? (Term.app (Term.app g y) x) with
                  | none =>
                      dsimp only
                      rw [ih m j (Term.app g y) hgyN hgyj,
                          ih m k (Term.app g y) hgyN hgyk,
                          ih m j x hxN hxj, ih m k x hxN hxk]
                  | some p =>
                      obtain ⟨c', args⟩ := p
                      have hlt : ∀ a ∈ args, size a ≤ k := by
                        intro a ha
                        have hmem : a ∈ (Term.app (Term.app g y) x).spine.2 := by
                          obtain ⟨hsp, -⟩ := contractionHead?_eq hch
                          rw [hsp]; simpa using ha
                        have h1 := size_spine_arg_lt hmem
                        simp only [size] at h1
                        omega
                      have hltj : ∀ a ∈ args, size a ≤ j := by
                        intro a ha
                        have hmem : a ∈ (Term.app (Term.app g y) x).spine.2 := by
                          obtain ⟨hsp, -⟩ := contractionHead?_eq hch
                          rw [hsp]; simpa using ha
                        have h1 := size_spine_arg_lt hmem
                        simp only [size] at h1
                        omega
                      have hltN : ∀ a ∈ args, size a ≤ N := by
                        intro a ha
                        have hmem : a ∈ (Term.app (Term.app g y) x).spine.2 := by
                          obtain ⟨hsp, -⟩ := contractionHead?_eq hch
                          rw [hsp]; simpa using ha
                        have h1 := size_spine_arg_lt hmem
                        simp only [size] at h1
                        omega
                      have hmap : ∀ as : List Term,
                          (∀ a ∈ as, size a ≤ k) → (∀ a ∈ as, size a ≤ j) →
                          (∀ a ∈ as, size a ≤ N) →
                          as.map (devB cfg m j) = as.map (devB cfg m k) := by
                        intro as
                        induction as with
                        | nil => intro _ _ _; rfl
                        | cons a as ihas =>
                            intro hbk' hbj' hbN'
                            rw [List.map_cons, List.map_cons]
                            rw [ihas (fun b hb => hbk' b (List.mem_cons_of_mem a hb))
                                (fun b hb => hbj' b (List.mem_cons_of_mem a hb))
                                (fun b hb => hbN' b (List.mem_cons_of_mem a hb))]
                            rw [ih m j a (hbN' a List.mem_cons_self)
                                (hbj' a List.mem_cons_self),
                                ih m k a (hbN' a List.mem_cons_self)
                                (hbk' a List.mem_cons_self)]
                      dsimp only
                      by_cases hadm : admissible cfg c' m
                      · rw [if_pos hadm, if_pos hadm,
                            hmap args hlt hltj hltN]
                      · rw [if_neg hadm, if_neg hadm]
                        rw [ih m j (Term.app g y) hgyN hgyj,
                            ih m k (Term.app g y) hgyN hgyk,
                            ih m j x hxN hxj, ih m k x hxN hxk]

/-- The complete development `dev cfg m t` of `t` at mask `m`: `devB`
run with `size t` units of fuel, which suffices because every recursive
call of `devB` lands on a strict subterm. -/
@[reducible] noncomputable def dev (cfg : Config) (m : Perm) (t : Term) :
    Term := devB cfg m (size t) t

/-- Developing a list of spine arguments at a sufficient fuel computes
pointwise `dev`. -/
theorem devB_map_dev (m : Perm) (fuel : Nat) (as : List Term)
    (hf : ∀ a ∈ as, size a ≤ fuel) :
    as.map (devB cfg m fuel) = as.map (dev cfg m) := by
  induction as with
  | nil => rfl
  | cons a as ih =>
      rw [List.map_cons, List.map_cons]
      rw [devB_eq_dev cfg (size a) m fuel a (Nat.le_refl _)
          (hf a List.mem_cons_self),
          ih (fun b hb => hf b (List.mem_cons_of_mem a hb))]

/-- `dev` on atoms. -/
theorem dev_atom (a : String) (m : Perm) : dev cfg m (.atom a) = .atom a := by
  simp [dev, devB, size]

/-- `dev` on constants. -/
theorem dev_const (c : Const) (m : Perm) : dev cfg m (.const c) = .const c := by
  simp [dev, devB, size]

/-- `dev` on scopes. -/
theorem dev_scope (l : Label) (m : Perm) : dev cfg m (.scope l) = .scope l := by
  simp [dev, devB, size]

/-- `dev` on brackets: the body is developed at the inner permission. -/
theorem dev_bracket (l : Label) (b : Term) (m : Perm) :
    dev cfg m (.bracket l b) = .bracket l (dev cfg (inner cfg l m) b) := by
  have hsz : size (.bracket l b) = (size b).succ := by simp [size]
  show devB cfg m (size (.bracket l b)) (.bracket l b) = _
  rw [hsz, devB.eq_7]

/-- `dev` on a `Sc` redex: the argument is developed at the inner
permission and wrapped in a bracket. -/
theorem dev_app_scope {l : Label} {a : Term} (m : Perm)
    (h : RedexAt cfg (.app (.scope l) a) m) :
    dev cfg m (.app (.scope l) a) =
      .bracket l (dev cfg (inner cfg l m) a) := by
  have hsz : size (.app (.scope l) a) = (size a + 1).succ := by
    simp only [size]; omega
  show devB cfg m (size (.app (.scope l) a)) (.app (.scope l) a) = _
  rw [hsz, devB.eq_2, if_pos h]
  rw [devB_eq_dev cfg (size a) (inner cfg l m) (size a + 1) a
      (Nat.le_refl _) (by omega)]

/-- `dev` on a non-redex `Sc`-shaped application. -/
theorem dev_app_scope_no {l : Label} {a : Term} (m : Perm)
    (h : ¬ RedexAt cfg (.app (.scope l) a) m) :
    dev cfg m (.app (.scope l) a) = .app (.scope l) (dev cfg m a) := by
  have hsz : size (.app (.scope l) a) = (size a + 1).succ := by
    simp only [size]; omega
  show devB cfg m (size (.app (.scope l) a)) (.app (.scope l) a) = _
  rw [hsz, devB.eq_2, if_neg h]
  rw [devB_eq_dev cfg (size a) m (size a + 1) a
      (Nat.le_refl _) (by omega)]

/-- `dev` on an `Abs` redex: body and value are developed at the inner
permission and wrapped in a bracketed application. -/
theorem dev_app_bracket {l : Label} {b v : Term} (m : Perm)
    (h : RedexAt cfg (.app (.bracket l b) v) m) :
    dev cfg m (.app (.bracket l b) v) =
      .bracket l (.app (dev cfg (inner cfg l m) b)
        (dev cfg (inner cfg l m) v)) := by
  have hsz : size (.app (.bracket l b) v) =
      (size b + size v + 1).succ := by simp only [size]; omega
  show devB cfg m (size (.app (.bracket l b) v)) (.app (.bracket l b) v) = _
  rw [hsz, devB.eq_3, if_pos h]
  rw [devB_eq_dev cfg (size b) (inner cfg l m) (size b + size v + 1) b
      (Nat.le_refl _) (by omega),
      devB_eq_dev cfg (size v) (inner cfg l m) (size b + size v + 1) v
      (Nat.le_refl _) (by omega)]

/-- `dev` on a non-redex `Abs`-shaped application. -/
theorem dev_app_bracket_no {l : Label} {b v : Term} (m : Perm)
    (h : ¬ RedexAt cfg (.app (.bracket l b) v) m) :
    dev cfg m (.app (.bracket l b) v) =
      .app (.bracket l (dev cfg (inner cfg l m) b)) (dev cfg m v) := by
  have hsz : size (.app (.bracket l b) v) =
      (size b + size v + 1).succ := by simp only [size]; omega
  show devB cfg m (size (.app (.bracket l b) v)) (.app (.bracket l b) v) = _
  rw [hsz, devB.eq_3, if_neg h]
  rw [devB_eq_dev cfg (size b) (inner cfg l m) (size b + size v + 1) b
      (Nat.le_refl _) (by omega),
      devB_eq_dev cfg (size v) m (size b + size v + 1) v
      (Nat.le_refl _) (by omega)]

/-- `dev` on an application whose function is an atom: never a root
redex, the argument is developed at the same mask. -/
theorem dev_app_atom (a : String) (x : Term) (m : Perm) :
    dev cfg m (.app (.atom a) x) = .app (.atom a) (dev cfg m x) := by
  have hsz : size (.app (.atom a) x) = (size x + 1).succ := by
    simp only [size]; omega
  show devB cfg m (size (.app (.atom a) x)) (.app (.atom a) x) = _
  rw [hsz, devB.eq_4]
  rw [devB_eq_dev cfg (size x) m (size x + 1) x
      (Nat.le_refl _) (by omega)]

/-- `dev` on an application whose function is a constant: a root
contraction when the spine is a candidate and admissible, otherwise the
argument is developed. -/
theorem dev_app_const (c : Const) (x : Term) (m : Perm) :
    dev cfg m (.app (.const c) x) =
      match contractionHead? (.app (.const c) x) with
      | some (c', args) =>
          if admissible cfg c' m then
            contractTemplate c' (args.map (dev cfg m))
          else .app (.const c) (dev cfg m x)
      | none => .app (.const c) (dev cfg m x) := by
  have hsz : size (.app (.const c) x) = (size x + 1).succ := by
    simp only [size]; omega
  show devB cfg m (size (.app (.const c) x)) (.app (.const c) x) = _
  rw [hsz, devB.eq_5]
  cases hch : contractionHead? (.app (.const c) x) with
  | none =>
      dsimp only
      rw [devB_eq_dev cfg (size x) m (size x + 1) x
          (Nat.le_refl _) (by omega)]
  | some p =>
      obtain ⟨c', args⟩ := p
      dsimp only
      by_cases hadm : admissible cfg c' m
      · rw [if_pos hadm, if_pos hadm]
        have hmap : List.map (devB cfg m (size x + 1)) args =
            List.map (dev cfg m) args := by
          apply devB_map_dev
          intro a ha
          have hmem : a ∈ (Term.app (Term.const c) x).spine.2 := by
            obtain ⟨hsp, -⟩ := contractionHead?_eq hch
            rw [hsp]; simpa using ha
          have h1 := size_spine_arg_lt hmem
          simp only [size] at h1
          omega
        rw [hmap]
      · rw [if_neg hadm, if_neg hadm]
        rw [devB_eq_dev cfg (size x) m (size x + 1) x
            (Nat.le_refl _) (by omega)]

/-- `dev` on an application whose function is itself an application: a
root contraction when the spine is a candidate and admissible,
otherwise both children are developed. -/
theorem dev_app_app (g y x : Term) (m : Perm) :
    dev cfg m (.app (.app g y) x) =
      match contractionHead? (.app (.app g y) x) with
      | some (c', args) =>
          if admissible cfg c' m then
            contractTemplate c' (args.map (dev cfg m))
          else .app (dev cfg m (.app g y)) (dev cfg m x)
      | none => .app (dev cfg m (.app g y)) (dev cfg m x) := by
  have hsz : size (.app (.app g y) x) =
      (size (.app g y) + size x).succ := by simp only [size]
  show devB cfg m (size (.app (.app g y) x)) (.app (.app g y) x) = _
  rw [hsz, devB.eq_6]
  cases hch : contractionHead? (.app (.app g y) x) with
  | none =>
      dsimp only
      rw [devB_eq_dev cfg (size (.app g y)) m
          (size (.app g y) + size x) (.app g y)
          (Nat.le_refl _) (by omega),
          devB_eq_dev cfg (size x) m
          (size (.app g y) + size x) x
          (Nat.le_refl _) (by omega)]
  | some p =>
      obtain ⟨c', args⟩ := p
      dsimp only
      by_cases hadm : admissible cfg c' m
      · rw [if_pos hadm, if_pos hadm]
        have hmap : List.map
            (devB cfg m (size (.app g y) + size x)) args =
            List.map (dev cfg m) args := by
          apply devB_map_dev
          intro a ha
          have hmem : a ∈ (Term.app (Term.app g y) x).spine.2 := by
            obtain ⟨hsp, -⟩ := contractionHead?_eq hch
            rw [hsp]; simpa using ha
          have h1 := size_spine_arg_lt hmem
          simp only [size] at h1
          simp only [size]
          omega
        rw [hmap]
      · rw [if_neg hadm, if_neg hadm]
        rw [devB_eq_dev cfg (size (.app g y)) m
            (size (.app g y) + size x) (.app g y)
            (Nat.le_refl _) (by omega),
            devB_eq_dev cfg (size x) m
            (size (.app g y) + size x) x
            (Nat.le_refl _) (by omega)]

/-- `ParList` of pointwise developments. -/
theorem ParList.map_dev {m : Perm} (as : List Term)
    (h : ∀ a ∈ as, ParAt cfg m a (dev cfg m a)) :
    ParList cfg m as (as.map (dev cfg m)) := by
  induction as with
  | nil => simp; exact .nil
  | cons a as ih =>
      simp only [List.map_cons]
      exact .cons a (dev cfg m a) as (as.map (dev cfg m))
        (h a (List.mem_cons_self))
        (ih fun b hb => h b (List.mem_cons_of_mem a hb))

/-- `t ⇒ t°`: the complete development is a parallel reduct. Proved by
strong induction on `size t`, since contraction arguments are deep
subterms. -/
theorem ParAt.dev_aux : ∀ n : Nat, ∀ t : Term, size t ≤ n →
    ∀ (m : Perm), ParAt cfg m t (dev cfg m t) := by
  intro n
  induction n with
  | zero =>
      intro t ht m
      exfalso
      have hpos := size_pos t
      omega
  | succ n ih =>
      intro t ht m
      cases t with
      | atom a =>
          rw [dev_atom]
          exact .atom a
      | const c =>
          rw [dev_const]
          exact .const c
      | scope l =>
          rw [dev_scope]
          exact .scope l
      | bracket l b =>
          have hbs : size b ≤ n := by
            simp only [size] at ht; omega
          rw [dev_bracket]
          exact .bracket l b _ (ih b hbs (inner cfg l m))
      | app f x =>
          cases f with
          | scope l =>
              simp only [size] at ht
              have hxN : size x ≤ n := by omega
              by_cases hR : RedexAt cfg (.app (.scope l) x) m
              · rw [dev_app_scope cfg m hR]
                obtain ⟨k, hk⟩ := hR
                cases k with
                | sc l' a' =>
                    obtain ⟨heq, hs⟩ := hk
                    injection heq with h1 h2
                    injection h1 with hll
                    subst hll
                    subst h2
                    exact .contract_sc l x _ (ih x hxN (inner cfg l m)) hs
                | abs l' b' v' =>
                    obtain ⟨heq, -⟩ := hk
                    injection heq with h1 h2
                    cases h1
                | contr c' args' =>
                    obtain ⟨hsp, -⟩ := hk
                    have hnone : contractionHead? (.app (.scope l) x) = none := rfl
                    rw [hnone] at hsp
                    cases hsp
              · rw [dev_app_scope_no cfg m hR]
                exact .app _ _ _ _ (.scope l) (ih x hxN m)
          | bracket l b =>
              simp only [size] at ht
              have hbN : size b ≤ n := by omega
              have hxN : size x ≤ n := by omega
              by_cases hR : RedexAt cfg (.app (.bracket l b) x) m
              · rw [dev_app_bracket cfg m hR]
                obtain ⟨k, hk⟩ := hR
                cases k with
                | abs l' b' v' =>
                    obtain ⟨heq, hs⟩ := hk
                    injection heq with h1 h2
                    injection h1 with hll hbb
                    subst hll
                    subst hbb
                    subst h2
                    exact .contract_abs l b x _ _
                      (ih b hbN (inner cfg l m))
                      (ih x hxN (inner cfg l m)) hs
                | sc l' a' =>
                    obtain ⟨heq, -⟩ := hk
                    injection heq with h1 h2
                    cases h1
                | contr c' args' =>
                    obtain ⟨hsp, -⟩ := hk
                    have hnone : contractionHead? (.app (.bracket l b) x) = none := rfl
                    rw [hnone] at hsp
                    cases hsp
              · rw [dev_app_bracket_no cfg m hR]
                exact .app _ _ _ _
                  (.bracket l b _ (ih b hbN (inner cfg l m)))
                  (ih x hxN m)
          | atom a =>
              simp only [size] at ht
              have hxN : size x ≤ n := by omega
              rw [dev_app_atom]
              exact .app _ _ _ _ (.atom a) (ih x hxN m)
          | const c =>
              simp only [size] at ht
              have hxN : size x ≤ n := by omega
              rw [dev_app_const]
              cases hch : contractionHead? (.app (.const c) x) with
              | none =>
                  dsimp only
                  exact .app _ _ _ _ (.const c) (ih x hxN m)
              | some p =>
                  obtain ⟨c', args⟩ := p
                  dsimp only
                  by_cases hadm : admissible cfg c' m
                  · rw [if_pos hadm]
                    have hmem : ∀ a ∈ args,
                        a ∈ (Term.app (Term.const c) x).spine.2 := by
                      intro a ha
                      obtain ⟨hsp, -⟩ := contractionHead?_eq hch
                      rw [hsp]; simpa using ha
                    have hpar : ∀ a ∈ args, ParAt cfg m a (dev cfg m a) := by
                      intro a ha
                      have h1 := size_spine_arg_lt (hmem a ha)
                      simp only [size] at h1
                      exact ih a (by omega) m
                    exact .contract_contr _ _ c' args _ hch hadm
                      (ParList.map_dev cfg args hpar) rfl
                  · rw [if_neg hadm]
                    exact .app _ _ _ _ (.const c) (ih x hxN m)
          | app g y =>
              simp only [size] at ht
              have hgyN : size (.app g y) ≤ n := by
                simp only [size]; omega
              have hxN : size x ≤ n := by omega
              rw [dev_app_app]
              cases hch : contractionHead? (.app (.app g y) x) with
              | none =>
                  dsimp only
                  exact .app _ _ _ _
                    (ih (.app g y) hgyN m) (ih x hxN m)
              | some p =>
                  obtain ⟨c', args⟩ := p
                  dsimp only
                  by_cases hadm : admissible cfg c' m
                  · rw [if_pos hadm]
                    have hmem : ∀ a ∈ args,
                        a ∈ (Term.app (Term.app g y) x).spine.2 := by
                      intro a ha
                      obtain ⟨hsp, -⟩ := contractionHead?_eq hch
                      rw [hsp]; simpa using ha
                    have hpar : ∀ a ∈ args, ParAt cfg m a (dev cfg m a) := by
                      intro a ha
                      have h1 := size_spine_arg_lt (hmem a ha)
                      simp only [size] at h1
                      exact ih a (by omega) m
                    exact .contract_contr _ _ c' args _ hch hadm
                      (ParList.map_dev cfg args hpar) rfl
                  · rw [if_neg hadm]
                    exact .app _ _ _ _
                      (ih (.app g y) hgyN m) (ih x hxN m)

/-- `t ⇒ t°`. -/
theorem ParAt.dev {m : Perm} {t : Term} : ParAt cfg m t (dev cfg m t) :=
  ParAt.dev_aux cfg (size t) t (Nat.le_refl _) m

end Config

end Spherepop
