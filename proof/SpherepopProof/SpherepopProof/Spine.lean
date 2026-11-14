/-
Lemmas relating the application spine of a term to the `apply`
construction: a term is the left-nested application of its spine head to
its spine arguments, and a constant-headed spine of matching arity is a
contraction candidate. These are the bookkeeping facts used when a
contraction's arguments are reduced one by one.
-/

import SpherepopProof.Config

namespace Spherepop

open Term

namespace Config

variable (cfg : Config)

/-- The spine of an application node. -/
theorem spine_app (f x : Term) :
    (app f x).spine = (f.spine.1, f.spine.2 ++ [x]) := rfl

/-- Appending a singleton argument on the right applies the head to the
previous application. -/
theorem apply_append_single (f : Term) (as : List Term) (x : Term) :
    apply f (as ++ [x]) = app (apply f as) x := by
  induction as generalizing f with
  | nil => rfl
  | cons a as ih =>
      have h1 : apply f (a :: (as ++ [x])) = apply (app f a) (as ++ [x]) := rfl
      have h2 : apply f (a :: as) = apply (app f a) as := rfl
      rw [show (a :: as) ++ [x] = a :: (as ++ [x]) from rfl, h1, ih (app f a), h2]

/-- `apply h args` has spine `(h.spine.1, h.spine.2 ++ args)`: the spine
head is that of `h` and the arguments are `h`'s own followed by `args`. -/
theorem spine_apply (h : Term) (args : List Term) :
    (apply h args).spine = (h.spine.1, h.spine.2 ++ args) := by
  induction args generalizing h with
  | nil =>
      show (apply h []).spine = _
      rw [show apply h [] = h from rfl, List.append_nil]
  | cons a as ih =>
      show (apply (app h a) as).spine = _
      rw [ih (app h a), spine_app]
      show (h.spine.1, h.spine.2 ++ [a] ++ as) =
        (h.spine.1, h.spine.2 ++ (a :: as))
      rw [List.append_assoc]
      rfl

/-- A term is the application of its spine head to its spine arguments. -/
theorem eq_apply_spine (t : Term) :
    t = apply t.spine.1 t.spine.2 := by
  induction t with
  | atom a => rfl
  | const c => rfl
  | scope l => rfl
  | app f x ihf =>
      change app f x = apply f.spine.1 (f.spine.2 ++ [x])
      rw [apply_append_single, ← ihf]
  | bracket l b ih => rfl

/-- If the spine of `t` has a nonempty argument list, `t` is an
application. -/
theorem isApp_of_spine_args_ne_nil {t h : Term} {args : List Term}
    (hs : t.spine = (h, args)) (ha : args ≠ []) : ∃ f x, t = .app f x := by
  cases t with
  | app f x => exact ⟨f, x, rfl⟩
  | atom a =>
      have e : args = [] := by
        have := congrArg Prod.snd hs
        simpa [spine] using this.symm
      exact absurd e ha
  | const c =>
      have e : args = [] := by
        have := congrArg Prod.snd hs
        simpa [spine] using this.symm
      exact absurd e ha
  | scope l =>
      have e : args = [] := by
        have := congrArg Prod.snd hs
        simpa [spine] using this.symm
      exact absurd e ha
  | bracket l b =>
      have e : args = [] := by
        have := congrArg Prod.snd hs
        simpa [spine] using this.symm
      exact absurd e ha

/-- A contraction candidate `t` presents spine `(const c, args)` with
`args.length = arity c`. -/
theorem contractionHead?_eq {t : Term} {c : Const} {args : List Term}
    (h : contractionHead? t = some (c, args)) :
    t.spine = (.const c, args) ∧ args.length = arity c := by
  unfold contractionHead? at h
  cases hs : t.spine with
  | mk hd hargs =>
      rw [hs] at h
      dsimp only at h
      cases hd with
      | const c' =>
          dsimp only at h
          by_cases hlen : hargs.length = arity c'
          · rw [if_pos hlen] at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact ⟨rfl, hlen⟩
          · rw [if_neg hlen] at h
            exact absurd h (by simp)
      | atom a => simp at h
      | scope l => simp at h
      | app f x => simp at h
      | bracket l b => simp at h

/-- A contraction candidate is an application. -/
theorem isApp_of_contractionHead? {t : Term} {p : Const × List Term}
    (h : contractionHead? t = some p) : ∃ f x, t = .app f x := by
  obtain ⟨c, args⟩ := p
  obtain ⟨hsp, hlen⟩ := contractionHead?_eq h
  have hne : args ≠ [] := by
    rintro rfl
    cases c <;> simp [arity] at hlen
  obtain ⟨f, x, hfx⟩ := isApp_of_spine_args_ne_nil hsp hne
  exact ⟨f, x, hfx⟩

/-- The spine of `apply (const c) args` is `(const c, args)`. -/
theorem spine_apply_const (c : Const) (args : List Term) :
    (apply (.const c) args).spine = (.const c, args) := by
  rw [spine_apply]
  rfl

/-- The spine of a constant is itself with no arguments. -/
theorem spine_const (c : Const) : (Term.const c).spine = (Term.const c, []) := rfl

/-- Every arity is positive, so a constant with an empty argument list is
never a contraction candidate. -/
theorem arity_ne_zero (c : Const) : arity c ≠ 0 := by
  cases c <;> decide

/-- The size of a term, used for the strong inductions of the
substitution and development lemmas. -/
def size : Term → Nat
  | .atom _ => 1
  | .const _ => 1
  | .scope _ => 1
  | .app f x => size f + size x + 1
  | .bracket _ b => size b + 1

theorem size_pos (t : Term) : 0 < size t := by
  cases t <;> simp only [size] <;> omega

theorem size_app_left (f x : Term) : size f < size (.app f x) := by
  simp only [size]; omega

theorem size_app_right (f x : Term) : size x < size (.app f x) := by
  simp only [size]; omega

theorem size_bracket_body (l : Label) (b : Term) :
    size b < size (.bracket l b) := by
  simp only [size]; omega

/-- Every spine argument of `t` is a strict subterm of `t`. -/
theorem size_spine_arg_lt {t a : Term} (h : a ∈ t.spine.2) :
    size a < size t := by
  induction t with
  | app f x ihf =>
      rw [spine_app] at h
      dsimp only at h
      rw [List.mem_append, List.mem_singleton] at h
      cases h with
      | inl h' => exact lt_trans (ihf h') (size_app_left f x)
      | inr h' => rw [h']; exact size_app_right f x
  | atom a => simp [spine] at h
  | const c => simp [spine] at h
  | scope l => simp [spine] at h
  | bracket l b ih => simp [spine] at h

/-- `apply (const c) args` is a contraction candidate when `args` has the
arity of `c`. -/
theorem contractionHead?_apply_const (c : Const) (args : List Term)
    (hlen : args.length = arity c) :
    contractionHead? (apply (.const c) args) = some (c, args) := by
  unfold contractionHead?
  rw [spine_apply_const]
  dsimp only
  rw [if_pos hlen]

end Config

end Spherepop
