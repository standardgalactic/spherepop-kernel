/-
The Takahashi property of the paper `notes/settled-scope.tex`: if
`t ⇒ u` then `u ⇒ t°`. Together with `ParAt.dev` (`t ⇒ t°`) it gives
the diamond property of `⇒`, and through `StepAt.subset_par` and
`ParAt.stepStar` the confluence of ordinary reduction `→`.

The proof follows the paper: `contractTemplate_par` is the
contraction-template congruence, `par_spine_lt` decomposes a parallel
step on a constant-headed spine, `parList_takahashi_of` lifts the
property to argument lists through the mutual recursor `ParList.rec`,
and `ParAt.takahashi_aux` is a strong induction on `size t`, mirroring
`ParAt.dev_aux`.
-/

import SpherepopProof.Dev

namespace Spherepop

open Term
open Classical

namespace Config

variable (cfg : Config)

/-- `ParList` is closed under append. Proved through the mutual
recursor `ParList.rec` with a trivial `ParAt` motive. -/
theorem ParList.append {m : Perm} {as bs cs ds : List Term}
    (h1 : ParList cfg m as bs) (h2 : ParList cfg m cs ds) :
    ParList cfg m (as ++ cs) (bs ++ ds) := by
  refine ParList.rec
    (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun m as bs _ => ParList cfg m cs ds →
      ParList cfg m (as ++ cs) (bs ++ ds))
    (by intros; trivial) (by intros; trivial) (by intros; trivial)
    (by intros; trivial) (by intros; trivial) (by intros; trivial)
    (by intros; trivial) (by intros; trivial)
    ?_ ?_ h1 h2
  · intro m h2
    simpa using h2
  · intro m a a' as1 as1' ha ht iha iht h2
    exact .cons a a' (as1 ++ cs) (as1' ++ ds) ha (iht h2)

/-- `contractTemplate c args` is the bare constant when `args` does not
have the arity of `c`. -/
theorem ct_len_ne {c : Const} {args : List Term}
    (h : args.length ≠ arity c) : contractTemplate c args = .const c := by
  cases c <;> (unfold contractTemplate <;> split <;> simp_all [arity])

/-- The contraction template is a congruence for `⇒` on argument
lists. -/
theorem contractTemplate_par (c : Const) {as bs : List Term} {m : Perm}
    (h : ParList cfg m as bs) :
    ParAt cfg m (contractTemplate c as) (contractTemplate c bs) := by
  have hlen := ParList.length_eq cfg h
  by_cases hca : as.length = arity c
  · have hcb : bs.length = arity c := by rw [← hlen]; exact hca
    cases c with
    | I =>
        obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp hca
        obtain ⟨b, rfl⟩ := List.length_eq_one_iff.mp hcb
        cases h with
        | cons _ _ _ _ hab _ => exact hab
    | K =>
        obtain ⟨x, y, rfl⟩ := List.length_eq_two.mp hca
        obtain ⟨x', y', rfl⟩ := List.length_eq_two.mp hcb
        cases h with
        | cons _ _ _ _ hx h1 =>
            cases h1 with
            | cons _ _ _ _ hy _ => exact hx
    | W =>
        obtain ⟨f, x, rfl⟩ := List.length_eq_two.mp hca
        obtain ⟨f', x', rfl⟩ := List.length_eq_two.mp hcb
        cases h with
        | cons _ _ _ _ hf h1 =>
            cases h1 with
            | cons _ _ _ _ hx _ =>
                exact .app _ _ _ _ (.app _ _ _ _ hf hx) hx
    | B =>
        obtain ⟨f, g, x, rfl⟩ := List.length_eq_three.mp hca
        obtain ⟨f', g', x', rfl⟩ := List.length_eq_three.mp hcb
        cases h with
        | cons _ _ _ _ hf h1 =>
            cases h1 with
            | cons _ _ _ _ hg h2 =>
                cases h2 with
                | cons _ _ _ _ hx _ =>
                    exact .app _ _ _ _ hf (.app _ _ _ _ hg hx)
    | C =>
        obtain ⟨f, x, y, rfl⟩ := List.length_eq_three.mp hca
        obtain ⟨f', x', y', rfl⟩ := List.length_eq_three.mp hcb
        cases h with
        | cons _ _ _ _ hf h1 =>
            cases h1 with
            | cons _ _ _ _ hx h2 =>
                cases h2 with
                | cons _ _ _ _ hy _ =>
                    exact .app _ _ _ _ (.app _ _ _ _ hf hy) hx
    | S =>
        obtain ⟨f, g, x, rfl⟩ := List.length_eq_three.mp hca
        obtain ⟨f', g', x', rfl⟩ := List.length_eq_three.mp hcb
        cases h with
        | cons _ _ _ _ hf h1 =>
            cases h1 with
            | cons _ _ _ _ hg h2 =>
                cases h2 with
                | cons _ _ _ _ hx _ =>
                    exact .app _ _ _ _ (.app _ _ _ _ hf hx)
                        (.app _ _ _ _ hg hx)
  · rw [ct_len_ne hca, ct_len_ne (fun e => hca (hlen.trans e))]
    exact .const c

/-- If `t`'s spine is headed by `const c` with `args.length ≠ arity c`,
`t` is not a contraction candidate. -/
theorem contractionHead?_eq_none {t : Term} {c : Const} {args : List Term}
    (hs : t.spine = (.const c, args)) (hlen : args.length ≠ arity c) :
    contractionHead? t = none := by
  cases h : contractionHead? t with
  | none => rfl
  | some p =>
      obtain ⟨c', args'⟩ := p
      obtain ⟨hspine, hlen2⟩ := contractionHead?_eq h
      rw [hs] at hspine
      injection hspine with hc ha
      injection hc with hcc
      subst hcc
      subst ha
      exact absurd hlen2 hlen

/-- A constant-headed spine with full arity is a contraction candidate. -/
theorem contractionHead?_of_spine {t : Term} {c : Const} {args : List Term}
    (hs : t.spine = (.const c, args)) (hlen : args.length = arity c) :
    contractionHead? t = some (c, args) := by
  unfold contractionHead?
  rw [hs]
  simp only
  rw [if_pos hlen]

/-- A parallel step on a constant-headed spine with fewer arguments
than the arity decomposes pointwise: the reduct has the same head and
`ParList`-related arguments. Proved by induction on `t`; the app case
uses the induction hypothesis on the function child. -/
theorem par_spine_lt (t : Term) :
    ∀ {m : Perm} {u : Term}, ParAt cfg m t u →
    ∀ {c : Const} {as : List Term}, t.spine = (.const c, as) →
    as.length < arity c → ∃ as', u.spine = (.const c, as') ∧
      ParList cfg m as as' := by
  induction t with
  | atom a =>
      intro m u hp c as hs hlen
      cases hp with
      | atom a' => simp [spine] at hs
      | contract_contr t' u' c' args' args'' hsp hadm hpar hu =>
          simp [contractionHead?, spine] at hsp
  | const c0 =>
      intro m u hp c as hs hlen
      cases hp with
      | const c' =>
          have hs' : (Term.const c0).spine = (Term.const c0, []) :=
            spine_const c0
          rw [hs'] at hs
          injection hs with h1 h2
          injection h1 with hc
          subst hc
          subst h2
          exact ⟨[], spine_const _, .nil⟩
      | contract_contr t' u' c' args' args'' hsp hadm hpar hu =>
          obtain ⟨hspine, hlen2⟩ := contractionHead?_eq hsp
          have hs' : (Term.const c0).spine = (Term.const c0, []) :=
            spine_const c0
          rw [hs'] at hspine
          injection hspine with hc ha
          injection hc with hcc
          subst hcc
          subst ha
          simp only [List.length_nil] at hlen2
          exact absurd hlen2 (Ne.symm (arity_ne_zero _))
  | scope l =>
      intro m u hp c as hs hlen
      cases hp with
      | scope l' => simp [spine] at hs
      | contract_contr t' u' c' args' args'' hsp hadm hpar hu =>
          simp [contractionHead?, spine] at hsp
  | bracket l b ihb =>
      intro m u hp c as hs hlen
      cases hp with
      | bracket l' b' hb => simp [spine] at hs
      | contract_contr t' u' c' args' args'' hsp hadm hpar hu =>
          simp [contractionHead?, spine] at hsp
  | app f x ihf ihx =>
      intro m u hp c as hs hlen
      cases hp with
      | app _ f' _ x' hf hx =>
          rw [spine_app] at hs
          injection hs with h1 h2
          have hfsp : f.spine = (Term.const c, f.spine.2) :=
            Prod.ext_iff.mpr ⟨h1, rfl⟩
          have hlenf : f.spine.2.length < arity c := by
            have h2l := congrArg List.length h2
            simp only [List.length_append, List.length_cons,
              List.length_nil] at h2l
            omega
          obtain ⟨asf', hfsp', hfpar⟩ := ihf hf hfsp hlenf
          refine ⟨asf' ++ [x'], ?_, ?_⟩
          · show (Term.app f' x').spine = (Term.const c, asf' ++ [x'])
            rw [spine_app, hfsp']
          · rw [← h2]
            exact ParList.append cfg hfpar
              (.cons x x' [] [] hx .nil)
      | contract_sc l _ _ _ _ =>
          have hsp' : (Term.app (Term.scope l) x).spine =
              (Term.scope l, [x]) := rfl
          rw [hsp'] at hs
          injection hs with h1 h2
          cases h1
      | contract_abs l b _ _ _ _ _ _ =>
          have hsp' : (Term.app (Term.bracket l b) x).spine =
              (Term.bracket l b, [x]) := rfl
          rw [hsp'] at hs
          injection hs with h1 h2
          cases h1
      | contract_contr t' u' c' args' args'' hsp hadm hpar hu =>
          obtain ⟨hspine, hlen2⟩ := contractionHead?_eq hsp
          rw [hs] at hspine
          injection hspine with hc ha
          injection hc with hcc
          subst hcc
          subst ha
          exfalso
          omega

/-- The `ParList` half of the Takahashi property, relative to a
size-bounded pointwise development hypothesis. Proved through the
mutual recursor `ParList.rec` with a trivial `ParAt` motive: the
size bound travels inside the `ParList` motive so that every
cons-node can feed `hpar`. -/
theorem parList_takahashi_of (N : Nat) {m : Perm} {as bs : List Term}
    (h : ParList cfg m as bs) (hN : ∀ a ∈ as, size a < N)
    (hpar : ∀ {m' : Perm} {s s' : Term}, ParAt cfg m' s s' →
      size s < N → ParAt cfg m' s' (dev cfg m' s)) :
    ParList cfg m bs (as.map (dev cfg m)) := by
  refine ParList.rec
    (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun m' as bs _ => (∀ a ∈ as, size a < N) →
      ParList cfg m' bs (as.map (dev cfg m')))
    (by intros; trivial) (by intros; trivial) (by intros; trivial)
    (by intros; trivial) (by intros; trivial) (by intros; trivial)
    (by intros; trivial) (by intros; trivial)
    ?_ ?_ h hN
  · intro m' hall
    exact .nil
  · intro m' a a' as as' ha ht iha iht hall
    refine .cons a' (dev cfg m' a) as' (as.map (dev cfg m')) ?_ ?_
    · exact hpar ha (hall a List.mem_cons_self)
    · exact iht (fun b hb => hall b (List.mem_cons_of_mem a hb))

/-- The Takahashi property: `t ⇒ u` implies `u ⇒ t°`. Proved by strong
induction on `size t`, mirroring `ParAt.dev_aux`; every recursive need
on a strict subterm is served by the induction hypothesis at the
appropriate mask, and contraction arguments are strict subterms by
`size_spine_arg_lt`. -/
theorem ParAt.takahashi_aux : ∀ n : Nat, ∀ t : Term, size t ≤ n →
    ∀ (m : Perm) {u : Term}, ParAt cfg m t u →
    ParAt cfg m u (Config.dev cfg m t) := by
  intro n
  induction n with
  | zero =>
      intro t ht m u hp
      exfalso
      have hpos := size_pos t
      omega
  | succ n ih =>
      intro t ht m u hp
      have ih' : ∀ s : Term, size s ≤ n → ∀ (m' : Perm) {v : Term},
          ParAt cfg m' s v → ParAt cfg m' v (Config.dev cfg m' s) := ih
      cases t with
      | atom a =>
          cases hp with
          | atom a' =>
              rw [dev_atom]
              exact .atom a
          | contract_contr t' u' c' args' args'' hsp hadm hpar hu =>
              simp [contractionHead?, spine] at hsp
      | const c =>
          cases hp with
          | const c' =>
              rw [dev_const]
              exact .const c
          | contract_contr t' u' c' args' args'' hsp hadm hpar hu =>
              obtain ⟨hspine, hlen2⟩ := contractionHead?_eq hsp
              have hs' : (Term.const c).spine = (Term.const c, []) :=
                spine_const c
              rw [hs'] at hspine
              injection hspine with hc ha
              injection hc with hcc
              subst hcc
              subst ha
              simp only [List.length_nil] at hlen2
              exact absurd hlen2 (Ne.symm (arity_ne_zero _))
      | scope l =>
          cases hp with
          | scope l' =>
              rw [dev_scope]
              exact .scope l
          | contract_contr t' u' c' args' args'' hsp hadm hpar hu =>
              simp [contractionHead?, spine] at hsp
      | bracket l b =>
          cases hp with
          | bracket _ _ b' hb =>
              have hbs : size b ≤ n := by
                simp only [size] at ht; omega
              rw [dev_bracket]
              exact .bracket l b' _ (ih' b hbs (inner cfg l m) hb)
          | contract_contr t' u' c' args' args'' hsp hadm hpar hu =>
              simp [contractionHead?, spine] at hsp
      | app f x =>
          simp only [size] at ht
          have hfs : size f ≤ n := by omega
          have hxs : size x ≤ n := by omega
          cases hp with
          | app _ f' _ x' hf hx =>
              have hfs' : size f ≤ n := hfs
              cases f with
              | atom a =>
                  rw [dev_app_atom]
                  exact .app _ _ _ _ (ih' _ hfs' m hf) (ih' x hxs m hx)
              | scope l =>
                  by_cases hR : RedexAt cfg (Term.app (Term.scope l) x) m
                  · rw [dev_app_scope cfg m hR]
                    obtain ⟨k, hk⟩ := hR
                    cases k with
                    | sc l' a' =>
                        obtain ⟨heq, hs⟩ := hk
                        injection heq with h1 h2
                        injection h1 with hll
                        subst hll
                        subst h2
                        have hxeq : x' = x :=
                          ParAt.eq_of_settled cfg x
                            (Finset.Subset.refl _) hs hx
                        subst x'
                        cases hf with
                        | scope l'' =>
                            exact .contract_sc l x _
                              (ParAt.dev cfg (m := inner cfg l m)
                                (t := x)) hs
                        | contract_contr t'' u'' c'' args'' args3 hsp''
                            hadm'' hpar'' hu'' =>
                            simp [contractionHead?, spine] at hsp''
                    | abs l' b' v' =>
                        obtain ⟨heq, -⟩ := hk
                        injection heq with h1 h2
                        cases h1
                    | contr c' args' =>
                        obtain ⟨hsp, -⟩ := hk
                        have hnone : contractionHead?
                            (Term.app (Term.scope l) x) = none := rfl
                        rw [hnone] at hsp
                        cases hsp
                  · rw [dev_app_scope_no cfg m hR]
                    exact .app _ _ _ _ (ih' _ hfs' m hf) (ih' x hxs m hx)
              | bracket l b =>
                  have hbs : size b ≤ n := by
                    simp only [size] at ht; omega
                  by_cases hR : RedexAt cfg
                      (Term.app (Term.bracket l b) x) m
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
                        have hxeq : x' = x :=
                          ParAt.eq_of_settled cfg x
                            (Finset.Subset.refl _) hs hx
                        subst x'
                        cases hf with
                        | bracket _ _ b'' hb_inner =>
                            have hbdev : ParAt cfg (inner cfg l m) b''
                                (Config.dev cfg (inner cfg l m) b) :=
                              ih' b hbs (inner cfg l m) hb_inner
                            exact .contract_abs l b'' x _ _ hbdev
                              (ParAt.dev cfg (m := inner cfg l m)
                                (t := x)) hs
                        | contract_contr t'' u'' c'' args'' args3 hsp''
                            hadm'' hpar'' hu'' =>
                            simp [contractionHead?, spine] at hsp''
                    | sc l' a' =>
                        obtain ⟨heq, -⟩ := hk
                        injection heq with h1 h2
                        cases h1
                    | contr c' args' =>
                        obtain ⟨hsp, -⟩ := hk
                        have hnone : contractionHead?
                            (Term.app (Term.bracket l b) x) = none := rfl
                        rw [hnone] at hsp
                        cases hsp
                  · rw [dev_app_bracket_no cfg m hR]
                    exact .app _ _ _ _ (ih' _ hfs' m hf) (ih' x hxs m hx)
              | const c =>
                  cases hf with
                  | const c' =>
                      rw [dev_app_const]
                      cases hch : contractionHead?
                          (Term.app (Term.const c) x) with
                      | none =>
                          dsimp only
                          exact .app _ _ _ _ (.const c)
                            (ih' x hxs m hx)
                      | some p =>
                          obtain ⟨c'', args⟩ := p
                          dsimp only
                          by_cases hadm : admissible cfg c'' m
                          · rw [if_pos hadm]
                            obtain ⟨hspine, hlen⟩ :=
                              contractionHead?_eq hch
                            have hspine' :
                                (Term.app (Term.const c) x).spine =
                                (Term.const c, [x]) :=
                              spine_apply_const c [x]
                            rw [hspine'] at hspine
                            injection hspine with hc ha
                            injection hc with hcc
                            subst hcc
                            subst ha
                            have hpar' : ParList cfg m [x']
                                [Config.dev cfg m x] :=
                              .cons x' (Config.dev cfg m x) [] []
                                (ih' x hxs m hx) .nil
                            have hsp'' : contractionHead?
                                (Term.app (Term.const c) x') =
                                some (c, [x']) := by
                              have hlen' : ([x'] : List Term).length =
                                  arity c := by
                                simp only [List.length_cons,
                                  List.length_nil] at hlen ⊢
                                omega
                              have hs' :
                                  (Term.app (Term.const c) x').spine =
                                  (Term.const c, [x']) :=
                                spine_apply_const c [x']
                              unfold contractionHead?
                              rw [hs']
                              simp only
                              rw [if_pos hlen']
                            exact .contract_contr _ _ c _ _ hsp'' hadm
                              hpar' rfl
                          · rw [if_neg hadm]
                            exact .app _ _ _ _ (.const c)
                              (ih' x hxs m hx)
                  | contract_contr t'' u'' c'' args'' args3 hsp''
                      hadm'' hpar'' hu'' =>
                      have hnone : contractionHead? (Term.const c) =
                          none :=
                        contractionHead?_eq_none (spine_const c)
                          (fun h => arity_ne_zero c h.symm)
                      rw [hnone] at hsp''
                      cases hsp''
              | app g y =>
                  have hgy : size (Term.app g y) ≤ n := by
                    simp only [size] at ht; omega
                  rw [dev_app_app]
                  cases hch : contractionHead?
                      (Term.app (Term.app g y) x) with
                  | none =>
                      dsimp only
                      exact .app _ _ _ _ (ih' _ hfs' m hf)
                        (ih' x hxs m hx)
                  | some p =>
                      obtain ⟨c', args⟩ := p
                      dsimp only
                      by_cases hadm : admissible cfg c' m
                      · rw [if_pos hadm]
                        obtain ⟨hspine, hlen⟩ := contractionHead?_eq hch
                        have hspapp :
                            (Term.app (Term.app g y) x).spine =
                            ((Term.app g y).spine.1,
                              (Term.app g y).spine.2 ++ [x]) :=
                          spine_app _ _
                        rw [hspapp] at hspine
                        injection hspine with h1 h2
                        have hfsp : (Term.app g y).spine =
                            (Term.const c', (Term.app g y).spine.2) :=
                          Prod.ext_iff.mpr ⟨h1, rfl⟩
                        have hlenf : (Term.app g y).spine.2.length <
                            arity c' := by
                          have h2l := congrArg List.length h2
                          simp only [List.length_append, List.length_cons,
                            List.length_nil] at h2l hlen
                          omega
                        obtain ⟨asf', hfsp', hfpar⟩ :=
                          par_spine_lt cfg (Term.app g y) hf hfsp hlenf
                        have huspine : (Term.app f' x').spine =
                            (Term.const c', asf' ++ [x']) := by
                          rw [spine_app, hfsp']
                        have hlen'' : (asf' ++ [x']).length = arity c' := by
                          have hfl := ParList.length_eq cfg hfpar
                          have h2l := congrArg List.length h2
                          simp only [List.length_append, List.length_cons,
                            List.length_nil] at hfl h2l hlen
                          simp only [List.length_append, List.length_cons,
                            List.length_nil]
                          omega
                        have hch' : contractionHead?
                            (Term.app f' x') =
                            some (c', asf' ++ [x']) :=
                          contractionHead?_of_spine huspine hlen''
                        have hpar' : ParList cfg m (asf' ++ [x'])
                            (args.map (Config.dev cfg m)) := by
                          have hargs : args =
                              (Term.app g y).spine.2 ++ [x] := h2.symm
                          subst hargs
                          rw [List.map_append, List.map_cons,
                            List.map_nil]
                          apply ParList.append cfg _
                            (.cons x' (Config.dev cfg m x) [] []
                              (ih' x hxs m hx) .nil)
                          apply parList_takahashi_of cfg (n + 1) hfpar
                          · intro a ha
                            have hmem : a ∈
                                (Term.app (Term.app g y) x).spine.2 := by
                              rw [hspapp]
                              simp only [List.mem_append]
                              exact Or.inl ha
                            have h1 := size_spine_arg_lt hmem
                            simp only [size] at h1 ht
                            omega
                          · intro m'' s s' hp hsz
                            exact ih' s (by omega) m'' hp
                        exact .contract_contr _ _ c' _ _ hch' hadm hpar' rfl
                      · rw [if_neg hadm]
                        exact .app _ _ _ _ (ih' _ hfs' m hf)
                          (ih' x hxs m hx)
          | contract_sc l a a' h hs =>
              -- `a` is identified with `x` by index unification;
              -- `u = bracket l a'`, `dev` contracts the `Sc` redex
              have hR : RedexAt cfg (Term.app (Term.scope l) x) m :=
                ⟨.sc l x, rfl, hs⟩
              rw [dev_app_scope cfg m hR]
              exact .bracket l a' _ (ih' x hxs (inner cfg l m) h)
          | contract_abs l b v b' v' hb hv hs =>
              -- `v` is identified with `x`; `u = bracket l (app b' v')`
              have hbs : size b ≤ n := by
                simp only [size] at ht; omega
              have hR : RedexAt cfg (Term.app (Term.bracket l b) x) m :=
                ⟨.abs l b x, rfl, hs⟩
              rw [dev_app_bracket cfg m hR]
              exact .bracket l _ _
                (.app _ _ _ _
                  (ih' b hbs (inner cfg l m) hb)
                  (ih' x hxs (inner cfg l m) hv))
          | contract_contr t' u' c args args' hsp hadm hpar hu =>
              rw [hu]
              cases f with
              | atom a =>
                  have hnone : contractionHead?
                      (Term.app (Term.atom a) x) = none := rfl
                  rw [hnone] at hsp
                  cases hsp
              | scope l =>
                  have hnone : contractionHead?
                      (Term.app (Term.scope l) x) = none := rfl
                  rw [hnone] at hsp
                  cases hsp
              | bracket l b =>
                  have hnone : contractionHead?
                      (Term.app (Term.bracket l b) x) = none := rfl
                  rw [hnone] at hsp
                  cases hsp
              | const c0 =>
                  rw [dev_app_const]
                  rw [hsp]
                  dsimp only
                  rw [if_pos hadm]
                  apply contractTemplate_par cfg c
                  apply parList_takahashi_of cfg (n + 1) hpar
                  · intro a ha
                    obtain ⟨hsp2, -⟩ := contractionHead?_eq hsp
                    have hmem : a ∈ (Term.app (Term.const c0) x).spine.2 := by
                      rw [hsp2]; simpa using ha
                    have h1 := size_spine_arg_lt hmem
                    simp only [size] at h1 ht
                    omega
                  · intro m' s s' hp hsz
                    exact ih' s (by omega) m' hp
              | app g y =>
                  rw [dev_app_app]
                  rw [hsp]
                  dsimp only
                  rw [if_pos hadm]
                  apply contractTemplate_par cfg c
                  apply parList_takahashi_of cfg (n + 1) hpar
                  · intro a ha
                    obtain ⟨hsp2, -⟩ := contractionHead?_eq hsp
                    have hmem : a ∈ (Term.app (Term.app g y) x).spine.2 := by
                      rw [hsp2]; simpa using ha
                    have h1 := size_spine_arg_lt hmem
                    simp only [size] at h1 ht
                    omega
                  · intro m' s s' hp hsz
                    exact ih' s (by omega) m' hp

/-- `u ⇒ t°` whenever `t ⇒ u`. -/
theorem ParAt.takahashi {m : Perm} {t u : Term}
    (hp : ParAt cfg m t u) : ParAt cfg m u (Config.dev cfg m t) := by
  exact ParAt.takahashi_aux cfg (size t) t (Nat.le_refl _) m hp

end Config

end Spherepop
