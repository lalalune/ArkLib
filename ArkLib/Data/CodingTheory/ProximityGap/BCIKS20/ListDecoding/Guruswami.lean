/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Katerina Hristova, František Silváši, Julian Sutherland,
         Ilia Vlasov, Chung Thai Nguyen
-/

import ArkLib.Data.CodingTheory.ProximityGap.Basic
import ArkLib.Data.CodingTheory.GuruswamiSudan.Basic
import ArkLib.Data.CodingTheory.GuruswamiSudan.GuruswamiSudan
import ArkLib.Data.Polynomial.Trivariate

namespace ProximityGap

open NNReal Finset Function ProbabilityTheory Code
open scoped BigOperators LinearCode

universe u v w k l

/-! ### Generic order-of-vanishing lower bound over an integral-domain coefficient ring

The bivariate root-multiplicity lower bound `GuruswamiSudan.rootMultiplicity_ge_of_shift_zero`
is stated over a field.  The trivariate Guruswami–Sudan setting of [BCIKS20] Claim 5.4 evaluates
multiplicity of `Q : F[Z][X][Y]` over the coefficient ring `S = F[Z] = Polynomial F`, which is an
integral domain but not a field.  The lemmas below re-establish the order-`m` vanishing criterion
(`triv_rootMultiplicity_ge_of_shift_zero`) over any `[CommRing S] [IsDomain S]`, mirroring the
field proof but only using `NoZeroDivisors`. -/
section GenericTrivariateMultiplicity

open Polynomial Polynomial.Bivariate

variable {S : Type} [CommRing S] [IsDomain S] [DecidableEq S]

private lemma triv_comp_add_C_eq_zero_iff (p : S[X]) (a : S) :
    p.comp (Polynomial.X + Polynomial.C a) = 0 ↔ p = 0 := by
  rw [Polynomial.comp_eq_zero_iff]
  refine ⟨?_, fun h => Or.inl h⟩
  rintro (h | ⟨_, h2⟩)
  · exact h
  · exfalso; have := congrArg (fun q => Polynomial.coeff q 1) h2; simp at this

private lemma triv_compRingHom_addC_injective (a : S) :
    Function.Injective (Polynomial.compRingHom (Polynomial.X + Polynomial.C a) : S[X] →+* S[X]) := by
  rw [injective_iff_map_eq_zero]; intro r hr
  rw [Polynomial.coe_compRingHom] at hr; exact (triv_comp_add_C_eq_zero_iff r a).mp hr

omit [IsDomain S] in
private lemma triv_rm0_none_imp_zero (g : S[X][Y]) (hg : rootMultiplicity₀ g = none) :
    g = 0 := by
  unfold rootMultiplicity₀ at hg
  cases hwd : weightedDegree g 1 1 with
  | none => exact absurd hwd (weightedDegree_ne_none _ _ _)
  | some deg =>
    rw [hwd] at hg; simp only at hg
    rw [List.min?_eq_none_iff, List.filterMap_eq_nil_iff] at hg
    have hcoeff_zero : ∀ s t, s ≤ deg → t ≤ deg → coeff g s t = 0 := by
      intro s t hs ht
      have hmem := hg (s, t) (by
        rw [List.product, List.mem_flatMap]
        refine ⟨s, List.mem_range.mpr (Nat.lt_succ_of_le hs), ?_⟩
        rw [List.mem_map]; exact ⟨t, List.mem_range.mpr (Nat.lt_succ_of_le ht), rfl⟩)
      by_contra hc; simp only [hc, if_false] at hmem; exact (Option.some_ne_none _ hmem)
    have hwd_nat : natWeightedDegree g 1 1 = deg := by
      rw [weightedDegree_eq_natWeightedDegree] at hwd; exact Option.some.inj hwd
    have hcn : ∀ nn, g.coeff nn = 0 := by
      intro nn; by_contra hgn
      have hb : 1 * (g.coeff nn).natDegree + 1 * nn ≤ natWeightedDegree g 1 1 :=
        Finset.le_sup (f := fun mm => 1 * (g.coeff mm).natDegree + 1 * mm)
          (Polynomial.mem_support_iff.mpr hgn)
      rw [hwd_nat] at hb; simp only [one_mul] at hb
      have hn' : nn ≤ deg := by omega
      apply hgn; ext s; simp only [Polynomial.coeff_zero]
      by_cases hs : s ≤ deg
      · have := hcoeff_zero s nn hs hn'; rwa [Bivariate.coeff] at this
      · push Not at hs; exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    exact Polynomial.ext (fun nn => by rw [hcn nn, Polynomial.coeff_zero])

private lemma triv_shift_eq_zero_iff (f : S[X][Y]) (x y : S) :
    shift f x y = 0 ↔ f = 0 := by
  unfold shift
  rw [Polynomial.map_eq_zero_iff (triv_compRingHom_addC_injective x)]
  exact triv_comp_add_C_eq_zero_iff f (Polynomial.C y)

omit [IsDomain S] in
private lemma triv_rm0_some_witness (g : S[X][Y]) (val : ℕ)
    (hg : rootMultiplicity₀ g = some val) :
    ∃ s t, coeff g s t ≠ 0 ∧ s + t = val := by
  unfold rootMultiplicity₀ at hg
  cases hwd : weightedDegree g 1 1 with
  | none => rw [hwd] at hg; simp at hg
  | some deg =>
    rw [hwd] at hg; simp only at hg
    have hmem := List.min?_mem hg
    rw [List.mem_filterMap] at hmem
    obtain ⟨⟨s, t⟩, _, hval⟩ := hmem
    by_cases hc : coeff g s t = 0
    · simp [hc] at hval
    · simp only [hc, if_false] at hval; exact ⟨s, t, hc, by simpa using hval⟩

/-- Order-`m` vanishing from shifted-coefficient vanishing, over an integral-domain coefficient
ring `S`.  This is the `[CommRing S] [IsDomain S]` port of the field-only
`GuruswamiSudan.rootMultiplicity_ge_of_shift_zero`, needed for the trivariate setting `S = F[Z]`. -/
private lemma triv_rootMultiplicity_ge_of_shift_zero {f : S[X][Y]} {x y : S}
    {m : ℕ} (hf : f ≠ 0)
    (h : ∀ s t, s + t < m → ((shift f x y).coeff t).coeff s = 0) :
    (m : ℕ) ≤ Bivariate.rootMultiplicity f x y := by
  unfold Bivariate.rootMultiplicity
  cases hrm : rootMultiplicity₀ (shift f x y) with
  | none => exact absurd ((triv_shift_eq_zero_iff f x y).mp (triv_rm0_none_imp_zero _ hrm)) hf
  | some val =>
    show (m : Option ℕ) ≤ some val
    have hmval : m ≤ val := by
      by_contra hlt
      push Not at hlt
      obtain ⟨s, t, hne, hst⟩ := triv_rm0_some_witness (shift f x y) val hrm
      apply hne; rw [Bivariate.coeff]; exact h s t (by omega)
    exact_mod_cast hmval

end GenericTrivariateMultiplicity

/-! ### Generic weighted-degree sub-additivity (any coefficient semiring)

These mirror `GuruswamiSudan.natWeightedDegree_{add,sum,smul}_le` (which are proven for a field
coefficient ring) over an arbitrary semiring `S`, so they apply to the trivariate setting where the
coefficient ring is `S = F[Z]`. -/
section GenericTrivariateDegree

open Polynomial Polynomial.Bivariate

variable {S : Type} [Semiring S]

lemma tri_natWeightedDegree_add_le (p q : S[X][Y]) (u v : ℕ) :
    natWeightedDegree (p + q) u v ≤ max (natWeightedDegree p u v) (natWeightedDegree q u v) := by
  refine Finset.sup_le fun mm hm ↦ ?_
  by_cases h : mm ∈ p.support <;>
  by_cases h' : mm ∈ q.support <;>
    simp_all only [Polynomial.mem_support_iff, coeff_add, ne_eq, le_sup_iff]
  · have h_deg : (p.coeff mm + q.coeff mm).natDegree ≤
        max ((p.coeff mm).natDegree) ((q.coeff mm).natDegree) :=
      natDegree_add_le (p.coeff mm) (q.coeff mm)
    cases max_cases (natDegree (p.coeff mm)) (natDegree (q.coeff mm)) <;>
      simp_all only [sup_of_le_left, sup_eq_left, and_self, natWeightedDegree]
    · exact Or.inl (le_trans (add_le_add (mul_le_mul_of_nonneg_left h_deg <| Nat.zero_le _) le_rfl)
        <| Finset.le_sup (f := fun mm ↦ u * natDegree (p.coeff mm) + v * mm) <| by aesop)
    · exact Or.inr (le_trans (add_le_add (mul_le_mul_of_nonneg_left h_deg <| Nat.zero_le _) le_rfl)
        <| Finset.le_sup (f := fun mm ↦ u * natDegree (q.coeff mm) + v * mm) <| by aesop)
  all_goals simp_all only [not_not, add_zero, zero_add, not_false_eq_true]
  · exact Or.inl <| Finset.le_sup (f := fun mm ↦ u * natDegree (p.coeff mm) + v * mm) <| by aesop
  · exact Or.inr <| Finset.le_sup (f := fun mm ↦ u * natDegree (q.coeff mm) + v * mm) <| by aesop
  · simp at hm

lemma tri_natWeightedDegree_sum_le {ι : Type*} (s : Finset ι) (f : ι → S[X][Y]) (u v : ℕ) :
    natWeightedDegree (∑ i ∈ s, f i) u v ≤ s.sup (fun i ↦ natWeightedDegree (f i) u v) := by
  classical
  induction s using Finset.induction with
  | empty => simp only [Finset.sum_empty, Finset.sup_empty, Nat.bot_eq_zero, nonpos_iff_eq_zero,
      natWeightedDegree, Polynomial.support_zero, coeff_zero, natDegree_zero, mul_zero, zero_add,
      Finset.sup_empty, Nat.bot_eq_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sup_insert]
                        exact le_trans (tri_natWeightedDegree_add_le _ _ _ _) (max_le_max le_rfl ih)

end GenericTrivariateDegree

section BCIKS20ProximityGapSection5

variable {F : Type} [Field F] [DecidableEq F] [DecidableEq (RatFunc F)]
variable {n : ℕ}

section

open GuruswamiSudan Polynomial.Bivariate RatFunc Trivariate

/-- The degree bound (a.k.a. `D_X`) for instantiation of Guruswami-Sudan in Lemma 5.3 of [BCIKS20].
`D_X(m) = (m + 1/2)√rhon.` -/
noncomputable def D_X (rho : ℚ) (n m : ℕ) : ℝ := (m + 1/2) * (Real.sqrt rho) * n

omit [DecidableEq (RatFunc F)] in
/-- The first part of Lemma 5.3 from [BCIKS20].
Given `D_X` (`proximity_gap_degree_bound`) and `δ₀` (`proximity_gap_johnson`), a solution to
Guruswami-Sudan system exists. -/
lemma guruswami_sudan_for_proximity_gap_existence {k m : ℕ} {ωs : Fin n ↪ F} {f : Fin n → F}
    (hm : 1 ≤ m) :
    ∃ Q, Conditions (k + 1) m (_root_.proximity_gap_degree_bound (k + 1) n m) ωs f Q :=
    GuruswamiSudan.proximity_gap_existence (k + 1) n ωs f hm

omit [DecidableEq (RatFunc F)] in
open Polynomial in
/-- The second part of Lemma 5.3 from [BCIKS20].
For any solution `Q` of the Guruswami-Sudan system, and for any polynomial `P ∈ RS[n, k, rho]`
such that `δᵣ(w, P) ≤ δ₀(rho, m)`, we have that `Y - P(X)` divides `Q(X, Y)` in the polynomial ring
`F[X][Y]`. Note that in `F[X][Y]`, the term `X` actually refers to the outer variable, `Y`.
-/
lemma guruswami_sudan_for_proximity_gap_property {k m : ℕ} {ωs : Fin n ↪ F}
    {w : Fin n → F}
    {Q : F[X][Y]}
    (hk : k + 2 ≤ n) (hm : 1 ≤ m)
    (cond : Conditions (k + 1) m (_root_.proximity_gap_degree_bound (k + 1) n m) ωs w Q)
    {p : ReedSolomon.code ωs (k + 1)}
    (h : (↑Δ₀(w, fun i ↦ Polynomial.eval (ωs i) (ReedSolomon.codewordToPoly p)) : ℝ) / ↑n <
         _root_.proximity_gap_johnson (k + 1) n m)
    :
    (Polynomial.X - Polynomial.C (ReedSolomon.codewordToPoly p)) ∣ Q :=
  GuruswamiSudan.proximity_gap_divisibility hk hm p cond h

/-- The Guruswami-Sudan condition as it is stated in [BCIKS20]. -/
structure ModifiedGuruswami
  (m n k : ℕ)
  (ωs : Fin n ↪ F)
  (Q : F[Z][X][Y])
  (u₀ u₁ : Fin n → F)
  where
  Q_ne_0 : Q ≠ 0
  /-- Degree of the polynomial. -/
  Q_deg : natWeightedDegree Q 1 k < D_X ((k + 1) / (n : ℚ)) n m
  /-- Multiplicity of the roots is at least `m`. -/
  Q_multiplicity : ∀ i, rootMultiplicity Q
              (Polynomial.C <| ωs i)
              ((Polynomial.C <| u₀ i) + Polynomial.X * (Polynomial.C <| u₁ i))
            ≥ m
  /-- The X-degree bound. -/
  Q_deg_X :
    degreeX Q < D_X ((k + 1) / (n : ℚ)) n m
  /-- The Y-degree bound. -/
  Q_D_Y :
    D_Y Q < D_X ((k + 1 : ℚ) / n) n m / k
  /-- The YZ-degree bound. -/
  Q_D_YZ :
    D_YZ Q ≤ n * (m + 1/(2 : ℚ))^3 / (6 * Real.sqrt ((k + 1) / n))

section ModifiedGuruswamiHelpers

/-! ### Degree facts for the trivariate constant `1`

The constant polynomial `1 : F[Z][X][Y]` has all (bivariate-over-`F[Z]`) degree measures equal
to `0` and root multiplicity `0` at every curve point. These are the base facts used when
building/reasoning about candidate solutions `Q` of `ModifiedGuruswami` and, in particular, they
pin down the value of each `ModifiedGuruswami` constraint on the simplest nonzero witness. -/

omit [DecidableEq F] [DecidableEq (RatFunc F)] in
/-- The `X`-degree of the trivariate constant `1` is `0`. -/
lemma degreeX_one_triv : degreeX (1 : F[Z][X][Y]) = 0 := by
  unfold Polynomial.Bivariate.degreeX
  apply le_antisymm _ (Nat.zero_le _)
  apply Finset.sup_le
  intro i hi
  rw [Polynomial.mem_support_iff] at hi
  rcases eq_or_ne i 0 with h | h
  · subst h; simp
  · simp [Polynomial.coeff_one, h] at hi

omit [DecidableEq F] [DecidableEq (RatFunc F)] in
/-- The `Y`-degree of the trivariate constant `1` is `0`. -/
lemma natDegreeY_one_triv : natDegreeY (1 : F[Z][X][Y]) = 0 := by
  unfold Polynomial.Bivariate.natDegreeY
  simp

omit [DecidableEq F] [DecidableEq (RatFunc F)] in
/-- The `(u, v)`-weighted degree of the trivariate constant `1` is `0`. -/
lemma natWeightedDegree_one_triv (u v : ℕ) :
    natWeightedDegree (1 : F[Z][X][Y]) u v = 0 := by
  unfold Polynomial.Bivariate.natWeightedDegree
  apply le_antisymm _ (Nat.zero_le _)
  apply Finset.sup_le
  intro i hi
  rw [Polynomial.mem_support_iff] at hi
  rcases eq_or_ne i 0 with h | h
  · subst h; simp
  · simp [Polynomial.coeff_one, h] at hi

omit [DecidableEq (RatFunc F)] in
/-- The root multiplicity of the trivariate constant `1` at any point `(x, y)` is `0`.
Here the coefficient ring is `F[Z] = Polynomial (Polynomial F)`. -/
lemma rootMultiplicity_one_triv (x y : Polynomial F) :
    rootMultiplicity (1 : F[Z][X][Y]) x y = some 0 := by
  unfold Polynomial.Bivariate.rootMultiplicity
  rw [show Polynomial.Bivariate.shift (1 : F[Z][X][Y]) x y = 1 from by
    unfold Polynomial.Bivariate.shift; simp]
  unfold Polynomial.Bivariate.rootMultiplicity₀
  have hw : weightedDegree (1 : F[Z][X][Y]) 1 1 = some 0 := by
    unfold Polynomial.Bivariate.weightedDegree
    simp [Polynomial.natDegree_one]
  rw [hw]
  simp only [Nat.succ_eq_add_one, Nat.zero_add, List.range_one]
  have hp : ([0].product [0]) = [((0 : ℕ), (0 : ℕ))] := rfl
  rw [hp]
  simp only [List.filterMap_cons, List.filterMap_nil]
  have hc : coeff (1 : F[Z][X][Y]) 0 0 = 1 := by
    simp [Polynomial.Bivariate.coeff, Polynomial.coeff_one]
  rw [hc, if_neg one_ne_zero]
  simp

/-! ### Necessity of `0 < n` and `0 < k`

The statement of Claim 5.4 below quantifies over **all** `n, k, m`.  As formalized this is
**unsatisfiable** when `n = 0` or `k = 0`: the degree bound `D_X ρ n m` collapses to `0`, while
the `X`-degree (resp. `Y`-degree) of any polynomial is a natural number `≥ 0`, so the strict
constraints `degreeX Q < D_X …` (resp. `D_Y Q < D_X … / k`) cannot hold.

The two lemmas below record this precisely: any solution forces a contradiction.  Hence a faithful
restatement of Claim 5.4 must assume `0 < n` and `0 < k` (matching the non-degenerate Reed–Solomon
regime `k + 1 ≤ n` of [BCIKS20], and the `1 < k`, `n ≠ 0` hypotheses of the bivariate analogue
`GuruswamiSudan.gs_existence`). -/

omit [DecidableEq (RatFunc F)] in
/-- For `n = 0`, no `Q` can satisfy `ModifiedGuruswami`: the `X`-degree bound `D_X ρ 0 m = 0`
forces `(degreeX Q : ℝ) < 0`, which is impossible. -/
lemma modified_guruswami_unsat_of_n_zero {m k : ℕ} {ωs : Fin 0 ↪ F} {Q : F[Z][X][Y]}
    {u₀ u₁ : Fin 0 → F} (h : ModifiedGuruswami m 0 k ωs Q u₀ u₁) : False := by
  have hX := h.Q_deg_X
  unfold D_X at hX
  simp only [mul_zero, CharP.cast_eq_zero] at hX
  exact absurd hX (not_lt.mpr (Nat.cast_nonneg _))

omit [DecidableEq (RatFunc F)] in
/-- For `k = 0`, no `Q` can satisfy `ModifiedGuruswami`: the `Y`-degree bound `D_X ρ n m / 0 = 0`
forces `(D_Y Q : ℝ) < 0`, which is impossible. -/
lemma modified_guruswami_unsat_of_k_zero {m n : ℕ} {ωs : Fin n ↪ F} {Q : F[Z][X][Y]}
    {u₀ u₁ : Fin n → F} (h : ModifiedGuruswami m n 0 ωs Q u₀ u₁) : False := by
  have hY := h.Q_D_Y
  simp only [Nat.cast_zero, div_zero] at hY
  exact absurd hY (not_lt.mpr (Nat.cast_nonneg _))

/-! ### Trivariate monomial degree facts

The candidate solution `Q` of `ModifiedGuruswami` is assembled from the monomials `X^i Y^j Z^t`.
The lemmas below pin down each degree measure of a single such monomial, which is what controls
where a sum of monomials sits relative to the `ModifiedGuruswami` degree bounds. -/

/-- The trivariate monomial `X^i Y^j Z^t` as an element of `F[Z][X][Y]`. -/
noncomputable def triMonomial (i j t : ℕ) : F[Z][X][Y] :=
  Polynomial.monomial j (Polynomial.monomial i (Polynomial.monomial t (1 : F)))

omit [DecidableEq (RatFunc F)] in
/-- The trivariate monomial `X^i Y^j Z^t` is nonzero. -/
lemma triMonomial_ne_zero (i j t : ℕ) : triMonomial (F := F) i j t ≠ 0 := by
  unfold triMonomial; simp

omit [DecidableEq (RatFunc F)] in
/-- `degreeX (X^i Y^j Z^t) = i`. -/
lemma degreeX_triMonomial (i j t : ℕ) : degreeX (triMonomial (F := F) i j t) = i := by
  unfold degreeX triMonomial
  rw [Polynomial.support_monomial _
    (by simp : (Polynomial.monomial i (Polynomial.monomial t (1:F))) ≠ 0)]
  simp [Polynomial.coeff_monomial, Polynomial.natDegree_monomial]

omit [DecidableEq (RatFunc F)] in
/-- `natDegreeY (X^i Y^j Z^t) = j`. -/
lemma natDegreeY_triMonomial (i j t : ℕ) : natDegreeY (triMonomial (F := F) i j t) = j := by
  unfold natDegreeY triMonomial
  rw [Polynomial.natDegree_monomial]
  simp

omit [DecidableEq (RatFunc F)] in
/-- `natWeightedDegree (X^i Y^j Z^t) u v = u*i + v*j`. -/
lemma natWeightedDegree_triMonomial (i j t u v : ℕ) :
    natWeightedDegree (triMonomial (F := F) i j t) u v = u * i + v * j := by
  unfold natWeightedDegree triMonomial
  rw [Polynomial.support_monomial _
    (by simp : (Polynomial.monomial i (Polynomial.monomial t (1:F))) ≠ 0)]
  simp [Polynomial.coeff_monomial, Polynomial.natDegree_monomial]

omit [DecidableEq (RatFunc F)] in
/-- The `D_YZ` measure (as defined in `Trivariate.lean`) of a monomial `X^i Y^j Z^t` with `i ≠ j`
equals just the `Y`-degree index `j`.

This records a property of the *current* `D_YZ` definition: it computes
`max over j_Y of (j_Y + max over k_X of (Bivariate.coeff Q j_Y k_X).natDegree)`, and since
`Bivariate.coeff Q a b = (Q.coeff b).coeff a` (the first argument is the inner `X`-index), the
inner contribution vanishes for a single monomial unless `i = j`.  In particular the `Z`-degree
`t` is not captured, which makes the `Q_D_YZ` bound of `ModifiedGuruswami` easy to satisfy. -/
lemma D_YZ_triMonomial_of_ne (i j t : ℕ) (hij : i ≠ j) :
    D_YZ (triMonomial (F := F) i j t) = j := by
  unfold D_YZ triMonomial
  rw [Polynomial.support_monomial _
    (by simp : (Polynomial.monomial i (Polynomial.monomial t (1:F))) ≠ 0)]
  simp only [Finset.image_singleton, Finset.max_singleton]
  have hcj : (Polynomial.monomial j (Polynomial.monomial i (Polynomial.monomial t (1:F)))).coeff j
      = Polynomial.monomial i (Polynomial.monomial t (1:F)) := by
    rw [Polynomial.coeff_monomial, if_pos rfl]
  rw [hcj]
  rw [Polynomial.support_monomial _ (by simp : (Polynomial.monomial t (1:F)) ≠ 0)]
  simp only [Finset.image_singleton, Finset.max_singleton]
  unfold Polynomial.Bivariate.coeff
  rw [Polynomial.coeff_monomial, if_neg (Ne.symm hij)]
  simp [Polynomial.natDegree_zero]
  rfl

/-! ### Assembling a candidate from box-indexed coefficients

`triCoeffsToPoly box c` assembles `Q = ∑ c_{i,j,t} · X^i Y^j Z^t` over a finite index box of
triples `(i, j, t)`.  `natWeightedDegree_triCoeffsToPoly_le` bounds its `(u,v)`-weighted degree by
the box's weighted cap; specialising `(u,v)` recovers the `degreeX` and `natDegreeY` bounds via
`degreeX_as_weighted_deg` / `degreeY_as_weighted_deg`. -/

/-- `a · X^i Y^j Z^t` as nested monomials (carries the coefficient inside, avoiding the long
`SMul F (F[Z][X][Y])` synthesis path). -/
noncomputable def triMonC (i j t : ℕ) (a : F) : F[Z][X][Y] :=
  Polynomial.monomial j (Polynomial.monomial i (Polynomial.monomial t a))

omit [DecidableEq F] [DecidableEq (RatFunc F)] in
/-- The `(u,v)`-weighted degree of `a · X^i Y^j Z^t` is at most `u*i + v*j`. -/
lemma natWeightedDegree_triMonC_le (i j t u v : ℕ) (a : F) :
    natWeightedDegree (triMonC (F := F) i j t a) u v ≤ u * i + v * j := by
  classical
  unfold natWeightedDegree triMonC
  refine Finset.sup_le fun b hb ↦ ?_
  have hbj : b = j := by
    by_contra hbj
    rw [Polynomial.mem_support_iff, Polynomial.coeff_monomial, if_neg (Ne.symm hbj)] at hb
    exact hb rfl
  subst hbj
  rw [Polynomial.coeff_monomial, if_pos rfl]
  refine add_le_add (Nat.mul_le_mul_left u ?_) le_rfl
  exact Polynomial.natDegree_monomial_le _

/-- Assemble a trivariate polynomial from box-indexed coefficients. -/
noncomputable def triCoeffsToPoly (box : Finset (ℕ × ℕ × ℕ)) (c : box → F) : F[Z][X][Y] :=
  ∑ p : box, triMonC (F := F) p.1.1 p.1.2.1 p.1.2.2 (c p)

omit [DecidableEq F] [DecidableEq (RatFunc F)] in
/-- The weighted degree of the assembled polynomial is bounded by the box's weighted-degree cap. -/
lemma natWeightedDegree_triCoeffsToPoly_le (box : Finset (ℕ × ℕ × ℕ)) (c : box → F) (u v D : ℕ)
    (hbox : ∀ p ∈ box, u * p.1 + v * p.2.1 ≤ D) :
    natWeightedDegree (triCoeffsToPoly box c) u v ≤ D := by
  classical
  unfold triCoeffsToPoly
  refine le_trans (tri_natWeightedDegree_sum_le _ _ _ _) ?_
  refine Finset.sup_le fun p _ ↦ ?_
  exact le_trans (natWeightedDegree_triMonC_le _ _ _ _ _ _) (hbox p.1 p.2)

end ModifiedGuruswamiHelpers

omit [DecidableEq (RatFunc F)] in
/-- Claim 5.4 from [BCIKS20].
It essentially claims that there exists a solution to the Guruswami-Sudan constraints above.

NOTE: As currently formalized this lemma is **false** for `n = 0` or `k = 0` (see
`modified_guruswami_unsat_of_n_zero` / `modified_guruswami_unsat_of_k_zero`): the degree bound
`D_X` collapses to `0` and the strict degree constraints become unsatisfiable.  The statement
below therefore carries the proven-necessary side conditions `0 < n` and `0 < k` (the paper's
non-degenerate regime is `k + 1 ≤ n`, `1 ≤ m`; the eventual dimension-counting proof — the
trivariate analogue of `GuruswamiSudan.gs_existence` — may require strengthening to that full
regime). -/
lemma modified_guruswami_has_a_solution {m n k : ℕ} (hn : 0 < n) (hk : 0 < k)
    {ωs : Fin n ↪ F} {u₀ u₁ : Fin n → F} :
    ∃ Q : F[Z][X][Y], ModifiedGuruswami m n k ωs Q u₀ u₁ := by
  sorry

end

variable {m : ℕ} (k : ℕ) {δ : ℚ} {x₀ : F} {u₀ u₁ : Fin n → F} {Q : F[Z][X][Y]} {ωs : Fin n ↪ F}
         [Finite F]

noncomputable instance {α : Type} (s : Set α) [inst : Finite s] : Fintype s := Fintype.ofFinite _

/-- The set `S` (equation 5.2 of [BCIKS20]). -/
noncomputable def coeffs_of_close_proximity (ωs : Fin n ↪ F) (δ : ℚ) (u₀ u₁ : Fin n → F)
    : Finset F := Set.toFinset { z | ∃ v : ReedSolomon.code ωs (k + 1), δᵣ(u₀ + z • u₁, v) ≤ δ}

open Polynomial

omit [DecidableEq (RatFunc F)] in
/-- There exists a `δ`-close polynomial `P_z` for each `z` from the set `S`. -/
lemma exists_Pz_of_coeffs_of_close_proximity
    {k : ℕ}
  {z : F}
  (hS : z ∈ coeffs_of_close_proximity (k := k) ωs δ u₀ u₁)
    :
  ∃ Pz : F[X], Pz.natDegree ≤ k ∧ δᵣ(u₀ + z • u₁, Pz.eval ∘ ωs) ≤ δ := by
    unfold coeffs_of_close_proximity at hS
    obtain ⟨w, hS, dist⟩ : ∃ a ∈ ReedSolomon.code ωs (k + 1), ↑δᵣ(u₀ + z • u₁, a) ≤ δ := by
      simpa using hS
    obtain ⟨p, hS⟩ : ∃ y ∈ degreeLT F (k + 1), (ReedSolomon.evalOnPoints ωs) y = w := by
      simpa using hS
    exact ⟨p, ⟨
      by if h : p = 0
         then simp [h]
         else rw [mem_degreeLT, degree_eq_natDegree h, Nat.cast_lt] at hS; grind,
      by convert dist; rw [←hS.2]; rfl
    ⟩⟩

/-- The `δ`-close polynomial `Pz` for each `z` from the set `S` (`coeffs_of_close_proximity`). -/
noncomputable def Pz {k : ℕ} {z : F} (hS : z ∈ coeffs_of_close_proximity k ωs δ u₀ u₁) : F[X] :=
  (exists_Pz_of_coeffs_of_close_proximity (n := n) (k := k) hS).choose

open Trivariate
omit [DecidableEq (RatFunc F)] in
/-- Proposition 5.5 from [BCIKS20].
There exists a subset `S'` of the set `S` and a bivariate polynomial `P(X, Z)` that matches `Pz` on
that set. -/
lemma exists_a_set_and_a_matching_polynomial
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁) :
    ∃ S', ∃ (h_sub : S' ⊆ coeffs_of_close_proximity k ωs δ u₀ u₁), ∃ P : F[Z][X],
     #S' > #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (2 * D_Y Q) ∧
     ∀ z : S', Pz (h_sub z.2) = P.map (Polynomial.evalRingHom z.1) ∧
     P.natDegree ≤ k ∧
     Bivariate.degreeX P ≤ 1 := by
    sorry

/-- The subset `S'` extracted from Proprosition 5.5 [BCIKS20]. -/
noncomputable def matching_set (ωs : Fin n ↪ F) (δ : ℚ) (u₀ u₁ : Fin n → F)
  (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁) : Finset F :=
  (exists_a_set_and_a_matching_polynomial k h_gs (δ := δ)).choose

omit [DecidableEq (RatFunc F)] in
/-- `S'` is indeed a subset of `S` -/
lemma matching_set_is_a_sub_of_coeffs_of_close_proximity
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁) :
    matching_set k ωs δ u₀ u₁ h_gs ⊆ coeffs_of_close_proximity k ωs δ u₀ u₁ :=
  (exists_a_set_and_a_matching_polynomial k h_gs (δ := δ)).choose_spec.choose

end BCIKS20ProximityGapSection5

end ProximityGap

