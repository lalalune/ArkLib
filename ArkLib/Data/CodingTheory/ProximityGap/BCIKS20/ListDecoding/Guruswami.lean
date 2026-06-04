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
