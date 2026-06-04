/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import CompPoly.ToMathlib.Polynomial.BivariateDegree
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

/-!
# Interpolation ingredients for the [BCKHS25] route

Supporting lemmas for the low-`Z`-degree Berlekamp–Welch pair
([BCKHS25] Lemma 2.1) and the improved Guruswami–Sudan interpolant (§3):
this file currently provides the vanishing upgrade — a bivariate polynomial
whose `X`-degree is below the number of its `X`-vanishing points is zero —
which converts "the kernel solution is nontrivial" into "the error-locator
component is nonzero" in both constructions.
-/

namespace BCKHS25

-- Decidability/Fintype instances are threaded through the section; several
-- statement-level lemmas do not mention them directly.
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false

open Polynomial Polynomial.Bivariate

open Module

variable {F : Type*} [Field F] [DecidableEq F]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A bivariate polynomial of `X`-degree less than the number of points at
which its `X`-evaluation vanishes is zero (coefficient-wise root counting).
The `A ≠ 0` upgrade of [BCKHS25] Lemma 2.1 and the §3 interpolant both reduce
to this. -/
theorem eq_zero_of_degreeX_lt_card_of_evalX_eq_zero {f : F[X][Y]}
    {s : Finset F} (hdeg : degreeX f < s.card)
    (h : ∀ a ∈ s, evalX a f = 0) : f = 0 := by
  classical
  ext j : 1
  show f.coeff j = (0 : F[X][Y]).coeff j
  rw [Polynomial.coeff_zero]
  -- the j-th Y-coefficient vanishes at every point of s
  have hc : ∀ a ∈ s, (f.coeff j).eval a = 0 := by
    intro a ha
    have h0 := h a ha
    have hcoeff : (evalX a f).coeff j = (f.coeff j).eval a := by
      simp [evalX, Polynomial.coeff]
    rw [h0] at hcoeff
    simpa using hcoeff.symm
  by_cases hj : j ∈ f.support
  · have hdegj : (f.coeff j).natDegree < s.card :=
      lt_of_le_of_lt (Finset.le_sup (f := fun n => (f.coeff n).natDegree) hj) hdeg
    exact Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' (f.coeff j) s hc hdegj
  · exact Polynomial.notMem_support_iff.mp hj

/-- Abstract underdetermined-system existence: a linear map between
finite-dimensional spaces with strictly larger domain has a nonzero kernel
vector. -/
theorem exists_ne_zero_map_eq_zero {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [FiniteDimensional K V] [FiniteDimensional K W]
    (Φ : V →ₗ[K] W) (h : finrank K W < finrank K V) :
    ∃ v : V, v ≠ 0 ∧ Φ v = 0 := by
  have hk := LinearMap.ker_ne_bot_of_finrank_lt (f := Φ) h
  rcases Submodule.ne_bot_iff _ |>.mp hk with ⟨v, hvmem, hv0⟩
  exact ⟨v, hv0, hvmem⟩

/-- Unknown index type for the (A, B) coefficient vector: `A` has `X`-degree
`< da` and `Z`-degree `< za`; `B` has `X`-degree `< db` and `Z`-degree `< zb`. -/
abbrev BWIdx (da za db zb : ℕ) := (Fin da × Fin za) ⊕ (Fin db × Fin zb)

/-- The Berlekamp–Welch constraint matrix over the line word `u₀ + Z·u₁`: row
`(x, j)` is the `Z^j`-coefficient of `B(ω_x, Z) − (u₀ x + Z·u₁ x)·A(ω_x, Z)`. -/
def BWMatrix' (da za db zb : ℕ) (domain : ι ↪ F) (u₀ u₁ : ι → F) :
    Matrix (ι × Fin zb) (BWIdx da za db zb) F :=
  fun (xj : ι × Fin zb) idx =>
    match idx with
    | Sum.inl (i, j') =>
        -- −(u₀ x · a_{i,j} + u₁ x · a_{i,j−1}) contribution
        (if (j' : ℕ) = (xj.2 : ℕ) then -(u₀ xj.1) * (domain xj.1) ^ (i : ℕ) else 0) +
        (if (j' : ℕ) + 1 = (xj.2 : ℕ) then -(u₁ xj.1) * (domain xj.1) ^ (i : ℕ) else 0)
    | Sum.inr (i, j') =>
        if (j' : ℕ) = (xj.2 : ℕ) then (domain xj.1) ^ (i : ℕ) else 0

/-- The dimension count: with `zb = za + 1` (B one Z-degree higher) and
`da·za + db·(za+1) > n·(za+1)`, the constraint system has a nontrivial
solution. -/
theorem exists_ne_zero_BWvec (da za db zb : ℕ) (_hzb : zb = za + 1)
    (domain : ι ↪ F) (u₀ u₁ : ι → F)
    (hcount : Fintype.card ι * zb < da * za + db * zb) :
    ∃ v : BWIdx da za db zb → F, v ≠ 0 ∧
      Matrix.mulVec (BWMatrix' da za db zb domain u₀ u₁) v = 0 := by
  classical
  have hfr : finrank F ((ι × Fin zb) → F) < finrank F (BWIdx da za db zb → F) := by
    simp only [Module.finrank_pi, Fintype.card_prod, Fintype.card_sum, Fintype.card_fin]
    simpa using hcount
  obtain ⟨v, hv0, hker⟩ := exists_ne_zero_map_eq_zero
    (Matrix.mulVecLin (BWMatrix' da za db zb domain u₀ u₁)) hfr
  exact ⟨v, hv0, by simpa [Matrix.mulVecLin_apply] using hker⟩

/-- Package the `A`-block of a coefficient vector as a bivariate polynomial. -/
noncomputable def toPolyA {da za db zb : ℕ} (v : BWIdx da za db zb → F) : F[X][Y] :=
  ∑ j : Fin za, Polynomial.monomial (j : ℕ)
    (∑ i : Fin da, Polynomial.C (v (Sum.inl (i, j))) * Polynomial.X ^ (i : ℕ))

/-- Package the `B`-block of a coefficient vector as a bivariate polynomial. -/
noncomputable def toPolyB {da za db zb : ℕ} (v : BWIdx da za db zb → F) : F[X][Y] :=
  ∑ j : Fin zb, Polynomial.monomial (j : ℕ)
    (∑ i : Fin db, Polynomial.C (v (Sum.inr (i, j))) * Polynomial.X ^ (i : ℕ))

/-- The `Y`-coefficients of the packaged polynomial, evaluated in `X`: inside
the index range it is the coefficient-weighted power sum; beyond it, zero. -/
lemma coeff_evalX_toPolyB {da za db zb : ℕ} (v : BWIdx da za db zb → F)
    (a : F) (j : ℕ) :
    (evalX a (toPolyB v)).coeff j
      = if h : j < zb then ∑ i : Fin db, v (Sum.inr (i, ⟨j, h⟩)) * a ^ (i : ℕ) else 0 := by
  classical
  have hcoeff : (toPolyB v).coeff j
      = if h : j < zb then
          (∑ i : Fin db, Polynomial.C (v (Sum.inr (i, ⟨j, h⟩))) * Polynomial.X ^ (i : ℕ))
        else 0 := by
    simp only [toPolyB, Polynomial.finset_sum_coeff, Polynomial.coeff_monomial]
    by_cases h : j < zb
    · rw [dif_pos h, Finset.sum_eq_single (⟨j, h⟩ : Fin zb)]
      · simp
      · intro b _ hb
        have hne : ((j : ℕ) : ℕ) ≠ ((b : Fin _) : ℕ) := fun heq => hb (Fin.ext heq.symm)
        simp [hne.symm]
      · intro habs
        exact absurd (Finset.mem_univ _) habs
    · rw [dif_neg h]
      refine Finset.sum_eq_zero fun b _ => ?_
      have hne : (j : ℕ) ≠ ((b : Fin _) : ℕ) := fun heq => h (heq ▸ b.isLt)
      simp [hne.symm]
  have : (evalX a (toPolyB v)).coeff j = ((toPolyB v).coeff j).eval a := by
    simp [evalX, Polynomial.coeff]
  rw [this, hcoeff]
  by_cases h : j < zb
  · rw [dif_pos h, dif_pos h]
    simp [Polynomial.eval_finset_sum]
  · rw [dif_neg h, dif_neg h]
    simp

/-- Same for the `A`-block. -/
lemma coeff_evalX_toPolyA {da za db zb : ℕ} (v : BWIdx da za db zb → F)
    (a : F) (j : ℕ) :
    (evalX a (toPolyA v)).coeff j
      = if h : j < za then ∑ i : Fin da, v (Sum.inl (i, ⟨j, h⟩)) * a ^ (i : ℕ) else 0 := by
  classical
  have hcoeff : (toPolyA v).coeff j
      = if h : j < za then
          (∑ i : Fin da, Polynomial.C (v (Sum.inl (i, ⟨j, h⟩))) * Polynomial.X ^ (i : ℕ))
        else 0 := by
    simp only [toPolyA, Polynomial.finset_sum_coeff, Polynomial.coeff_monomial]
    by_cases h : j < za
    · rw [dif_pos h, Finset.sum_eq_single (⟨j, h⟩ : Fin za)]
      · simp
      · intro b _ hb
        have hne : ((j : ℕ) : ℕ) ≠ ((b : Fin _) : ℕ) := fun heq => hb (Fin.ext heq.symm)
        simp [hne.symm]
      · intro habs
        exact absurd (Finset.mem_univ _) habs
    · rw [dif_neg h]
      refine Finset.sum_eq_zero fun b _ => ?_
      have hne : (j : ℕ) ≠ ((b : Fin _) : ℕ) := fun heq => h (heq ▸ b.isLt)
      simp [hne.symm]
  have : (evalX a (toPolyA v)).coeff j = ((toPolyA v).coeff j).eval a := by
    simp [evalX, Polynomial.coeff]
  rw [this, hcoeff]
  by_cases h : j < za
  · rw [dif_pos h, dif_pos h]
    simp [Polynomial.eval_finset_sum]
  · rw [dif_neg h, dif_neg h]
    simp

/-- Coefficient recovery: the packaged polynomials are injective images of the
coefficient vector. -/
private lemma coeff_coeff_toPolyA {da za db zb : ℕ} (v : BWIdx da za db zb → F)
    (i : Fin da) (j : Fin za) :
    ((toPolyA v).coeff (j : ℕ)).coeff (i : ℕ) = v (Sum.inl (i, j)) := by
  classical
  -- compute the Y-coefficient, then its X-coefficient
  have hYcoeff : (toPolyA v).coeff (j : ℕ)
      = ∑ i' : Fin da, Polynomial.C (v (Sum.inl (i', j))) * Polynomial.X ^ (i' : ℕ) := by
    simp only [toPolyA, Polynomial.finset_sum_coeff, Polynomial.coeff_monomial]
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      have hne : ((j : Fin za) : ℕ) ≠ ((b : Fin za) : ℕ) := fun heq => hb (Fin.ext heq.symm)
      simp [hne.symm]
    · intro habs
      exact absurd (Finset.mem_univ _) habs
  rw [hYcoeff, Polynomial.finset_sum_coeff]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    have hne : ((i : Fin da) : ℕ) ≠ ((b : Fin da) : ℕ) := fun heq => hb (Fin.ext heq.symm)
    simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hne]
  · intro habs
    exact absurd (Finset.mem_univ _) habs

private lemma coeff_coeff_toPolyB {da za db zb : ℕ} (v : BWIdx da za db zb → F)
    (i : Fin db) (j : Fin zb) :
    ((toPolyB v).coeff (j : ℕ)).coeff (i : ℕ) = v (Sum.inr (i, j)) := by
  classical
  have hYcoeff : (toPolyB v).coeff (j : ℕ)
      = ∑ i' : Fin db, Polynomial.C (v (Sum.inr (i', j))) * Polynomial.X ^ (i' : ℕ) := by
    simp only [toPolyB, Polynomial.finset_sum_coeff, Polynomial.coeff_monomial]
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      have hne : ((j : Fin zb) : ℕ) ≠ ((b : Fin zb) : ℕ) := fun heq => hb (Fin.ext heq.symm)
      simp [hne.symm]
    · intro habs
      exact absurd (Finset.mem_univ _) habs
  rw [hYcoeff, Polynomial.finset_sum_coeff]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    have hne : ((i : Fin db) : ℕ) ≠ ((b : Fin db) : ℕ) := fun heq => hb (Fin.ext heq.symm)
    simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hne]
  · intro habs
    exact absurd (Finset.mem_univ _) habs

/-- The kernel rows are exactly the Y-coefficients of the Berlekamp–Welch
identity: if `mulVec (BWMatrix' …) v = 0` then at every domain point
`B(ω_x, Y) = (u₀ x + u₁ x · Y) · A(ω_x, Y)`. -/
private lemma identity_of_mulVec_eq_zero {da za db zb : ℕ} (hzb : zb = za + 1)
    (domain : ι ↪ F) (u₀ u₁ : ι → F) (v : BWIdx da za db zb → F)
    (hker : Matrix.mulVec (BWMatrix' da za db zb domain u₀ u₁) v = 0) (x : ι) :
    evalX (domain x) (toPolyB v)
      = (Polynomial.C (u₀ x) + Polynomial.C (u₁ x) * Polynomial.X)
          * evalX (domain x) (toPolyA v) := by
  classical
  ext j : 1
  -- RHS coefficient: u₀·a_j + u₁·a_{j−1}
  have hrhs : ((Polynomial.C (u₀ x) + Polynomial.C (u₁ x) * Polynomial.X)
      * evalX (domain x) (toPolyA v)).coeff j
      = u₀ x * (evalX (domain x) (toPolyA v)).coeff j
        + u₁ x * (if j = 0 then 0 else (evalX (domain x) (toPolyA v)).coeff (j - 1)) := by
    rw [add_mul, Polynomial.coeff_add, Polynomial.coeff_C_mul]
    congr 1
    rw [mul_assoc, mul_comm Polynomial.X, ← mul_assoc]
    cases j with
    | zero => simp
    | succ j' =>
        rw [Polynomial.coeff_mul_X]
        simp [Polynomial.coeff_C_mul]
  -- the kernel row at (x, j) for j < zb; trivial beyond
  rw [hrhs]
  simp only [coeff_evalX_toPolyB, coeff_evalX_toPolyA]
  by_cases hj : j < zb
  · rw [dif_pos hj]
    -- expand the vanishing kernel row
    have hrow := congrFun hker (x, ⟨j, hj⟩)
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at hrow
    rw [Fintype.sum_sum_type] at hrow
    -- collapse the A-block double sum
    have hAblock : (∑ p : Fin da × Fin za,
        BWMatrix' da za db zb domain u₀ u₁ (x, ⟨j, hj⟩) (Sum.inl p) * v (Sum.inl p))
        = -(u₀ x) * (if h : j < za then
              ∑ i : Fin da, v (Sum.inl (i, ⟨j, h⟩)) * (domain x) ^ (i : ℕ) else 0)
          + -(u₁ x) * (if h : j - 1 < za ∧ 1 ≤ j then
              ∑ i : Fin da, v (Sum.inl (i, ⟨j - 1, h.1⟩)) * (domain x) ^ (i : ℕ) else 0) := by
      rw [Fintype.sum_prod_type]
      simp only [BWMatrix', add_mul, Finset.sum_add_distrib]
      congr 1
      · -- the u₀-part: collapse j' = j
        by_cases h : j < za
        · rw [dif_pos h, Finset.mul_sum]
          rw [Finset.sum_comm]
          rw [Finset.sum_eq_single (⟨j, h⟩ : Fin za)]
          · refine Finset.sum_congr rfl fun i _ => ?_
            simp [mul_comm, mul_left_comm]
          · intro b _ hb
            have hne : ((b : Fin za) : ℕ) ≠ j := fun heq => hb (Fin.ext heq)
            refine Finset.sum_eq_zero fun i _ => ?_
            simp [hne]
          · intro habs
            exact absurd (Finset.mem_univ _) habs
        · rw [dif_neg h, mul_zero]
          refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun b _ => ?_
          have hne : ((b : Fin za) : ℕ) ≠ j := fun heq => h (heq ▸ b.isLt)
          simp [hne]
      · -- the u₁-part: collapse j' + 1 = j
        by_cases h : j - 1 < za ∧ 1 ≤ j
        · rw [dif_pos h, Finset.mul_sum]
          rw [Finset.sum_comm]
          rw [Finset.sum_eq_single (⟨j - 1, h.1⟩ : Fin za)]
          · refine Finset.sum_congr rfl fun i _ => ?_
            have hcond : (j - 1) + 1 = j := Nat.succ_pred_eq_of_pos h.2
            simp [hcond, mul_comm, mul_left_comm]
          · intro b _ hb
            have hne : ¬(((b : Fin za) : ℕ) + 1 = j) := by
              intro heq
              apply hb
              apply Fin.ext
              change ((b : Fin za) : ℕ) = j - 1
              omega
            refine Finset.sum_eq_zero fun i _ => ?_
            simp [hne]
          · intro habs
            exact absurd (Finset.mem_univ _) habs
        · rw [dif_neg h, mul_zero]
          refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun b _ => ?_
          have hblt : ((b : Fin za) : ℕ) < za := b.isLt
          have hne : ¬(((b : Fin za) : ℕ) + 1 = j) := by
            intro heq
            exact h ⟨by omega, by omega⟩
          simp [hne]
    -- collapse the B-block double sum
    have hBblock : (∑ p : Fin db × Fin zb,
        BWMatrix' da za db zb domain u₀ u₁ (x, ⟨j, hj⟩) (Sum.inr p) * v (Sum.inr p))
        = ∑ i : Fin db, v (Sum.inr (i, ⟨j, hj⟩)) * (domain x) ^ (i : ℕ) := by
      rw [Fintype.sum_prod_type]
      simp only [BWMatrix']
      rw [Finset.sum_comm]
      rw [Finset.sum_eq_single (⟨j, hj⟩ : Fin zb)]
      · refine Finset.sum_congr rfl fun i _ => ?_
        simp [mul_comm]
      · intro b _ hb
        have hne : ((b : Fin zb) : ℕ) ≠ j := fun heq => hb (Fin.ext heq)
        refine Finset.sum_eq_zero fun i _ => ?_
        simp [hne]
      · intro habs
        exact absurd (Finset.mem_univ _) habs
    rw [hAblock, hBblock] at hrow
    -- rearrange: B-sum = u₀·A_j + u₁·A_{j−1}
    by_cases hza : j < za
    · by_cases hj1 : j - 1 < za ∧ 1 ≤ j
      · rw [dif_pos hza, dif_pos hj1] at hrow
        rw [dif_pos hza]
        have hj0 : ¬(j = 0) := by omega
        rw [if_neg hj0, dif_pos hj1.1]
        linear_combination hrow
      · -- j = 0 (since j < za ≤ ... and ¬(j−1<za ∧ 1≤j) with j<za means ¬1≤j)
        have hj0 : j = 0 := by omega
        rw [dif_pos hza, dif_neg hj1] at hrow
        rw [dif_pos hza, if_pos hj0]
        linear_combination hrow
    · -- j ≥ za: A_j term vanishes; j−1 may still be < za (j = za case)
      rw [dif_neg hza] at hrow
      rw [dif_neg hza]
      by_cases hj1 : j - 1 < za ∧ 1 ≤ j
      · rw [dif_pos hj1] at hrow
        have hj0 : ¬(j = 0) := by omega
        rw [if_neg hj0, dif_pos hj1.1]
        linear_combination hrow
      · rw [dif_neg hj1] at hrow
        by_cases hj0 : j = 0
        · rw [if_pos hj0]
          linear_combination hrow
        · rw [if_neg hj0]
          have : ¬(j - 1 < za) := by omega
          rw [dif_neg this]
          linear_combination hrow
  · -- j ≥ zb: everything vanishes
    rw [dif_neg hj]
    have hza : ¬(j < za) := by omega
    rw [dif_neg hza]
    have hj0 : ¬(j = 0) := by omega
    rw [if_neg hj0]
    have hj1 : ¬(j - 1 < za) := by omega
    rw [dif_neg hj1]
    ring

end BCKHS25
