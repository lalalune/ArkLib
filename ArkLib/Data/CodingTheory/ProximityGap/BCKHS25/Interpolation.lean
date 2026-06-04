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

end BCKHS25
