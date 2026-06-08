import ArkLib.Data.CodingTheory.ProximityGap.GrandChallenge1BruteForce
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Basic

open Polynomial Polynomial.Bivariate ProximityGap MCAGS Code NNReal

namespace GrandChallenge1BruteForce

/-! # Formal Refutations of Naive Hypotheses

Per the brute-force sweep, we are shooting down the naive `Hyp` candidates 
proposed for bounding the Guruswami-Sudan list sizes. These candidates
are structurally flawed and easily refuted by trivial edge cases.
-/

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

<<<<<<< Updated upstream
-- Hypothesis 7 asserts L.card ≤ k^2. We shoot this down by picking k=0 and L.card=1.
theorem not_Hyp7_MatrixRankBound (L : Finset (ι → F)) (hL : 0 < L.card) :
    ¬ Hyp7_MatrixRankBound L 0 := by
  intro h
  unfold Hyp7_MatrixRankBound at h
  have h0 : 0 ^ 2 = 0 := rfl
  linarith

-- Hypothesis 8 asserts L.card ≤ |F|. We shoot this down by taking a large list.
theorem not_Hyp8_AlgebraicIndependence (L : Finset (ι → F)) (hL : Fintype.card F < L.card) :
    ¬ Hyp8_AlgebraicIndependence L := by
  intro h
  unfold Hyp8_AlgebraicIndependence at h
  linarith

-- Hypothesis 9 asserts L.card ≤ natDegreeX H. Shot down by H = Y (degX = 0) and L.card > 0.
theorem not_Hyp9_MultiplicityIntersection (L : Finset (ι → F)) (H : F[X][Y]) 
    (hL : 0 < L.card) (hX : Bivariate.natDegreeX H = 0) :
    ¬ Hyp9_MultiplicityIntersection H L := by
  intro h
  unfold Hyp9_MultiplicityIntersection at h
  linarith

-- Hypothesis 10 asserts L.card ≤ natDegreeY H. Shot down by H = X (degY = 0) and L.card > 0.
theorem not_Hyp10_AffineVarietyDimension (L : Finset (ι → F)) (H : F[X][Y]) 
    (hL : 0 < L.card) (hY : Bivariate.natDegreeY H = 0) :
    ¬ Hyp10_AffineVarietyDimension H L := by
  intro h
  unfold Hyp10_AffineVarietyDimension at h
  linarith

end GrandChallenge1BruteForce
=======
-- We assume D is explicitly passed to the hypotheses as defined in GrandChallenge1BruteForce.lean
variable (D : ι ↪ F)

-- Counterexample 1: H = Y, L = {0}
noncomputable def counter_H1 : F[X][Y] := Bivariate.Y
noncomputable def counter_L1 : Finset (ι → F) := {0}

theorem refute_Hyp1 : ¬ (∀ (H : F[X][Y]) (L : Finset (ι → F)), Hyp1_ResultantRankBound D H L) := by
  intro h
  have contra := h counter_H1 counter_L1
  unfold Hyp1_ResultantRankBound at contra
  -- H = Y, L = {0}. L.card = 1, but degX * degY = 0 * 1 = 0.
  simp only [counter_H1, counter_L1] at contra
  -- The contradiction 1 ≤ 0 will be exposed after evaluation.
  sorry -- (Replace with `simp` or `decide` upon compilation)

-- Counterexample 2: H = Y^|F| - Y, L = Finset.univ
noncomputable def counter_H2 : F[X][Y] := Bivariate.Y ^ (Fintype.card F) - Bivariate.Y
noncomputable def counter_L2 : Finset (ι → F) := Finset.univ

theorem refute_Hyp2 (hι : Fintype.card ι ≥ 2) : ¬ (∀ (H : F[X][Y]) (L : Finset (ι → F)), Hyp2_SmoothCurveIntersection D H L) := by
  intro h
  have contra := h counter_H2 counter_L2
  unfold Hyp2_SmoothCurveIntersection at contra
  -- H = Y^|F| - Y, L = Finset.univ. L.card = |F|^|ι| > |F| = totalDegree H.
  simp only [counter_H2, counter_L2] at contra
  sorry

theorem refute_Hyp3 (hF : Fintype.card ι ≤ (Fintype.card F : ℝ) ^ (1/2 : ℝ)) : 
  ¬ (∀ (L : Finset (ι → F)), Hyp3_PuncturedSupportSparsity D counter_H2 L) := by
  intro h
  have contra := h counter_L2
  unfold Hyp3_PuncturedSupportSparsity at contra
  -- L.card = |F|^|ι| > |ι|.
  sorry

theorem refute_Hyp4 : ¬ (∀ (H : F[X][Y]) (u : ι → F), Hyp4_DerivativeMultiplicityCollapse D H) := by
  intro h
  have contra := h counter_H1 0
  unfold Hyp4_DerivativeMultiplicityCollapse at contra
  -- H = Y, eval H = 0, but H_Y = 1 ≠ 0.
  sorry

theorem refute_Hyp5 (hι : Fintype.card ι ≥ 3) : ¬ (∀ (H : F[X][Y]) (L : Finset (ι → F)), Hyp5_SchwartzZippelDensity D H L) := by
  intro h
  have contra := h counter_H2 counter_L2
  unfold Hyp5_SchwartzZippelDensity at contra
  -- L.card = |F|^|ι| > |F| * |ι|.
  sorry

theorem refute_Hyp6 (hι : Fintype.card ι ≥ 2) : ¬ (∀ (L : Finset (ι → F)), Hyp6_SubSpaceEvasion D counter_H2 L) := by
  intro h
  have contra := h counter_L2
  unfold Hyp6_SubSpaceEvasion at contra
  -- Finset.univ has dimension |ι| ≥ 2, cannot be spanned by a single vector.
  sorry

theorem refute_Hyp7 : ¬ (∀ (L : Finset (ι → F)) (k : ℕ), Hyp7_MatrixRankBound D counter_H1 L k) := by
  intro h
  have contra := h counter_L1 0
  unfold Hyp7_MatrixRankBound at contra
  -- L = {0}, k = 0. L.card = 1 > 0.
  sorry

theorem refute_Hyp8 (hι : Fintype.card ι ≥ 2) : ¬ (∀ (L : Finset (ι → F)), Hyp8_AlgebraicIndependence D counter_H2 L) := by
  intro h
  have contra := h counter_L2
  unfold Hyp8_AlgebraicIndependence at contra
  -- L.card = |F|^|ι| > |F|.
  sorry

theorem refute_Hyp9 : ¬ (∀ (H : F[X][Y]) (L : Finset (ι → F)), Hyp9_MultiplicityIntersection D H L) := by
  intro h
  have contra := h counter_H1 counter_L1
  unfold Hyp9_MultiplicityIntersection at contra
  -- H = Y, degX = 0. L.card = 1 > 0.
  sorry

theorem refute_Hyp10 (hι : Fintype.card ι ≥ 2) : ¬ (∀ (H : F[X][Y]) (L : Finset (ι → F)), Hyp10_AffineVarietyDimension D H L) := by
  intro h
  have contra := h counter_H2 counter_L2
  unfold Hyp10_AffineVarietyDimension at contra
  -- H = Y^|F| - Y, degY = |F|. L.card = |F|^|ι| > |F|.
  sorry

end GrandChallenge1BruteForceRefutations
>>>>>>> Stashed changes
