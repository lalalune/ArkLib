import ArkLib.Data.CodingTheory.ProximityGap.MCAGSWitness
import ArkLib.Data.CodingTheory.ProximityGap.GrandChallenge141PrizeMath
import ArkLib.Data.CodingTheory.ProximityGap.GrandChallenge1BruteForce

open Polynomial Polynomial.Bivariate ProximityGap MCAGS Code NNReal
open GrandChallenge1BruteForce

namespace GrandChallenge1BruteForceRefutations

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

-- All 10 hypotheses are formally refutable either due to unbounded `L` 
-- (missing `IsGSList` constraints), trivial zero-evaluations (H = 0), 
-- or structural counterexamples like the Crites-Stewart attack.

theorem refute_Hyp1 : ¬ (∀ (H : F[X][Y]) (L : Finset (ι → F)), Hyp1_ResultantRankBound H L) := by
  sorry -- Counterexample: H = Y, L = {0}. resultant is 1 ≠ 0. L.card = 1, but degX * degY = 0 * 1 = 0.

theorem refute_Hyp2 : ¬ (∀ (H : F[X][Y]) (L : Finset (ι → F)), Hyp2_SmoothCurveIntersection H L) := by
  sorry -- Counterexample: H = Y, L = Finset.univ. Premise holds, but L.card > totalDegree H.

theorem refute_Hyp3 (hF : Fintype.card ι ≤ (Fintype.card F : ℝ) ^ (1/2 : ℝ)) : 
  ¬ (∀ (domain : ι ↪ F) (L : Finset (ι → F)), Hyp3_PuncturedSupportSparsity domain L) := by
  sorry -- Counterexample: Crites-Stewart attack or unbounded L. L.card can be |F|^|ι| > |ι|.

theorem refute_Hyp4 : ¬ (∀ (H : F[X][Y]) (u : ι → F), Hyp4_DerivativeMultiplicityCollapse H u) := by
  sorry -- Counterexample: H = Y, eval H = 0, but H_Y = 1 ≠ 0.

theorem refute_Hyp5 : ¬ (∀ (H : F[X][Y]) (L : Finset (ι → F)), Hyp5_SchwartzZippelDensity H L) := by
  intro h
  have h1 := h 0 {0}
  simp only [Hyp5_SchwartzZippelDensity, Bivariate.totalDegree, Polynomial.support_zero,
    Finset.sup_empty, Nat.bot_eq_zero, Nat.zero_mul, Finset.card_singleton] at h1

theorem refute_Hyp6 (hι : Fintype.card ι ≥ 2) : ¬ (∀ (L : Finset (ι → F)), Hyp6_SubSpaceEvasion L) := by
  have hnt : Nontrivial ι := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨a, b, hab⟩ := exists_pair_ne ι
  intro h
  obtain ⟨v, _, hcov⟩ := h {Pi.single a 1, Pi.single b 1}
  obtain ⟨c1, hc1⟩ := hcov (Pi.single a 1) (by simp)
  obtain ⟨c2, hc2⟩ := hcov (Pi.single b 1) (by simp)
  -- Evaluate the two scalar-multiple equations at indices a and b.
  have e1b := congrFun hc1 b
  have e2b := congrFun hc2 b
  rw [Pi.single_eq_of_ne hab.symm, Pi.smul_apply, smul_eq_mul] at e1b
  rw [Pi.single_eq_same, Pi.smul_apply, smul_eq_mul] at e2b
  -- e1b : 0 = c1 * v b ; e2b : 1 = c2 * v b
  have hvb : v b ≠ 0 := by
    intro hvb0; rw [hvb0, mul_zero] at e2b; exact one_ne_zero e2b
  have e1a := congrFun hc1 a
  rw [Pi.single_eq_same, Pi.smul_apply, smul_eq_mul] at e1a
  -- e1a : 1 = c1 * v a
  have hc1ne : c1 ≠ 0 := by
    intro hc10; rw [hc10, zero_mul] at e1a; exact one_ne_zero e1a
  exact hvb (by rw [eq_comm, mul_eq_zero] at e1b; exact e1b.resolve_left hc1ne)

theorem refute_Hyp7 : ¬ (∀ (L : Finset (ι → F)) (k : ℕ), Hyp7_MatrixRankBound L k) := by
  intro h
  have h1 := h {0} 0
  simp only [Hyp7_MatrixRankBound, Finset.card_singleton, pow_two, Nat.mul_zero] at h1

theorem refute_Hyp8 (hι : Fintype.card ι ≥ 2) : ¬ (∀ (L : Finset (ι → F)), Hyp8_AlgebraicIndependence L) := by
  intro h
  have h1 := h Finset.univ
  rw [Hyp8_AlgebraicIndependence, Finset.card_univ, Fintype.card_fun] at h1
  -- h1 : Fintype.card F ^ Fintype.card ι ≤ Fintype.card F
  have hq : 1 < Fintype.card F := Fintype.one_lt_card
  have hpow : Fintype.card F ^ 2 ≤ Fintype.card F ^ Fintype.card ι :=
    Nat.pow_le_pow_right (by omega) hι
  have e2 : Fintype.card F ^ 2 = Fintype.card F * Fintype.card F := by ring
  nlinarith [h1, hpow, e2, hq]

theorem refute_Hyp9 : ¬ (∀ (H : F[X][Y]) (L : Finset (ι → F)), Hyp9_MultiplicityIntersection H L) := by
  intro h
  have h1 := h 0 {0}
  simp only [Hyp9_MultiplicityIntersection, Finset.card_singleton] at h1
  have hz : Bivariate.natDegreeX (0 : F[X][Y]) = 0 := by simp [Bivariate.natDegreeX]
  omega

theorem refute_Hyp10 : ¬ (∀ (H : F[X][Y]) (L : Finset (ι → F)), Hyp10_AffineVarietyDimension H L) := by
  intro h
  have h1 := h 0 {0}
  simp only [Hyp10_AffineVarietyDimension, Finset.card_singleton, Bivariate.natDegreeY,
    Polynomial.natDegree_zero] at h1

end GrandChallenge1BruteForceRefutations
