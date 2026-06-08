/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AlphaWeight

/-!
# BCIKS20 Appendix A.4 (P1) — weight-bound obstruction for unconstrained lift direction (#138)

This file tests the remaining `Λ_𝒪 ≤ 1` part of `AlphaGenuineRegularWeightLe` against the current
two-field `ClaimA2.Hypotheses`.  The simple family below has valid specialized polynomial
`R(x₀, Y) = Y`, but its first lift-direction Hasse coefficient is `X^2`; this is the missing
low-degree/grading constraint showing up at order `1`.
-/

open Polynomial Polynomial.Bivariate BCIKS20AppendixA ProximityPrize.BCIKS20.GammaGenuine

namespace BCIKS20.HenselNumerator

variable {F : Type} [Field F]

noncomputable section

/-- The unconstrained first lift-direction coefficient used by the counterexample family. -/
def badLiftCoeff (x₀ : F) : F[X][X] :=
  ((Polynomial.X : F[X][X]) - Polynomial.C (Polynomial.C x₀)) *
    Polynomial.C ((Polynomial.X : F[X]) ^ 2)

/-- A valid `ClaimA2.Hypotheses` input whose first lift-direction coefficient has `X`-degree `2`.
Specializing the middle variable at `x₀` kills the added term, so `R(x₀, Y) = Y`. -/
def badR (x₀ : F) : F[X][X][Y] :=
  (Polynomial.X : F[X][X][Y]) + Polynomial.C (badLiftCoeff x₀)

lemma evalX_badR (x₀ : F) :
    Bivariate.evalX (Polynomial.C x₀) (badR x₀) = (Polynomial.X : F[X][Y]) := by
  simp [badR, badLiftCoeff, Bivariate.evalX_eq_map]

lemma badR_hypotheses (x₀ : F) :
    ClaimA2.Hypotheses x₀ (badR x₀) (Polynomial.X : F[X][Y]) := by
  constructor
  · simp [evalX_badR]
  · simpa [evalX_badR] using (Polynomial.separable_X (R := F[X]))

lemma badH_natDegree : (Polynomial.X : F[X][Y]).natDegree = 1 := by
  rw [Polynomial.natDegree_X]

lemma badH_natDegree_pos : 0 < (Polynomial.X : F[X][Y]).natDegree := by
  rw [badH_natDegree]
  norm_num

instance badH_fact_irreducible : Fact (Irreducible (Polynomial.X : F[X][Y])) :=
  ⟨Polynomial.irreducible_X⟩

instance badH_fact_natDegree_pos : Fact (0 < (Polynomial.X : F[X][Y]).natDegree) :=
  ⟨badH_natDegree_pos⟩

lemma derivative_badLiftCoeff (x₀ : F) :
    Polynomial.derivative (badLiftCoeff x₀) = Polynomial.C ((Polynomial.X : F[X]) ^ 2) := by
  rw [badLiftCoeff, Polynomial.derivative_mul, Polynomial.derivative_sub,
    Polynomial.derivative_X, Polynomial.derivative_C, sub_zero, Polynomial.derivative_C,
    mul_zero, add_zero, one_mul]

lemma evalX_hasseDerivX_badR_one_zero (x₀ : F) :
    Bivariate.evalX (Polynomial.C x₀)
        (hasseDerivX 1 (hasseDerivY 0 (badR x₀)))
      = Polynomial.C ((Polynomial.X : F[X]) ^ 2) := by
  rw [hasseDerivY_zero, badR, hasseDerivX_add]
  have hY : hasseDerivX 1 (Polynomial.X : F[X][X][Y]) = 0 := by
    unfold hasseDerivX
    simp
  have hC : hasseDerivX 1 (Polynomial.C (badLiftCoeff x₀) : F[X][X][Y])
      = Polynomial.C (Polynomial.C ((Polynomial.X : F[X]) ^ 2)) := by
    unfold hasseDerivX
    simp [derivative_badLiftCoeff]
  rw [hY, hC, zero_add]
  simp [Bivariate.evalX_eq_map]

lemma evalX_hasseDerivX_badR_one (x₀ : F) :
    Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 (badR x₀))
      = Polynomial.C ((Polynomial.X : F[X]) ^ 2) := by
  simpa using evalX_hasseDerivX_badR_one_zero (F := F) x₀

lemma hasseCoeffRepr𝒪_badR_one_zero (x₀ : F) :
    hasseCoeffRepr𝒪 (Polynomial.X : F[X][Y]) x₀ (badR x₀) 1 0 =
      Ideal.Quotient.mk (Ideal.span {H_tilde' (Polynomial.X : F[X][Y])})
        (Polynomial.C ((Polynomial.X : F[X]) ^ 2)) := by
  simp [hasseCoeffRepr𝒪, evalX_hasseDerivX_badR_one]

end

end BCIKS20.HenselNumerator
