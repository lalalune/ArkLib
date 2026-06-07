/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P1ConditionalAll
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P1ConditionalCleared

/-!
# Cleared all-prefix structured-endpoint P1 wrappers

This companion keeps the corrected cleared-base conditional route wired into the older
all-prefix structured-invariant endpoint from `P1ConditionalAll.lean`, without growing that
near-cap file.  The declarations here are endpoint packaging: the repaired cleared-base
div/alpha case splits and the P2 unlock hypotheses remain explicit.
-/

noncomputable section
set_option linter.style.longLine false

namespace BCIKS20.HenselNumerator

open Polynomial Polynomial.Bivariate
open BCIKS20AppendixA
open ProximityPrize.BCIKS20.GammaGenuine
open AlphaWeight

section P1ConditionalAllCleared

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-! ## Single-order structured-endpoint wrappers -/

/-- Route the repaired cleared-base div-weight all-prefix invariant through the
structured-invariant P1 endpoint. -/
theorem βHensel_weight_bound_of_structured_invariant_unlocked_of_divWeight_clearedBaseCases
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hRgraded : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdiv : DivWeightLe_clearedBaseCases H x₀ R hHyp hH D) (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_of_structured_invariant H x₀ R hHyp hH hDH hdR2
    hdHR hW hRgraded hDRx0
      (βHenselStructuredWeightInvariant_all_unlocked_of_divWeight_clearedBaseCases
        H x₀ R hHyp hH hDH hDRx0 hdR2 hdiv)
      t

/-- Route repaired alpha-side cleared-base cases through the all-prefix structured endpoint,
using only successor-order lift identities. -/
theorem βHensel_weight_bound_of_structured_invariant_unlocked_of_alphaWeight_clearedBaseCases_succLift
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hRgraded : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hliftSucc : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp (t + 1))
        = αGenuine H x₀ R hHyp (t + 1)
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1 + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * (t + 1) - 1))
    (hα : AlphaGenuineRegularWeightLe_clearedBaseCases H x₀ R hHyp hH D) (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_of_structured_invariant H x₀ R hHyp hH hDH hdR2
    hdHR hW hRgraded hDRx0
      (βHenselStructuredWeightInvariant_all_unlocked_of_alphaWeight_clearedBaseCases_succLift
        H x₀ R hHyp hH hDH hDRx0 hdR2 hliftSucc hα)
      t

/-- Route the full-vanishing cleared-base conditional all-prefix invariant through the
structured-invariant P1 endpoint. -/
theorem βHensel_weight_bound_of_structured_invariant_unlocked_of_fullVanishes_clearedBaseCases
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hRgraded : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hvan : FaaDiBrunoFullSumVanishes H x₀ R hHyp)
    (hα : AlphaGenuineRegularWeightLe_clearedBaseCases H x₀ R hHyp hH D) (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_of_structured_invariant H x₀ R hHyp hH hDH hdR2
    hdHR hW hRgraded hDRx0
      (βHenselStructuredWeightInvariant_all_unlocked_of_fullVanishes_clearedBaseCases
        H x₀ R hHyp hH hDH hDRx0 hdR2 hvan hα)
      t

/-- Route the restricted-match cleared-base conditional all-prefix invariant through the
structured-invariant P1 endpoint. -/
theorem βHensel_weight_bound_of_structured_invariant_unlocked_of_restrictedMatch_clearedBaseCases
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hRgraded : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hmatch : RestrictedFaaDiBrunoMatch H x₀ R hHyp)
    (hα : AlphaGenuineRegularWeightLe_clearedBaseCases H x₀ R hHyp hH D) (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_of_structured_invariant H x₀ R hHyp hH hDH hdR2
    hdHR hW hRgraded hDRx0
      (βHenselStructuredWeightInvariant_all_unlocked_of_restrictedMatch_clearedBaseCases
        H x₀ R hHyp hH hDH hDRx0 hdR2 hmatch hα)
      t

/-! ## All-order structured-endpoint wrappers -/

/-- All-`t` P1 weight bound from repaired cleared-base div-weight cases through the
structured-invariant endpoint. -/
theorem βHensel_weight_bound_all_of_structured_invariant_unlocked_of_divWeight_clearedBaseCases
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hRgraded : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdiv : DivWeightLe_clearedBaseCases H x₀ R hHyp hH D) :
    ∀ t, weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  fun t =>
    βHensel_weight_bound_of_structured_invariant_unlocked_of_divWeight_clearedBaseCases
      H x₀ R hHyp hH hDH hdR2 hdHR hW hRgraded hDRx0 hdiv t

/-- All-`t` P1 weight bound from repaired alpha-side cleared-base cases through the
structured-invariant endpoint, using only successor-order lift identities. -/
theorem βHensel_weight_bound_all_of_structured_invariant_unlocked_of_alphaWeight_clearedBaseCases_succLift
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hRgraded : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hliftSucc : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp (t + 1))
        = αGenuine H x₀ R hHyp (t + 1)
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1 + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * (t + 1) - 1))
    (hα : AlphaGenuineRegularWeightLe_clearedBaseCases H x₀ R hHyp hH D) :
    ∀ t, weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  fun t =>
    βHensel_weight_bound_of_structured_invariant_unlocked_of_alphaWeight_clearedBaseCases_succLift
      H x₀ R hHyp hH hDH hdR2 hdHR hW hRgraded hDRx0 hliftSucc hα t

/-- All-`t` P1 weight bound from full P2 vanishing and repaired alpha-side cleared-base cases
through the structured-invariant endpoint. -/
theorem βHensel_weight_bound_all_of_structured_invariant_unlocked_of_fullVanishes_clearedBaseCases
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hRgraded : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hvan : FaaDiBrunoFullSumVanishes H x₀ R hHyp)
    (hα : AlphaGenuineRegularWeightLe_clearedBaseCases H x₀ R hHyp hH D) :
    ∀ t, weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  fun t =>
    βHensel_weight_bound_of_structured_invariant_unlocked_of_fullVanishes_clearedBaseCases
      H x₀ R hHyp hH hDH hdR2 hdHR hW hRgraded hDRx0 hvan hα t

/-- All-`t` P1 weight bound from restricted P2 match and repaired alpha-side cleared-base cases
through the structured-invariant endpoint. -/
theorem βHensel_weight_bound_all_of_structured_invariant_unlocked_of_restrictedMatch_clearedBaseCases
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hRgraded : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hmatch : RestrictedFaaDiBrunoMatch H x₀ R hHyp)
    (hα : AlphaGenuineRegularWeightLe_clearedBaseCases H x₀ R hHyp hH D) :
    ∀ t, weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  fun t =>
    βHensel_weight_bound_of_structured_invariant_unlocked_of_restrictedMatch_clearedBaseCases
      H x₀ R hHyp hH hDH hdR2 hdHR hW hRgraded hDRx0 hmatch hα t

end P1ConditionalAllCleared

end BCIKS20.HenselNumerator

-- Axiom audit: the new endpoint wrappers stay on the inherited standard axiom surface.
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_of_structured_invariant_unlocked_of_divWeight_clearedBaseCases
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_of_structured_invariant_unlocked_of_alphaWeight_clearedBaseCases_succLift
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_of_structured_invariant_unlocked_of_fullVanishes_clearedBaseCases
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_of_structured_invariant_unlocked_of_restrictedMatch_clearedBaseCases
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_all_of_structured_invariant_unlocked_of_divWeight_clearedBaseCases
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_all_of_structured_invariant_unlocked_of_alphaWeight_clearedBaseCases_succLift
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_all_of_structured_invariant_unlocked_of_fullVanishes_clearedBaseCases
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_all_of_structured_invariant_unlocked_of_restrictedMatch_clearedBaseCases
