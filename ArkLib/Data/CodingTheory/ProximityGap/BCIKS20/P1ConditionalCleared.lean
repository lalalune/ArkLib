/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P1Conditional
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AlphaWeightCleared

/-!
# Corrected cleared-base conditional P1 unlock wrappers

Compatibility wrappers connecting the repaired cleared-base #138 predicates to the existing
`P1Conditional` endpoint surface.  The direct div-weight wrappers are lift-free.  The alpha-side
wrappers use only successor-order lift identities, and the `fullVanishes` / `restrictedMatch`
wrappers obtain those successor identities from the existing P2 closed endpoints.

These declarations do not prove the remaining successor witnesses, `RestrictedFaaDiBrunoMatch`, or
full P1 from first principles; they keep downstream consumers off the known-false un-cleared
order-zero predicate.
-/

noncomputable section
set_option linter.style.longLine false

namespace BCIKS20.HenselNumerator

open Polynomial Polynomial.Bivariate
open BCIKS20AppendixA
open ProximityPrize.BCIKS20.GammaGenuine
open AlphaWeight

section P1ConditionalCleared

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- Prefix structured invariant from the repaired cleared-base div-weight cases, exposed from the
P1 conditional namespace with the `ξ` side condition discharged. -/
theorem βHenselStructuredWeightInvariant_unlocked_of_divWeight_clearedBaseCases
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdiv : DivWeightLe_clearedBaseCases H x₀ R hHyp hH D) (k : ℕ) :
    βHenselStructuredWeightInvariant (D := D) H x₀ R hHyp hH k :=
  AlphaWeight.βHenselStructuredWeightInvariant_of_divWeight_clearedBaseCases'
    H x₀ R hHyp hH hDH hDRx0 hdR2 hdiv k

/-- Prefix structured invariant from repaired alpha-side cleared-base cases and successor-order
lift identities, exposed from the P1 conditional namespace with `ξ` discharged. -/
theorem βHenselStructuredWeightInvariant_unlocked_of_alphaWeight_clearedBaseCases_succLift
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hliftSucc : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp (t + 1))
        = αGenuine H x₀ R hHyp (t + 1)
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1 + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * (t + 1) - 1))
    (hα : AlphaGenuineRegularWeightLe_clearedBaseCases H x₀ R hHyp hH D) (k : ℕ) :
    βHenselStructuredWeightInvariant (D := D) H x₀ R hHyp hH k :=
  AlphaWeight.βHenselStructuredWeightInvariant_of_alphaWeight_clearedBaseCases_succLift'
    H x₀ R hHyp hH hDH hDRx0 hdR2 hliftSucc hα k

/-- Prefix structured invariant unlocked by full P2 vanishing and repaired alpha-side
cleared-base cases. -/
theorem βHenselStructuredWeightInvariant_unlocked_of_fullVanishes_clearedBaseCases
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hvan : FaaDiBrunoFullSumVanishes H x₀ R hHyp)
    (hα : AlphaGenuineRegularWeightLe_clearedBaseCases H x₀ R hHyp hH D) (k : ℕ) :
    βHenselStructuredWeightInvariant (D := D) H x₀ R hHyp hH k :=
  βHenselStructuredWeightInvariant_unlocked_of_alphaWeight_clearedBaseCases_succLift
    H x₀ R hHyp hH hDH hDRx0 hdR2
    (fun t => (P2_closed_of_fullVanishes H x₀ R hHyp hvan).2 (t + 1)) hα k

/-- Prefix structured invariant unlocked by the restricted P2 match and repaired alpha-side
cleared-base cases. -/
theorem βHenselStructuredWeightInvariant_unlocked_of_restrictedMatch_clearedBaseCases
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hmatch : RestrictedFaaDiBrunoMatch H x₀ R hHyp)
    (hα : AlphaGenuineRegularWeightLe_clearedBaseCases H x₀ R hHyp hH D) (k : ℕ) :
    βHenselStructuredWeightInvariant (D := D) H x₀ R hHyp hH k :=
  βHenselStructuredWeightInvariant_unlocked_of_alphaWeight_clearedBaseCases_succLift
    H x₀ R hHyp hH hDH hDRx0 hdR2
    (fun t => (P2_closed_of_restrictedMatch H x₀ R hHyp hmatch).2 (t + 1)) hα k

/-- P1 weight bound unlocked directly from repaired cleared-base div-weight cases. -/
theorem βHensel_weight_bound_unlocked_of_divWeight_clearedBaseCases
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hdiv : DivWeightLe_clearedBaseCases H x₀ R hHyp hH D) (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  AlphaWeight.βHensel_weight_bound_of_divWeight_clearedBaseCases'
    H x₀ R hHyp hH hDH hDRx0 hdR2 hdHR hW hdiv t

/-- P1 weight bound from repaired alpha-side cleared-base cases and successor-order lift
identities, with `ξ` discharged. -/
theorem βHensel_weight_bound_unlocked_of_alphaWeight_clearedBaseCases_succLift
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hliftSucc : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp (t + 1))
        = αGenuine H x₀ R hHyp (t + 1)
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1 + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * (t + 1) - 1))
    (hα : AlphaGenuineRegularWeightLe_clearedBaseCases H x₀ R hHyp hH D) (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  AlphaWeight.βHensel_weight_bound_of_alphaWeight_clearedBaseCases_succLift'
    H x₀ R hHyp hH hDH hDRx0 hdR2 hdHR hW hliftSucc hα t

/-- P1 weight bound unlocked by full P2 vanishing and repaired alpha-side cleared-base cases. -/
theorem βHensel_weight_bound_unlocked_of_fullVanishes_clearedBaseCases
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hvan : FaaDiBrunoFullSumVanishes H x₀ R hHyp)
    (hα : AlphaGenuineRegularWeightLe_clearedBaseCases H x₀ R hHyp hH D) (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_unlocked_of_alphaWeight_clearedBaseCases_succLift
    H x₀ R hHyp hH hDH hDRx0 hdR2 hdHR hW
    (fun t => (P2_closed_of_fullVanishes H x₀ R hHyp hvan).2 (t + 1)) hα t

/-- P1 weight bound unlocked by the restricted P2 match and repaired alpha-side cleared-base
cases. -/
theorem βHensel_weight_bound_unlocked_of_restrictedMatch_clearedBaseCases
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hmatch : RestrictedFaaDiBrunoMatch H x₀ R hHyp)
    (hα : AlphaGenuineRegularWeightLe_clearedBaseCases H x₀ R hHyp hH D) (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_unlocked_of_alphaWeight_clearedBaseCases_succLift
    H x₀ R hHyp hH hDH hDRx0 hdR2 hdHR hW
    (fun t => (P2_closed_of_restrictedMatch H x₀ R hHyp hmatch).2 (t + 1)) hα t

end P1ConditionalCleared

end BCIKS20.HenselNumerator

-- Axiom audit: every new wrapper stays on the inherited standard axiom surface.
#print axioms BCIKS20.HenselNumerator.βHenselStructuredWeightInvariant_unlocked_of_divWeight_clearedBaseCases
#print axioms BCIKS20.HenselNumerator.βHenselStructuredWeightInvariant_unlocked_of_alphaWeight_clearedBaseCases_succLift
#print axioms BCIKS20.HenselNumerator.βHenselStructuredWeightInvariant_unlocked_of_fullVanishes_clearedBaseCases
#print axioms BCIKS20.HenselNumerator.βHenselStructuredWeightInvariant_unlocked_of_restrictedMatch_clearedBaseCases
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_unlocked_of_divWeight_clearedBaseCases
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_unlocked_of_alphaWeight_clearedBaseCases_succLift
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_unlocked_of_fullVanishes_clearedBaseCases
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_unlocked_of_restrictedMatch_clearedBaseCases
