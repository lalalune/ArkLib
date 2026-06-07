/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AlphaWeightDivisibility
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2MatchProof

/-!
# BCIKS20 Appendix A.4 (P1) — monic reduction of the weight invariant to the successor core (#138)

This file lands the **monic-`H` reduction** of the BCIKS20 Appendix A.4 weight invariant
`AlphaGenuineRegularWeightLe` (#138), the P1 analogue of the now-proven monic P2 match
`restrictedFaaDiBrunoMatch_of_monic` (#139).

For monic `H` (`H.leadingCoeff = 1`, the WLOG case of the minimal-polynomial reduction) three of the
four inputs to the assembly lemma `AlphaGenuineRegularWeightLe.of_normalized_divWeight_cases_succLift`
are already discharged, **axiom-clean**:

* the successor **lift identity** `hliftSucc` is `(P2_closed_of_leadingCoeff_one …).2` at order `t+1`
  (proven via the monic P2 match);
* the **base** `h0` (`βHensel 0 = a · W𝒪` with `Λ_𝒪`-weight `≤ 1`) is `βHensel_zero_weight_le_one`
  together with the monic collapse `W𝒪 = 1` (`AlphaWeight.W𝒪_eq_one_of_monic`);
* the `W`-factor of the successor clearing product collapses (`W𝒪 ^ (t+2) = 1`).

Hence the *entire* monic invariant follows from a single remaining obligation: the **successor
divisibility-with-weight core** `SuccDivWeightLe_of_monic` — at every order, `βHensel (t+1)` is
`ξ^{2t+1}`-divisible in `𝒪 H` with a quotient of `Λ_𝒪`-weight `≤ 1`. This is exactly the irreducible
BCIKS20 Newton ξ-order-gain / `Λ(α_t) = 1` regularity claim; it is carried here as an explicit
hypothesis, never an `axiom` or `sorry`. The reduction pins the open #138 obligation (in the monic
case) to this single core, the same way `P2_closed_of_leadingCoeff_one` pinned #139.
-/

open Polynomial Polynomial.Bivariate
open BCIKS20AppendixA
open ProximityPrize.BCIKS20.GammaGenuine

namespace BCIKS20.HenselNumerator.AlphaWeight

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
variable {D : ℕ}

/-- **The monic successor divisibility-with-weight obligation — the irreducible #138 core.**
For monic `H` the clearing product collapses to `ξ^{2t+1}`, so the only open content of the
successor divisibility-with-weight is: each `βHensel (t+1)` is `ξ^{2t+1}`-divisible in `𝒪 H` with a
quotient of `Λ_𝒪`-weight `≤ 1`. This is the BCIKS20 Newton ξ-order-gain / weight-1 regularity core;
it is genuinely open (the same weight-`≤-1` wall flagged in `AlphaWeight.lean`). -/
def SuccDivWeightLe_of_monic (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (D : ℕ) : Prop :=
  ∀ t : ℕ, ∃ a : 𝒪 H,
    βHensel H x₀ R hHyp (t + 1) = a * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * t + 1)
      ∧ weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1

/-- **Monic reduction of the full A.4 weight invariant (#138) to its successor core.**
For monic `H`, the order-0 invariant, the `W𝒪 = 1` collapse, and the successor lift identity
(`P2_closed_of_leadingCoeff_one`, axiom-clean) are all discharged, so the full
`AlphaGenuineRegularWeightLe` follows from *only* `SuccDivWeightLe_of_monic`. This is the P1 analogue
of the proven monic P2 match: it reduces the remaining #138 obligation in the monic (WLOG) case to
exactly the BCIKS20 Newton ξ-order-gain / weight-1 regularity core, with no `axiom`, no `sorry`. -/
theorem AlphaGenuineRegularWeightLe_of_monic_of_succDivWeight
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (hmonic : H.Monic) (hd : 2 ≤ H.natDegree) (hD : D ≤ H.natDegree)
    (hsucc : SuccDivWeightLe_of_monic H x₀ R hHyp hH D) :
    AlphaGenuineRegularWeightLe H x₀ R hHyp hH D := by
  have hlc : H.leadingCoeff = 1 := hmonic
  refine AlphaGenuineRegularWeightLe.of_normalized_divWeight_cases_succLift
    H x₀ R hHyp hH D (fun t => ?_) ?_ (fun t => ?_)
  · exact (BCIKS20.HenselNumerator.P2_closed_of_leadingCoeff_one H x₀ R hHyp hlc).2 (t + 1)
  · refine ⟨βHensel H x₀ R hHyp 0, ?_, βHensel_zero_weight_le_one H x₀ R hHyp hH hd hD⟩
    rw [W𝒪_eq_one_of_monic H hmonic, mul_one]
  · obtain ⟨a, ha, hwt⟩ := hsucc t
    refine ⟨a, ?_, hwt⟩
    rw [W𝒪_eq_one_of_monic H hmonic, one_pow, mul_one]
    exact ha

end BCIKS20.HenselNumerator.AlphaWeight

/-! ## Source audit -/
#print axioms
  BCIKS20.HenselNumerator.AlphaWeight.AlphaGenuineRegularWeightLe_of_monic_of_succDivWeight
