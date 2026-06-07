/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2Close
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2Assembly
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2Reabsorb
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.UnclearedEmbedding

/-!
# Quantitative extraction / base-case API for the carved P2 core (BCIKS20 A.4, issue #139)

Infrastructure around `RestrictedFaaDiBrunoMatch` — the #139 analogue of #138's clearing-product
divisibility/quotient API. Every consequence lemma takes the (unproven) combinatorial core
`RestrictedFaaDiBrunoMatchAt` only as an explicit hypothesis (using just the proven `ζ ≠ 0`),
exactly as the in-tree P2 consequence theorems do — none assumes the STEP-8 core.

* `coeff_succ_βHenselAssembled_eq_of_restrictedMatchAt` / `restrictedMatchAt_of_…` /
  `restrictedMatchAt_iff_coeff_succ_βHenselAssembled_eq` — the carved core at order `t` is *exactly*
  the normalized-quotient coefficient equation `coeff (t+1) βHenselAssembled = −rFdBSum t / ζ`.
* `coeff_succ_βHenselAssembled_eq_of_restrictedMatch` — the all-orders consumer.
* `restrictedFaaDiBrunoSum_zero_eq_powerSum` — the `t = 0` base case of the raw STEP-1 defect sum.
* `embeddingCleared_eq_Wpow_mul_uncleared_of_target` — makes the cleared/un-cleared `eval₂` mismatch
  *quantitative*: under the STEP-8 target, the two `𝒪`-reps differ by exactly `W^{natDegreeY p}`.
-/

noncomputable section

open scoped BigOperators
open Finset
open Polynomial Polynomial.Bivariate
open ArkLib.PowerSeriesComposition
open BCIKS20AppendixA
open ProximityPrize.BCIKS20.GammaGenuine

namespace BCIKS20.HenselNumerator

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- **Quantitative coefficient extraction from the carved P2 core (consequence, axiom-clean).**
Given `RestrictedFaaDiBrunoMatchAt t` and the genuine separability non-vanishing `ζ ≠ 0`, the
`(t+1)` coefficient of `βHenselAssembled` is `−restrictedFaaDiBrunoSum t / ζ`.
#139 analogue of #138's `divWeight_quotient_unique`: the unproven combinatorial core is taken
only as a hypothesis. -/
theorem coeff_succ_βHenselAssembled_eq_of_restrictedMatchAt (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ)
    (hmatch : RestrictedFaaDiBrunoMatchAt H x₀ R hHyp t) :
    PowerSeries.coeff (t + 1) (βHenselAssembled H x₀ R hHyp)
      = -restrictedFaaDiBrunoSum H x₀ R hHyp t / ClaimA2.ζ R x₀ H := by
  unfold RestrictedFaaDiBrunoMatchAt at hmatch
  rw [hmatch, neg_neg, mul_comm, mul_div_assoc, div_self (ζ_ne_zero H x₀ R hHyp), mul_one]

/-- **Converse of the quantitative extraction (axiom-clean).** The explicit coefficient equation
implies the carved single-order core `RestrictedFaaDiBrunoMatchAt t` (again only using `ζ ≠ 0`). -/
theorem restrictedMatchAt_of_coeff_succ_βHenselAssembled_eq (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ)
    (hcoeff : PowerSeries.coeff (t + 1) (βHenselAssembled H x₀ R hHyp)
      = -restrictedFaaDiBrunoSum H x₀ R hHyp t / ClaimA2.ζ R x₀ H) :
    RestrictedFaaDiBrunoMatchAt H x₀ R hHyp t := by
  unfold RestrictedFaaDiBrunoMatchAt
  rw [hcoeff, mul_div_assoc', mul_comm (ClaimA2.ζ R x₀ H),
    mul_div_assoc, div_self (ζ_ne_zero H x₀ R hHyp), mul_one, neg_neg]

/-- **The carved core at order `t` is exactly the normalized-quotient coefficient equation.** -/
theorem restrictedMatchAt_iff_coeff_succ_βHenselAssembled_eq (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ) :
    RestrictedFaaDiBrunoMatchAt H x₀ R hHyp t ↔
      PowerSeries.coeff (t + 1) (βHenselAssembled H x₀ R hHyp)
        = -restrictedFaaDiBrunoSum H x₀ R hHyp t / ClaimA2.ζ R x₀ H :=
  ⟨coeff_succ_βHenselAssembled_eq_of_restrictedMatchAt H x₀ R hHyp t,
    restrictedMatchAt_of_coeff_succ_βHenselAssembled_eq H x₀ R hHyp t⟩

/-- **All-orders quantitative coefficient extraction (axiom-clean).** From the full carved core
`RestrictedFaaDiBrunoMatch`, every successor coefficient of the assembled numerator series is the
normalized quotient `−restrictedFaaDiBrunoSum t / ζ`. -/
theorem coeff_succ_βHenselAssembled_eq_of_restrictedMatch (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hmatch : RestrictedFaaDiBrunoMatch H x₀ R hHyp) (t : ℕ) :
    PowerSeries.coeff (t + 1) (βHenselAssembled H x₀ R hHyp)
      = -restrictedFaaDiBrunoSum H x₀ R hHyp t / ClaimA2.ζ R x₀ H :=
  coeff_succ_βHenselAssembled_eq_of_restrictedMatchAt H x₀ R hHyp t (hmatch t)

/-- **Order-zero base case of the raw restricted Faà-di-Bruno sum (axiom-clean).** The un-normalized
STEP-1 defect sum collapses at `t = 0` to the single surviving Taylor power-sum over the `Y`-degree
of `Q` — the raw sibling of `restrictedFaaDiBrunoPartitionForm_zero_eq_powerSum`. -/
theorem restrictedFaaDiBrunoSum_zero_eq_powerSum (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) :
    restrictedFaaDiBrunoSum H x₀ R hHyp 0 =
      ∑ i ∈ Finset.range ((Q x₀ R H).natDegree + 1),
        (liftToFunctionField (H := H)
            ((Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 R)).coeff i))
        * (PowerSeries.coeff 0 (βHenselAssembled H x₀ R hHyp)) ^ i := by
  rw [restrictedFaaDiBrunoSum_eq_restrictedPartitionForm H x₀ R hHyp 0,
    restrictedFaaDiBrunoPartitionForm_zero_eq_powerSum H x₀ R hHyp]

/-- **Order-zero raw sum after reabsorbing the surviving power-sum (axiom-clean).** The raw
restricted Faà-di-Bruno sum at `t = 0` is exactly the cleared root evaluation
`hasseEvalAtRoot ... 1 0`. -/
theorem restrictedFaaDiBrunoSum_zero_eq_hasseEvalAtRoot (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) :
    restrictedFaaDiBrunoSum H x₀ R hHyp 0 = hasseEvalAtRoot H x₀ R 1 0 := by
  rw [restrictedFaaDiBrunoSum_zero_eq_powerSum H x₀ R hHyp,
    ← restrictedFaaDiBrunoPartitionZeroPowerSum_eq_hasseEvalAtRoot H x₀ R hHyp]
  rfl

/-- **Order-zero quantitative coefficient extraction (axiom-clean).** The carved P2 core at
order zero gives the base successor coefficient equation directly in terms of `hasseEvalAtRoot`. -/
theorem coeff_one_βHenselAssembled_eq_of_restrictedMatchAt_zero
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hmatch : RestrictedFaaDiBrunoMatchAt H x₀ R hHyp 0) :
    PowerSeries.coeff 1 (βHenselAssembled H x₀ R hHyp)
      = -hasseEvalAtRoot H x₀ R 1 0 / ClaimA2.ζ R x₀ H := by
  simpa [restrictedFaaDiBrunoSum_zero_eq_hasseEvalAtRoot H x₀ R hHyp] using
    coeff_succ_βHenselAssembled_eq_of_restrictedMatchAt H x₀ R hHyp 0 hmatch

/-- **Converse order-zero quantitative extraction (axiom-clean).** The base coefficient equation
with the reabsorbed LHS `hasseEvalAtRoot` implies the carved order-zero core. -/
theorem restrictedMatchAt_zero_of_coeff_one_βHenselAssembled_eq
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hcoeff :
      PowerSeries.coeff 1 (βHenselAssembled H x₀ R hHyp)
        = -hasseEvalAtRoot H x₀ R 1 0 / ClaimA2.ζ R x₀ H) :
    RestrictedFaaDiBrunoMatchAt H x₀ R hHyp 0 := by
  apply restrictedMatchAt_of_coeff_succ_βHenselAssembled_eq H x₀ R hHyp 0
  simpa [restrictedFaaDiBrunoSum_zero_eq_hasseEvalAtRoot H x₀ R hHyp] using hcoeff

/-- **Order-zero carved core iff the reabsorbed base coefficient equation.** -/
theorem restrictedMatchAt_zero_iff_coeff_one_βHenselAssembled_eq
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) :
    RestrictedFaaDiBrunoMatchAt H x₀ R hHyp 0 ↔
      PowerSeries.coeff 1 (βHenselAssembled H x₀ R hHyp)
        = -hasseEvalAtRoot H x₀ R 1 0 / ClaimA2.ζ R x₀ H :=
  ⟨coeff_one_βHenselAssembled_eq_of_restrictedMatchAt_zero H x₀ R hHyp,
    restrictedMatchAt_zero_of_coeff_one_βHenselAssembled_eq H x₀ R hHyp⟩

/-- **The cleared `𝒪`-rep embedding is `W^{natDegreeY p}` times the un-cleared rep embedding, GIVEN
the STEP-8 target (axiom-clean).** Makes the cleared/un-cleared `eval₂` mismatch *quantitative*:
under the carved STEP-8 match `HasseCoeffRepr𝒪UnclearedEval₂Target`, the two `𝒪`-reps are related by
exactly the `m = |λ|`-dependent factor `W^{natDegreeY p}` named in the #139 obstruction analysis. -/
theorem embeddingCleared_eq_Wpow_mul_uncleared_of_target (x₀ : F) (R : F[X][X][Y]) (i1 m : ℕ)
    (htarget : HasseCoeffRepr𝒪UnclearedEval₂Target H x₀ R i1 m) :
    embeddingOf𝒪Into𝕃 H
        (Ideal.Quotient.mk (Ideal.span {H_tilde' H}) (hasseCoeffRepr𝒪_cleared H x₀ R i1 m) : 𝒪 H)
      = liftToFunctionField (H := H) H.leadingCoeff
            ^ Bivariate.natDegreeY
                (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX i1 (hasseDerivY m R)))
          * embeddingOf𝒪Into𝕃 H (hasseCoeffRepr𝒪 H x₀ R i1 m) := by
  rw [embeddingOf𝒪Into𝕃_hasseCoeffRepr𝒪_cleared,
    (HasseCoeffRepr𝒪UnclearedMatchesRoot.of_eval₂Target H x₀ R i1 m htarget)]

end BCIKS20.HenselNumerator

#print axioms BCIKS20.HenselNumerator.coeff_succ_βHenselAssembled_eq_of_restrictedMatchAt
#print axioms BCIKS20.HenselNumerator.restrictedMatchAt_iff_coeff_succ_βHenselAssembled_eq
#print axioms BCIKS20.HenselNumerator.restrictedFaaDiBrunoSum_zero_eq_powerSum
#print axioms BCIKS20.HenselNumerator.restrictedFaaDiBrunoSum_zero_eq_hasseEvalAtRoot
#print axioms BCIKS20.HenselNumerator.coeff_one_βHenselAssembled_eq_of_restrictedMatchAt_zero
#print axioms BCIKS20.HenselNumerator.restrictedMatchAt_zero_iff_coeff_one_βHenselAssembled_eq
#print axioms BCIKS20.HenselNumerator.embeddingCleared_eq_Wpow_mul_uncleared_of_target
