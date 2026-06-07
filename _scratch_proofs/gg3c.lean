import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2Assembly
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2Reabsorb
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2Vanish

/-! Attempt the genuine term-level partition match.  Strategy: clear the denominator, then
reindex the LHS (Y-degree i + X-Taylor ab) against the RHS (X-Taylor i1 + partition of t+1-i1). -/

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

-- First: reformulate the partition match as a cleared (denominator-free) equation.
-- RHS = ζ·(recSum/den), den ≠ 0.  So MatchAt ↔ LHS·den = ζ·recSum.
-- This avoids division and makes the term-by-term match tractable.

theorem partitionMatchAt_iff_cleared (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (t : ℕ) :
    RestrictedFaaDiBrunoPartitionMatchAt H x₀ R hHyp t ↔
      restrictedFaaDiBrunoPartitionForm H x₀ R hHyp t
        * ((liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1 + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * (t + 1) - 1))
      = ClaimA2.ζ R x₀ H *
          (∑ i1 ∈ Finset.range (t + 2),
            ∑ lam ∈ (Finset.univ : Finset (Nat.Partition (t + 1 - i1))).filter
                      (fun lam => (t + 1) ∉ lam.parts),
              embeddingOf𝒪Into𝕃 H (W𝒪 H) ^ (i1 + deltaSave i1 - 1)
                * embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp) ^ (2 * i1 + sigmaLambda lam - 2)
                * embeddingOf𝒪Into𝕃 H (B_coeff H x₀ R i1 lam)
                * embeddingOf𝒪Into𝕃 H (partitionProd lam (βHensel H x₀ R hHyp))) := by
  unfold RestrictedFaaDiBrunoPartitionMatchAt restrictedMatchRecursionPartitionForm
  set den : 𝕃 H := (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1 + 1)
      * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * (t + 1) - 1) with hden
  set recSum : 𝕃 H :=
    ∑ i1 ∈ Finset.range (t + 2),
      ∑ lam ∈ (Finset.univ : Finset (Nat.Partition (t + 1 - i1))).filter
                (fun lam => (t + 1) ∉ lam.parts),
        embeddingOf𝒪Into𝕃 H (W𝒪 H) ^ (i1 + deltaSave i1 - 1)
          * embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp) ^ (2 * i1 + sigmaLambda lam - 2)
          * embeddingOf𝒪Into𝕃 H (B_coeff H x₀ R i1 lam)
          * embeddingOf𝒪Into𝕃 H (partitionProd lam (βHensel H x₀ R hHyp)) with hrec
  have hden_ne : den ≠ 0 := by
    rw [hden]
    exact den_ne_zero H x₀ R hHyp (t + 1)
  -- goal: (LHS = ζ·(recSum/den)) ↔ (LHS·den = ζ·recSum)
  rw [mul_div_assoc']
  rw [eq_div_iff hden_ne]

end BCIKS20.HenselNumerator

-- Confirm the cleared form is a genuine route to closing #139:
-- proving the cleared equation for all t closes the keystone.
namespace Final
open BCIKS20.HenselNumerator

theorem keystone_of_cleared {F : Type} [Field F] (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hcleared : ∀ t : ℕ,
      restrictedFaaDiBrunoPartitionForm H x₀ R hHyp t
        * ((liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1 + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * (t + 1) - 1))
      = ClaimA2.ζ R x₀ H *
          (∑ i1 ∈ Finset.range (t + 2),
            ∑ lam ∈ (Finset.univ : Finset (Nat.Partition (t + 1 - i1))).filter
                      (fun lam => (t + 1) ∉ lam.parts),
              embeddingOf𝒪Into𝕃 H (W𝒪 H) ^ (i1 + deltaSave i1 - 1)
                * embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp) ^ (2 * i1 + sigmaLambda lam - 2)
                * embeddingOf𝒪Into𝕃 H (B_coeff H x₀ R i1 lam)
                * embeddingOf𝒪Into𝕃 H (partitionProd lam (βHensel H x₀ R hHyp)))) :
    βHenselAssembled H x₀ R hHyp = gammaGenuine x₀ R H hHyp := by
  have hpart : RestrictedFaaDiBrunoPartitionMatch H x₀ R hHyp := fun t =>
    (partitionMatchAt_iff_cleared H x₀ R hHyp t).mpr (hcleared t)
  exact βHenselAssembled_eq_gammaGenuine H x₀ R hHyp
    (assembledSeries_isRoot_of_partitionMatch H x₀ R hHyp hpart)

end Final

#print axioms BCIKS20.HenselNumerator.partitionMatchAt_iff_cleared
#print axioms Final.keystone_of_cleared
