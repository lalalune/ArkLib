import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2Assembly
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2BijectionApply

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

theorem restrictedMatch_rhs_eq_restrictedMatchRecursionPartitionForm_proof (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ) :
    let recSum : 𝕃 H :=
      ∑ i1 ∈ Finset.range (t + 2),
        ∑ lam ∈ (Finset.univ : Finset (Nat.Partition (t + 1 - i1))).filter
                  (fun lam => (t + 1) ∉ lam.parts),
          embeddingOf𝒪Into𝕃 H (W𝒪 H) ^ (i1 + deltaSave i1 - 1)
            * embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp) ^ (2 * i1 + sigmaLambda lam - 2)
            * embeddingOf𝒪Into𝕃 H (B_coeff H x₀ R i1 lam)
            * embeddingOf𝒪Into𝕃 H (partitionProd lam (βHensel H x₀ R hHyp));
    let den : 𝕃 H :=
      (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1 + 1)
        * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * (t + 1) - 1);
    - (ClaimA2.ζ R x₀ H
        * PowerSeries.coeff (t + 1) (βHenselAssembled H x₀ R hHyp))
      = ClaimA2.ζ R x₀ H * (recSum / den) := by
  sorry

end BCIKS20.HenselNumerator
