import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2Match

open scoped BigOperators
open Finset Polynomial Polynomial.Bivariate ArkLib.PowerSeriesComposition
open BCIKS20AppendixA ProximityPrize.BCIKS20.GammaGenuine
open ProximityPrize.HenselSeriesCoeff

namespace BCIKS20.HenselNumerator

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

-- Examine βHensel 1 via βHensel_succ at k=0:
-- the sum is over i1 ∈ range 2, lam ∈ partitions of (1 - i1) with 1 ∉ parts.
-- i1 = 0: partitions of 1 with 1 ∉ parts: ONLY the indiscrete (single part {1}), excluded! so EMPTY.
-- i1 = 1: partitions of 0 with 1 ∉ parts: the empty partition (always there). 
-- So βHensel 1 = - [ W^{1+0-1} · ξ^{2·1+1-2} · B_coeff(i1=1, empty) · partitionProd(empty) ]
--             = - [ W^0 · ξ^1 · B_coeff(1, ∅) · 1 ] = - ξ · B_coeff(1, ∅)
example (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) :
    βHensel H x₀ R hHyp 1 =
      - ∑ i1 ∈ Finset.range 2,
          ∑ lam ∈ (Finset.univ : Finset (Nat.Partition (1 - i1))).filter
                    (fun lam => 1 ∉ lam.parts),
            (W𝒪 H) ^ (i1 + deltaSave i1 - 1)
              * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * i1 + sigmaLambda lam - 2)
              * B_coeff H x₀ R i1 lam
              * partitionProd lam
                  (fun l => if _h : l < 1 then βHensel H x₀ R hHyp l else 0) := by
  have := βHensel_succ H x₀ R hHyp 0
  simpa using this

end BCIKS20.HenselNumerator
