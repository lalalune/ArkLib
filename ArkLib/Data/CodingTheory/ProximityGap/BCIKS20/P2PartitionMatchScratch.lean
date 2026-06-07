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

theorem restrictedFaaDiBrunoPartitionMatchAt_proof (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ) :
    RestrictedFaaDiBrunoPartitionMatchAt H x₀ R hHyp t := by
  unfold RestrictedFaaDiBrunoPartitionMatchAt
  unfold restrictedFaaDiBrunoPartitionForm restrictedMatchRecursionPartitionForm
  rw [← restrictedFaaDiBrunoSum_eq_partitionForm H x₀ R hHyp t]
  rw [← restrictedMatch_rhs_eq_recursionPartitionForm H x₀ R hHyp t]
  sorry

end BCIKS20.HenselNumerator
