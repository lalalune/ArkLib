import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2Assembly

open scoped BigOperators
open Finset Polynomial Polynomial.Bivariate ArkLib.PowerSeriesComposition
open BCIKS20AppendixA ProximityPrize.BCIKS20.GammaGenuine

namespace BCIKS20.HenselNumerator

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

-- Drive LHS: STEP0 (replace coeff0 by α₀), STEP1 (sum_comm), STEP2 (antidiag_reindex)
example (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ) :
    restrictedFaaDiBrunoPartitionForm H x₀ R hHyp t = 0 := by
  unfold restrictedFaaDiBrunoPartitionForm
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, βHenselAssembled_constantCoeff]
  -- STEP1: sum_comm over (i, ab)
  rw [Finset.sum_comm]
  -- now: ∑ ab ∈ antidiag(t+1), ∑ i ∈ range(Q.nd+1), ...
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  -- now ∑ i1 ∈ range(t+2), ∑ i ∈ range(Q.nd+1), [coeff_l part * inner lam-sum]
  extract_goal
  sorry

end BCIKS20.HenselNumerator
