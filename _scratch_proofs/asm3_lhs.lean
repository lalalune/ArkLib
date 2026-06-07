import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2Assembly
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2Vanish

open scoped BigOperators
open Finset Polynomial Polynomial.Bivariate ArkLib.PowerSeriesComposition
open BCIKS20AppendixA ProximityPrize.BCIKS20.GammaGenuine

namespace BCIKS20.HenselNumerator

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

-- recall taylorCollapse, antidiag_reindex, depSwap are in keystone_base.lean's namespace;
-- but they're private/in scratch. Let me re-prove minimal versions or check availability.
-- Instead I'll explore the LHS unfold.

example (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ) :
    restrictedFaaDiBrunoPartitionForm H x₀ R hHyp t = 0 := by
  unfold restrictedFaaDiBrunoPartitionForm
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, βHenselAssembled_constantCoeff]
  sorry

end BCIKS20.HenselNumerator
