/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import scripts.probes.astra_mca_production_upper
import ArkLib.Data.CodingTheory.ProximityGap.KKH26WitnessSpread

/-!
# The constructed upper bound for the existing KKH26 evaluation-code predicate

This adapter uses the existing code definition unchanged. It supplies an
upper bound only, not the matching universal lower bound or a prize solution.
-/

set_option autoImplicit false

namespace AstraMcaKkh26Upper

open AstraMcaProductionUpper ArkLib.ProximityGap.PrizeShapePrimeP30
open ArkLib.ProximityGap.KKH26 ProximityGap.MCAThresholdLedger
open scoped NNReal ENNReal

local instance : Fact (Nat.Prime P) := ⟨prime_P⟩

/-- The constructed code is the repository's original power-domain evaluation code. -/
theorem production_code_eq_evalCode :
    productionCode = evalCode g (2 ^ 30) (2 ^ 29 - 1) := by
  ext w
  exact production_code_iff w

/-- Upper bracket stated directly on the repository's original production-code predicate. -/
theorem first_prime_rate_half_delta_star_upper :
    mcaDeltaStar (F := ZMod P) (evalCode g (2 ^ 30) (2 ^ 29 - 1))
      ((1 : ℝ≥0∞) / 2 ^ 128) ≤ (357913942 : ℝ≥0) / 1073741824 := by
  rw [← production_code_eq_evalCode]
  exact production_delta_star_upper

end AstraMcaKkh26Upper

#print axioms AstraMcaKkh26Upper.production_code_eq_evalCode
#print axioms AstraMcaKkh26Upper.first_prime_rate_half_delta_star_upper
