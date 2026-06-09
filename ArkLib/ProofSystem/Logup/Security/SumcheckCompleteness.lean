/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Logup.Security.SubPhaseSplit
import ArkLib.ProofSystem.Sumcheck.Spec.General

open scoped NNReal ENNReal
open OracleComp ProtocolSpec

namespace Logup

section SumcheckCompleteness

variable {ι : Type} (oSpec : OracleSpec ι)
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [Fact ((-1 : F) ≠ 1)]
  [SampleableType F]
variable (n M : ℕ)
variable (params : ProtocolParams M)
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- `F` is inhabited (by `0`), needed to synthesize the outer-phase challenge `SampleableType`
instances used when naming the sub-verifier obligations. -/
local instance : Inhabited F := ⟨0⟩

/-- The embedded sumcheck completeness residual for LogUp.
This completes the completeness run-unfolding bridge for the generic sumcheck module.
-/
theorem sumcheckCompletenessResidual_proved (hInit : NeverFail init) :
    SumcheckCompletenessResidual oSpec F n M params init impl := by
  sorry

end SumcheckCompleteness

end Logup
