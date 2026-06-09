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

section SumcheckSoundness

variable {ι : Type} (oSpec : OracleSpec ι)
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [Fact ((-1 : F) ≠ 1)]
  [SampleableType F]
variable (n M : ℕ)
variable (params : ProtocolParams M)
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- `F` is inhabited (by `0`), needed to synthesize the outer-phase challenge `SampleableType`
instances used when naming the sub-verifier obligations. -/
local instance : Inhabited F := ⟨0⟩

/-- The embedded sumcheck soundness residual for LogUp.
This structurally bounds the probability that `sumcheckVerifier` accepts an invalid sumcheck claim
by the standard sumcheck error `sumcheckSoundnessError`.
-/
theorem sumcheckSoundnessResidual_proved (sumcheckSoundnessError : ℝ≥0) (hInit : NeverFail init) :
    SumcheckSoundnessResidual oSpec F n M params init impl sumcheckSoundnessError := by
  sorry

end SumcheckSoundness

end Logup
