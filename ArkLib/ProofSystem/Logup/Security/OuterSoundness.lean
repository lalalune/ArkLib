/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Logup.Security.SubPhaseSplit
import ArkLib.ProofSystem.Logup.Security.OuterAcceptance
import ArkLib.ProofSystem.Logup.Security.OuterRun
import ArkLib.ProofSystem.Logup.LogupGrandSumIdentity

open scoped NNReal ENNReal
open OracleComp ProtocolSpec

namespace Logup

section OuterSoundness

variable {ι : Type} (oSpec : OracleSpec ι)
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [Fact ((-1 : F) ≠ 1)]
  [SampleableType F]
variable (n M : ℕ)
variable (params : ProtocolParams M)
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- `F` is inhabited (by `0`), needed to synthesize the outer-phase challenge `SampleableType`
instances used when naming the outer sub-verifier obligations. -/
local instance : Inhabited F := ⟨0⟩

/-- The outer LogUp phase soundness residual.
By fixing `midLanguage` to be the exact sumcheck claim, the Schwartz-Zippel bound
`logup_SZ_soundness` guarantees that an invalid LogUp input produces a sumcheck claim of zero
with probability bounded by `outerSoundnessError`.
-/
theorem outerSoundnessResidual_proved (hInit : NeverFail init) :
    OuterSoundnessResidual oSpec F n M params init impl := by
  sorry

end OuterSoundness

end Logup
