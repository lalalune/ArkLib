/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Composition.Sequential.ChallengeSeamBridge
import ArkLib.OracleReduction.RunUnroll

/-!
# Challenge-seam transfer for a `liftM`-ed phase game (issue #62 / #13)

The two remaining `sorry`s in `AppendSoundnessMsgProof.lean` (`Verifier.append_soundness_msg'`) are
the per-phase soundness bounds. Their only non-trivial content is a **challenge-oracle-seam
transfer**: the appended phase-`i` game runs that phase's `pSpecᵢ` rounds under the *combined*
challenge oracle `[(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ`, whereas `Vᵢ.soundness` runs them under
`pSpecᵢ`'s own oracle.

This file isolates that transfer as a single reusable `evalDist` equality, built directly on the
proven `evalDist_challengeSeam_bridge_left`: for **any** `pSpec₁`-side computation `oa`, simulating
its `liftM` into the appended challenge oracle (then projecting the value with `run'`) has the same
distribution as simulating `oa` under `pSpec₁`'s own challenge oracle. The appended phase-1 game is
exactly such a `liftM oa`, so this is the brick that turns the phase-1 `sorry` into a direct
application of `V₁.soundness`. The right-half analogue (for phase 2 / `pSpec₂`) is symmetric,
via `evalDist_challengeSeam_bridge_right`.
-/

open OracleComp OracleSpec ProtocolSpec
open scoped ENNReal

namespace OracleReduction

variable {ι : Type} {oSpec : OracleSpec ι} {σ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
  [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
  (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- **Challenge-seam transfer (left half), at `run'`/`evalDist`.** Simulating a `pSpec₁`-side
computation `oa`, lifted into the *combined* challenge oracle, and projecting the value (`run'`),
has the same distribution as simulating `oa` directly under `pSpec₁`'s challenge oracle. Immediate
from `evalDist_challengeSeam_bridge_left` (a `.run` equality) by projecting the first component. -/
theorem evalDist_run'_challengeSeam_left {α : Type}
    (oa : OracleComp (oSpec + [pSpec₁.Challenge]ₒ) α) (s : σ) :
    evalDist ((simulateQ (impl.addLift (challengeQueryImpl (pSpec := pSpec₁ ++ₚ pSpec₂)) :
        QueryImpl _ (StateT σ ProbComp))
        (liftM oa : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) α)).run' s)
      = evalDist ((simulateQ (impl.addLift (challengeQueryImpl (pSpec := pSpec₁)) :
        QueryImpl _ (StateT σ ProbComp)) oa).run' s) := by
  rw [StateT.run'_eq, StateT.run'_eq, evalDist_map, evalDist_map,
    Prover.evalDist_challengeSeam_bridge_left (impl := impl) oa s]

/-- **Challenge-seam transfer (right half), at `run'`/`evalDist`.** The `pSpec₂` analogue, from
`evalDist_challengeSeam_bridge_right`. Used for the phase-2 (`Prover.snd`) leg. -/
theorem evalDist_run'_challengeSeam_right {α : Type}
    (oa : OracleComp (oSpec + [pSpec₂.Challenge]ₒ) α) (s : σ) :
    evalDist ((simulateQ (impl.addLift (challengeQueryImpl (pSpec := pSpec₁ ++ₚ pSpec₂)) :
        QueryImpl _ (StateT σ ProbComp))
        (liftM oa : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) α)).run' s)
      = evalDist ((simulateQ (impl.addLift (challengeQueryImpl (pSpec := pSpec₂)) :
        QueryImpl _ (StateT σ ProbComp)) oa).run' s) := by
  rw [StateT.run'_eq, StateT.run'_eq, evalDist_map, evalDist_map,
    Prover.evalDist_challengeSeam_bridge_right (impl := impl) oa s]

end OracleReduction
