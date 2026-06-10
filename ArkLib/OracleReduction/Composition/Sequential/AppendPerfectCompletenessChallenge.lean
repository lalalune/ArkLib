/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Composition.Sequential.AppendChallengeSeamChallenge
import ArkLib.OracleReduction.Composition.Sequential.AppendSeamBridges
import ArkLib.OracleReduction.Composition.Sequential.AppendSeamBridges2
import ArkLib.OracleReduction.Composition.Sequential.AppendSoundnessSeamTransfer

/-!
# Challenge-seam append perfect completeness

`append_perfectCompleteness_challenge`: the `V_to_P`-seam analogue of
`append_perfectCompleteness_message`. The message-seam proof factors the prover *syntactically*
(`Prover.append_run_msg`), which is **false** at a challenge seam; so we route through the proven
challenge-seam completeness keystone `append_completeness_challenge_via_seamFactor` specialized to
zero error, discharging its three per-phase challenge-oracle relabel residuals
(`hStage1Bridge`/`hStage2Bridge`/`hTot`) from the proven seam-transfer infrastructure
(`appendStageᵢ_run_eq_liftM` + `evalDist_run'_challengeSeam_left/right`).
-/

open OracleComp OracleSpec ProtocolSpec OptionTStateT
open scoped ENNReal NNReal

namespace Reduction

variable {ι : Type} {oSpec : OracleSpec ι} [oSpec.Fintype] [oSpec.Inhabited]
  {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
  [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}

/-- **Challenge-seam `hStage1Bridge` discharge.** The phase-1 game over the *combined* challenge
oracle agrees (as `evalDist`) with `R₁`'s own phase-1 game: `appendStage₁_run_eq_liftM` rewrites the
stage to `liftM (R₁.run …)` over the combined oracle, and `evalDist_run'_challengeSeam_left` transfers
the combined run back to `pSpec₁`'s own challenge oracle. -/
theorem challenge_hStage1Bridge
    (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    (stmt : Stmt₁) (wit : Wit₁) :
    evalDist (Prod.fst <$> (init >>= fun s =>
        StateT.run (simulateQ (impl.addLift challengeQueryImpl)
          (OptionT.run (appendStage₁ R₁ R₂ stmt wit))) s))
      = evalDist (gameOf init impl R₁ stmt wit) := by
  rw [appendStage₁_run_eq_liftM, map_bind, gameOf, evalDist_bind, evalDist_bind]
  refine bind_congr fun s => ?_
  rw [← StateT.run'_eq]
  exact OracleReduction.evalDist_run'_challengeSeam_left impl ((R₁.run stmt wit).run) s

/-- **Challenge-seam `hTot` discharge.** The appended simulated honest game never *samples* a
failure: `init` never fails (`hInit`) and the simulated run never fails (`simulateQ_run_neverFail`
from the never-failing honest implementation `addLift_neverFail`). -/
theorem challenge_hTot
    (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0)
    (hInit : NeverFail init)
    (stmt : Stmt₁) (wit : Wit₁) :
    Pr[⊥ | gameOf init impl (R₁.append R₂) stmt wit] = 0 := by
  rw [gameOf, probFailure_bind_eq_zero_iff]
  refine ⟨by rwa [probFailure_eq_zero_iff], fun s _ => ?_⟩
  rw [StateT.run'_eq, probFailure_map]
  exact simulateQ_run_neverFail _ (addLift_neverFail impl himplNF) _ s

end Reduction
