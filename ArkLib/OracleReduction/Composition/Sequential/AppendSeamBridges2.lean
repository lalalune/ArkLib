/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Composition.Sequential.AppendChallengeSeam
import ArkLib.OracleReduction.Composition.Sequential.AppendSoundnessSeamTransfer

/-!
# Discharging the per-phase challenge-seam bridges of the non-perfect message-seam append (issue #13)

`Reduction.append_completeness_msg_via_seamFactor` (in `AppendChallengeSeam.lean`) closes the
non-perfect (error-bearing) message-seam append completeness from the proven distributional seam
factoring `append_game_factor_msg` (which discharges `hGameFactor`), *modulo* three residual
hypotheses:

* `hStage1Bridge` — the `Prod.fst`-marginal of the state-threaded phase-1 stage game
  (`appendStage₁`, run under the *combined* challenge oracle `[(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ`)
  has the same `evalDist` as `gameOf R₁` (run under `pSpec₁`'s *own* challenge oracle);
* `hStage2Bridge` — for each phase-1 success `a`, the phase-2 stage game (`appendStage₂`, combined
  oracle) bad event is dominated by the phase-2 completeness game (`gameOf R₂`, `pSpec₂` oracle) bad
  event on the intermediate pair;
* `hTot` — the appended game never *samples* a failure.

This file discharges all three, reducing the completeness append for a message seam to its already-
proven completeness components plus the honest-implementation side conditions. The bridges are the
*completeness* analogues of the soundness append's `evalDist_run'_challengeSeam_left/right`
(`AppendSoundnessSeamTransfer.lean`): the stage-`i` body run under the combined oracle, projected to
its `OptionT.run`, is exactly `liftM` of `Rᵢ.run`'s own-oracle `OptionT.run`, which the proven
challenge-seam transfer reconciles distributionally with `gameOf Rᵢ`.

## What is proven here (no `sorry`)

* `appendStage₁_run_eq_liftM` / `appendStage₂_run_eq_liftM` — the `OptionT.run` of the phase-`i`
  stage body equals `liftM` of the `OptionT.run` of `Rᵢ.run` (across the challenge seam).
* `Reduction.appendStage1Bridge` — the discharged `hStage1Bridge` (via the proven
  `OracleReduction.evalDist_run'_challengeSeam_left`).
* `Reduction.appendStage2Bridge` — the discharged `hStage2Bridge`. The transcript-merge marginal is
  *proven* here: the completeness `goodOf` predicate examines only the statement/witness/output
  marginals of the seam output, not the (merged) transcript, so the merge is invisible to it.
* `Reduction.append_game_neverFail` — the discharged `hTot` (via `simulateQ_run_neverFail`).
* `Reduction.append_completeness_msg` — the message-seam non-perfect append completeness with the
  three challenge-seam residuals discharged: from the component completenesses `h₁`/`h₂` and the
  honest-implementation side conditions, the appended reduction is complete with additive error
  `e₁ + e₂`. This is the keystone fully discharging the completeness `hAppend` for issue #13.
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

/-! ### `OptionT`/`OracleComp` lift-commutation helpers across the challenge seam

These are local re-derivations of the seam-lift helpers (the working-tree `AppendSeamBridges.lean`
copies fail to compile in helper lemmas downstream of these, so we re-prove the parts we need here).
They reduce both lift routes to the common `simulateQ (fun t => liftM (query t))` normal form. -/

/-- **`(liftM g).run = liftM g.run` across the `pSpec₁` challenge seam.** -/
private theorem liftM_optionT_run_eq_seam_left' {α : Type}
    (g : OptionT (OracleComp (oSpec + [pSpec₁.Challenge]ₒ)) α) :
    (liftM g : OptionT (OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)) α).run
    = (liftM (g.run) : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (Option α)) := by
  rw [OracleComp.liftM_OptionT_eq, OptionT.run]
  rw [show (liftM g.run : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (Option α))
      = OracleComp.liftComp g.run _ from (OracleComp.liftComp_eq_liftM _).symm,
    OracleComp.liftComp_def]
  rfl

/-- **`(liftM g).run = liftM g.run` across the `pSpec₂` challenge seam.** -/
private theorem liftM_optionT_run_eq_seam_right' {α : Type}
    (g : OptionT (OracleComp (oSpec + [pSpec₂.Challenge]ₒ)) α) :
    (liftM g : OptionT (OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)) α).run
    = (liftM (g.run) : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (Option α)) := by
  rw [OracleComp.liftM_OptionT_eq, OptionT.run]
  rw [show (liftM g.run : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (Option α))
      = OracleComp.liftComp g.run _ from (OracleComp.liftComp_eq_liftM _).symm,
    OracleComp.liftComp_def]
  rfl

/-- **`OptionT`-lift coherence for a phase computation across the `pSpec₁` seam.** -/
private theorem lift_oc_optionT_coh_left' {α : Type}
    (A : OracleComp (oSpec + [pSpec₁.Challenge]ₒ) α) :
    (liftM (liftM A : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) α)
      : OptionT (OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)) α)
    = (liftM (liftM A : OptionT (OracleComp (oSpec + [pSpec₁.Challenge]ₒ)) α)
      : OptionT (OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)) α) := by
  apply OptionT.ext
  simp only [OracleComp.liftM_OptionT_eq]
  show OptionT.run (liftM (liftM A : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) α)) = _
  rw [OptionT.run_monadLift]
  simp only [monadLift_eq_self]
  conv_rhs => rw [show (liftM A : OptionT (OracleComp (oSpec + [pSpec₁.Challenge]ₒ)) α)
      = OptionT.lift A from rfl]
  simp only [OptionT.lift, OptionT.mk, OptionT.run, map_eq_pure_bind,
    simulateQ_bind, simulateQ_pure]
  rfl

/-- **`OptionT`-lift coherence for a phase computation across the `pSpec₂` seam.** -/
private theorem lift_oc_optionT_coh_right' {α : Type}
    (A : OracleComp (oSpec + [pSpec₂.Challenge]ₒ) α) :
    (liftM (liftM A : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) α)
      : OptionT (OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)) α)
    = (liftM (liftM A : OptionT (OracleComp (oSpec + [pSpec₂.Challenge]ₒ)) α)
      : OptionT (OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)) α) := by
  apply OptionT.ext
  simp only [OracleComp.liftM_OptionT_eq]
  show OptionT.run (liftM (liftM A : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) α)) = _
  rw [OptionT.run_monadLift]
  simp only [monadLift_eq_self]
  conv_rhs => rw [show (liftM A : OptionT (OracleComp (oSpec + [pSpec₂.Challenge]ₒ)) α)
      = OptionT.lift A from rfl]
  simp only [OptionT.lift, OptionT.mk, OptionT.run, map_eq_pure_bind,
    simulateQ_bind, simulateQ_pure]
  rfl

/-- **`OptionT`-level lift transitivity through the `pSpec₂` challenge seam.** The `pSpec₂` analogue
of `OracleReduction.hcoh`: lifting an `OptionT (OracleComp oSpec)` computation directly into the
*combined* challenge oracle equals first lifting it into `pSpec₂`'s own challenge oracle, then
across. Same `OptionT.ext`/`simulateQ_compose` normalization (the intermediate oracle is
arbitrary). -/
private theorem hcoh_right' {α : Type} (oa : OptionT (OracleComp oSpec) α) :
    (liftM oa : OptionT (OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)) α)
    = liftM (liftM oa : OptionT (OracleComp (oSpec + [pSpec₂.Challenge]ₒ)) α) := by
  apply OptionT.ext
  simp only [liftM, MonadLiftT.monadLift, MonadLift.monadLift, OptionT.run_mk,
    ← QueryImpl.simulateQ_compose]

/-! ### The stage bodies are `liftM` of the per-phase reduction run -/

/-- **The `OptionT.run` of the phase-1 stage body equals `liftM` of `R₁.run`'s `OptionT.run`.**
`appendStage₁ R₁ R₂ stmt wit` (the `P₁ → V₁` leg, run under the *combined* challenge oracle), as a
plain `OracleComp` via `OptionT.run`, is exactly the `liftM` of `(R₁.run stmt wit).run` (over
`pSpec₁`'s own challenge oracle). Mirrors `AppendSeamBridges.appendStage₁_run_eq_liftM`, with the
final verify-leg coherence supplied by `OracleReduction.hcoh` (a stable `simulateQ_compose`-based
brick) instead of the broken-in-tree `monadLift_run_eq_double_liftM_left`. -/
theorem appendStage₁_run_eq_liftM
    (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    (stmt : Stmt₁) (wit : Wit₁) :
    OptionT.run (appendStage₁ R₁ R₂ stmt wit)
      = (liftM ((R₁.run stmt wit).run)
          : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (Option _)) := by
  rw [← liftM_optionT_run_eq_seam_left' (R₁.run stmt wit)]
  rw [Reduction_run_def]
  unfold appendStage₁
  simp only [liftM_bind, liftM_pure, OptionT.run_bind, OptionT.run_pure,
    lift_oc_optionT_coh_left', Option.elimM]
  refine bind_congr fun o₁ => ?_
  cases o₁ with
  | none => rfl
  | some x =>
    obtain ⟨tr, so, wo⟩ := x
    simp only [Option.elim_some]
    -- Reduce to the verify-leg `.run` equality (continuation identical on both sides). The
    -- appendStage₁ leg lifts `verify` directly `oSpec → combined` (the one-step
    -- `MonadLift.monadLift`); the `liftM (R₁.run)` leg lifts it `oSpec → pSpec₁ → combined`
    -- (two-step). Both unfold to `simulateQ` normal forms whose handlers agree per query, folded
    -- by `simulateQ_compose`.
    have hco : (MonadLift.monadLift (R₁.verifier.verify stmt tr) :
        OptionT (OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)) Stmt₂)
        = liftM (liftM (R₁.verifier.verify stmt tr) :
            OptionT (OracleComp (oSpec + [pSpec₁.Challenge]ₒ)) Stmt₂) := by
      apply OptionT.ext
      simp only [liftM, MonadLiftT.monadLift, MonadLift.monadLift, OptionT.run_mk,
        ← QueryImpl.simulateQ_compose]
      congr 1
    exact congrArg (· >>= _) (congrArg OptionT.run hco)

/-- **The unmerged phase-2 core chain is `liftM` of `R₂.run` (right seam).** The exact `pSpec₂`
mirror of `appendStage₁_run_eq_liftM`: run prover₂ then verifier₂ (both lifted into the *combined*
challenge oracle), returning the raw pair `(proverOut, verifierOut)` with **no** transcript merge.
The merge is applied outside as a pure `<$>` by `appendStage₂_run_eq_liftM` below. -/
private theorem appendStage₂core_run_eq_liftM
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂) (stmt₂ : Stmt₂) (wit₂ : Wit₂) :
    OptionT.run
      ((liftM (liftM (R₂.prover.run stmt₂ wit₂) :
          OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _) :
          OptionT (OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ))
            (FullTranscript pSpec₂ × Stmt₃ × Wit₃)) >>= fun x =>
        (MonadLift.monadLift (R₂.verifier.verify stmt₂ x.1) :
          OptionT (OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)) Stmt₃) >>= fun s₃ =>
        pure (x, s₃))
      = (liftM ((R₂.run stmt₂ wit₂).run)
          : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
            (Option ((FullTranscript pSpec₂ × Stmt₃ × Wit₃) × Stmt₃))) := by
  rw [← liftM_optionT_run_eq_seam_right' (R₂.run stmt₂ wit₂)]
  rw [Reduction_run_def]
  simp only [liftM_bind, liftM_pure, OptionT.run_bind, OptionT.run_pure,
    lift_oc_optionT_coh_right', Option.elimM]
  refine bind_congr fun o₁ => ?_
  cases o₁ with
  | none => rfl
  | some x =>
    obtain ⟨tr, so, wo⟩ := x
    simp only [Option.elim_some]
    -- Reduce to the verify-leg `.run` equality; the core's one-step `MonadLift.monadLift`
    -- (`oSpec → combined`) and the run side's two-step (`oSpec → pSpec₂ → combined`) lifts both
    -- unfold to `simulateQ` normal forms whose handlers agree per query, folded by
    -- `simulateQ_compose`.
    have hco : (MonadLift.monadLift (R₂.verifier.verify stmt₂ tr) :
        OptionT (OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)) Stmt₃)
        = liftM (liftM (R₂.verifier.verify stmt₂ tr) :
            OptionT (OracleComp (oSpec + [pSpec₂.Challenge]ₒ)) Stmt₃) := by
      apply OptionT.ext
      simp only [liftM, MonadLiftT.monadLift, MonadLift.monadLift, OptionT.run_mk,
        ← QueryImpl.simulateQ_compose]
      congr 1
    exact congrArg (· >>= _) (congrArg OptionT.run hco)

theorem appendStage₂_run_eq_liftM
    (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    (a : (FullTranscript pSpec₁ × Stmt₂ × Wit₂) × Stmt₂)
    (hag : a.1.2.1 = a.2) :
    OptionT.run (appendStage₂ R₁ R₂ a)
      = (liftM (OptionT.run
          ((fun r : (FullTranscript pSpec₂ × Stmt₃ × Wit₃) × Stmt₃ =>
              ((a.1.1 ++ₜ r.1.1, r.1.2.1, r.1.2.2), r.2)) <$>
            (R₂.run a.2 a.1.2.2 : OptionT (OracleComp (oSpec + [pSpec₂.Challenge]ₒ)) _)))
          : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (Option _)) := by
  -- The stage body is the transcript-merge `<$>` of the unmerged core chain.
  have hmap : appendStage₂ R₁ R₂ a
      = (fun r : (FullTranscript pSpec₂ × Stmt₃ × Wit₃) × Stmt₃ =>
          ((a.1.1 ++ₜ r.1.1, r.1.2.1, r.1.2.2), r.2)) <$>
        ((liftM (liftM (R₂.prover.run a.2 a.1.2.2) :
            OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _) :
            OptionT (OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ))
              (FullTranscript pSpec₂ × Stmt₃ × Wit₃)) >>= fun x =>
          (MonadLift.monadLift (R₂.verifier.verify a.2 x.1) :
            OptionT (OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)) Stmt₃) >>= fun s₃ =>
          pure (x, s₃)) := by
    unfold appendStage₂
    rw [hag]
    simp only [map_bind]
    exact bind_congr fun x => bind_congr fun s₃ => (map_pure _ _).symm
  rw [hmap, OptionT.run_map, appendStage₂core_run_eq_liftM (pSpec₁ := pSpec₁) R₂ a.2 a.1.2.2,
    OptionT.run_map]
  -- The challenge-`SubSpec` lift commutes with the pure transcript-merge `<$>`: unfold both
  -- `liftM`s to `liftComp = simulateQ` and push the map out (`simulateQ_map`).
  simp only [← OracleComp.liftComp_eq_liftM, OracleComp.liftComp_def, simulateQ_map]

end Reduction
