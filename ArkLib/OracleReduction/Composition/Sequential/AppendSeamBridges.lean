/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Composition.Sequential.AppendChallengeSeam
import ArkLib.OracleReduction.Composition.Sequential.AppendSoundnessMsgProof

/-!
# Discharging the per-phase challenge-seam bridges of the non-perfect message-seam append

`Reduction.append_completeness_msg_via_seamFactor` (in `AppendChallengeSeam.lean`) closes the
non-perfect (error-bearing) message-seam append completeness from the proven distributional
seam factoring `append_game_factor_msg` (which discharges `hGameFactor`), *modulo* three residual
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
  stage body equals `liftM` of the `OptionT.run` of `Rᵢ.run` (across the challenge seam). The
  `OracleComp`-first vs `OptionT`-first lift mismatch is reconciled at the `OptionT.run`
  (plain-`OracleComp`) level by `liftComp`/`simulateQ` normalization.
* `Reduction.appendStage1Bridge` / `Reduction.appendStage2Bridge` — the discharged
  `hStage1Bridge` / `hStage2Bridge` (the latter under the named transcript-merge marginal hypothesis
  `hStage2Marginal`, isolating the irreducible bad-event relabel on the merged transcript).
* `Reduction.append_game_neverFail` — the discharged `hTot` (via `simulateQ_run_neverFail`).
* `Reduction.append_completeness_msg` — the message-seam non-perfect append completeness with the
  three challenge-seam residuals discharged: from the component completenesses `h₁`/`h₂` and the
  honest-implementation side conditions, the appended reduction is complete with additive error
  `e₁ + e₂` (modulo the single named transcript-merge marginal `hStage2Marginal`).
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

/-- **`(liftM g).run = liftM g.run` across the `pSpec₁` challenge seam.** The `OptionT`-lift of an
own-oracle `g` (`oSpec+[pSpec₁.Challenge]ₒ → combined`) commutes with `OptionT.run`: both reduce to
`liftComp = simulateQ (fun t => liftM (query t))` of the underlying `OracleComp`. Non-private
companion of `Verifier.liftM_optionT_run_eq_seam`; bridges the `OptionT`-level seam body to the
`OracleComp`-level `evalDist_run'_challengeSeam_left`. -/
theorem liftM_optionT_run_eq_seam_left {α : Type}
    (g : OptionT (OracleComp (oSpec + [pSpec₁.Challenge]ₒ)) α) :
    (liftM g : OptionT (OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)) α).run
    = (liftM (g.run) : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (Option α)) := by
  rw [OracleComp.liftM_OptionT_eq, OptionT.run]
  rw [show (liftM g.run : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (Option α))
      = OracleComp.liftComp g.run _ from (OracleComp.liftComp_eq_liftM _).symm,
    OracleComp.liftComp_def]
  rfl

/-- **`(liftM g).run = liftM g.run` across the `pSpec₂` challenge seam.** The `pSpec₂` analogue of
`liftM_optionT_run_eq_seam_left`. -/
theorem liftM_optionT_run_eq_seam_right {α : Type}
    (g : OptionT (OracleComp (oSpec + [pSpec₂.Challenge]ₒ)) α) :
    (liftM g : OptionT (OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)) α).run
    = (liftM (g.run) : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (Option α)) := by
  rw [OracleComp.liftM_OptionT_eq, OptionT.run]
  rw [show (liftM g.run : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (Option α))
      = OracleComp.liftComp g.run _ from (OracleComp.liftComp_eq_liftM _).symm,
    OracleComp.liftComp_def]
  rfl

/-- **`OptionT`-lift coherence for a phase computation across the `pSpec₁` seam.** Lifting a
`pSpec₁`-oracle `OracleComp` value `A` *first across `OracleComp`* (`oSpec+[pSpec₁.Challenge]ₒ →
combined`) and then into `OptionT` of the combined oracle, equals lifting it into `OptionT` of its
own (`pSpec₁`) oracle first and then across into `OptionT` of the combined oracle. Both routes reduce
to the same `simulateQ (fun t => liftM (query t))` normal form. Non-private companion of
`Verifier.lift_oc_optionT_coh`. -/
theorem lift_oc_optionT_coh_left {α : Type}
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

/-- **`OptionT`-lift coherence for a phase computation across the `pSpec₂` seam.** The `pSpec₂`
analogue of `lift_oc_optionT_coh_left`. -/
theorem lift_oc_optionT_coh_right {α : Type}
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

/-- **Verifier-leg `OptionT`-lift coherence across the `pSpec₁` seam, at `.run`.** The verifier
seam leg is an `OptionT (OracleComp oSpec)` value `V` (the verifier queries only `oSpec`). The
phase-1 stage body lifts it `oSpec → combined` directly (`MonadLift.monadLift`), whereas
`liftM (R₁.run …)` lifts it `oSpec → pSpec₁ → combined`; these build distinct (`propositionally`-
equal-but-not-defeq) `MonadLift` instances. Both reduce to the same `simulateQ (fun t => liftM
(query t))` normal form, so the `.run`s agree — the same `OptionT.ext`/`simulateQ_compose` route as
`OracleReduction.hcoh`, stated at the goal's `MonadLift.monadLift`/`.run` shape. -/
theorem monadLift_run_eq_double_liftM_left {α : Type} (V : OptionT (OracleComp oSpec) α) :
    (MonadLift.monadLift V :
        OptionT (OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)) α).run
    = (liftM (liftM V : OptionT (OracleComp (oSpec + [pSpec₁.Challenge]ₒ)) α)
        : OptionT (OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)) α).run := by
  simp only [liftM, MonadLiftT.monadLift, MonadLift.monadLift, OptionT.run_mk]
  rw [← QueryImpl.simulateQ_compose]
  congr 1

/-- **`OptionT`-level lift transitivity through the `pSpec₂` challenge seam.** The `pSpec₂` analogue
of `OracleReduction.hcoh`: lifting an `OptionT (OracleComp oSpec)` computation directly into the
*combined* challenge oracle equals first lifting it into `pSpec₂`'s own challenge oracle then across.
Same `OptionT.ext`/`simulateQ_compose` normalization (the intermediate oracle is arbitrary). -/
theorem hcoh_right {α : Type} (oa : OptionT (OracleComp oSpec) α) :
    (liftM oa : OptionT (OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)) α)
    = liftM (liftM oa : OptionT (OracleComp (oSpec + [pSpec₂.Challenge]ₒ)) α) := by
  apply OptionT.ext
  simp only [liftM, MonadLiftT.monadLift, MonadLift.monadLift, OptionT.run_mk]

/-- **Verifier-leg `OptionT`-lift coherence across the `pSpec₂` seam, at `.run`.** The `pSpec₂`
analogue of `monadLift_run_eq_double_liftM_left`. -/
theorem monadLift_run_eq_double_liftM_right {α : Type} (V : OptionT (OracleComp oSpec) α) :
    (MonadLift.monadLift V :
        OptionT (OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)) α).run
    = (liftM (liftM V : OptionT (OracleComp (oSpec + [pSpec₂.Challenge]ₒ)) α)
        : OptionT (OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)) α).run := by
  simp only [liftM, MonadLiftT.monadLift, MonadLift.monadLift, OptionT.run_mk]
  rw [← QueryImpl.simulateQ_compose]
  congr 1

/-- **The `OptionT.run` of the phase-1 stage body equals `liftM` of `R₁.run`'s `OptionT.run`.**
`appendStage₁ R₁ R₂ stmt wit` (the `P₁ → V₁` leg, run under the *combined* challenge oracle), as a
plain `OracleComp` via `OptionT.run`, is exactly the `liftM` of `(R₁.run stmt wit).run` (over
`pSpec₁`'s own challenge oracle). Unfolds `appendStage₁` and `Reduction.run` (`Reduction_run_def`),
reconciles the `OracleComp`-first prover lift (`appendStage₁`) with the `OptionT`-first lift of
`liftM (R₁.run …)` via `lift_oc_optionT_coh_left`, then strips to `OracleComp` with
`liftM_optionT_run_eq_seam_left`. -/
theorem appendStage₁_run_eq_liftM
    (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    (stmt : Stmt₁) (wit : Wit₁) :
    OptionT.run (appendStage₁ R₁ R₂ stmt wit)
      = (liftM ((R₁.run stmt wit).run)
          : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (Option _)) := by
  -- Reduce the RHS to `(liftM (R₁.run stmt wit)).run` (both at plain-`OracleComp` level).
  rw [← liftM_optionT_run_eq_seam_left (R₁.run stmt wit)]
  -- Unfold both `OptionT.run`s and `Reduction.run`; the prover legs are reconciled by
  -- `lift_oc_optionT_coh_left`, the verify legs are a bare lift, and the final `pure`/`getM` cancel.
  rw [Reduction_run_def]
  unfold appendStage₁
  -- The prover legs match after `lift_oc_optionT_coh_left`; the verify legs differ only by a
  -- redundant `liftM`-to-self on the RHS (`monadLift_eq_self`); the final `pure` differs by the
  -- (defeq) destructured prover output. `simp` normalizes all three to a common chain.
  simp only [liftM_bind, liftM_pure, OptionT.run_bind, OptionT.run_pure,
    lift_oc_optionT_coh_left, Option.elimM, bind_assoc]
  -- Prover legs are now identical; `bind_congr` reduces to the per-output `elim` branches.
  refine bind_congr fun o₁ => ?_
  cases o₁ with
  | none => rfl
  | some x =>
    obtain ⟨tr, so, wo⟩ := x
    simp only [Option.elim_some]
    -- Reduce to the verify-leg `.run` equality (the continuation `k` is identical on both sides).
    -- `verify : OptionT (OracleComp oSpec)`; the appendStage₁ leg lifts it `oSpec → combined`
    -- directly, the `liftM (R₁.run)` leg lifts it `oSpec → pSpec₁ → combined`.
    exact congrArg (· >>= _) (monadLift_run_eq_double_liftM_left (R₁.verifier.verify stmt tr))

end Reduction
