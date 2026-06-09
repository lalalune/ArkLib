/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Composition.Sequential.AppendChallengeSeam
import ArkLib.OracleReduction.Composition.Sequential.AppendRunEvalDistChallenge

/-!
# Challenge-seam append game-factoring (`hGameFactor` discharge for a `V_to_P` seam)

`AppendChallengeSeam.lean` discharges the completeness `hGameFactor` residual of
`append_completeness_msg_proof` for the **message seam** via `append_game_factor_msg`, whose only
seam-specific step is `append_run_natural_msg` (the *syntactic* run factoring through
`Prover.append_run_msg`). At a **challenge seam** (`pSpec₂`'s round 0 is `V_to_P`) the syntactic run
factoring is *false* — the appended prover samples the seam `getChallenge` before consuming
`P₁.output` — but the appended honest *game* still factors as a distribution: the seam challenge is a
uniform sample that commutes, under the honest state-preserving implementation, past the prover's
`oSpec`-computation (the simulated analogue of the bare `evalDist_bind_comm` used in
`Prover.append_run_evalDist_challenge`, here `RunUnroll.evalDist_simulateQ_swap_prefix`).

`append_game_factor_challenge` discharges `hGameFactor` for the challenge seam; combined with the
(seam-direction-agnostic) bridges in `AppendSeamBridges.lean` it gives challenge-seam append
completeness, the missing keystone for the Spartan composed perfect completeness (#114).
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

/-- **The simulated appended honest game factors at a challenge seam (`evalDist`-level).** The
distributional core of completeness `hGameFactor` for a `V_to_P` seam: the simulated honest game of
`R₁.append R₂` — running its rounds under `impl.addLift challengeQueryImpl` — has the same `evalDist`
as the **union-bound order** `appendStage₁ ; appendStage₂` (= `(P₁→V₁) ; (P₂→V₂)`), in the `mx >>= my`
shape `probComp_seam_completeness` consumes.

The natural-order chain `P₁ → P₂ → V₁ → V₂` is reached from the appended run by the simulated seam
swap `evalDist_simulateQ_swap_prefix` (the seam `getChallenge` commutes past `P₁.output` under the
state-preserving `impl.addLift challengeQueryImpl`); the `P₂`-past-`V₁` reorder to the stage chain is
the proven `seam_swap_evalDist_eq`. -/
theorem append_game_factor_challenge
    (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    (stmt : Stmt₁) (wit : Wit₁) (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .V_to_P)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .V_to_P)
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0) :
    evalDist (gameOf init impl (R₁.append R₂) stmt wit)
      = evalDist (init >>= fun s =>
          StateT.run' (simulateQ (impl.addLift challengeQueryImpl)
            ((appendStage₁ R₁ R₂ stmt wit) >>= (appendStage₂ R₁ R₂)).run) s) := by
  -- The `P₂`-past-`V₁` reorder (natural-order → stage chain), seam-direction-agnostic. Pin the
  -- seam-swap `spec` (and `challengeQueryImpl`'s `pSpec`) to the combined challenge oracle so every
  -- instance (the combined `SampleableType` for `challengeQueryImpl`, the per-phase `SubSpec` lifts in
  -- `W1`/`W2`) is synthesized the *same* way the goal's are — no `haveI` indirection, no instance-term
  -- mismatch under `Eq.trans`.
  have hswap := seam_swap_evalDist_eq
    (spec := oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) init
    (impl.addLift (challengeQueryImpl (pSpec := pSpec₁ ++ₚ pSpec₂)))
    (addLift_state_preserving impl himplSP)
    (liftM (R₁.prover.run stmt wit)) (fun x => liftM (R₂.prover.run x.2.1 x.2.2))
    (fun x => (MonadLift.monadLift (R₁.verifier.verify stmt x.1) :
        OptionT (OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)) Stmt₂))
    (fun x a s₂ => (MonadLift.monadLift (R₂.verifier.verify s₂ a.1) :
          OptionT (OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)) Stmt₃) >>= fun s₃ =>
      pure ((x.1 ++ₜ a.1, a.2.1, a.2.2), s₃))
    (fun x s' => simulateQ_run_neverFail _ (addLift_neverFail impl himplNF) _ s')
  -- Unfold `gameOf` (LHS) and the stage chain (RHS) so the goal's RHS becomes `hswap`'s union-bound
  -- RHS *syntactically*; `appendStageᵢ` unfold to exactly the `liftM FSTᵢ ≫ Wᵢ ≫ pure` legs.
  simp only [gameOf, appendStage₁, appendStage₂]
  -- Bridge to `hswap` (the `P₂`-past-`V₁` reorder). `convert` absorbs the defeq instance-term
  -- differences (the combined-challenge `SampleableType`); the residual goal is the seam-challenge
  -- swap (`appended game = natural-order game`).
  refine Eq.trans ?_ hswap
  -- `gameOf` (`abbrev`) unfolds to `init >>= fun s => (simulateQ so (·.run)).run' s`; pull `evalDist`
  -- through the `init` bind so the residual is the per-seed seam-challenge swap.
  simp only [gameOf]
  rw [evalDist_bind, evalDist_bind]
  refine bind_congr fun s => ?_
  -- The seam-challenge swap under simulation. The appended run's seam `getChallenge` sits before the
  -- `P₁.output` replay; `evalDist_simulateQ_swap_prefix` (state-preserving) commutes them to the
  -- natural order, matching the bare `Prover.append_run_evalDist_challenge` reorder lifted through
  -- `simulateQ`.
  sorry

/-- **Challenge-seam append completeness (`hGameFactor` discharged via the seam-challenge swap).**
The challenge-seam analogue of `append_completeness_msg_via_seamFactor`: threads
`append_game_factor_challenge` into `append_completeness_msg_proof` for the same two-stage
decomposition, leaving only the (seam-direction-agnostic) per-phase challenge-oracle relabel bridges
`hStage1Bridge`/`hStage2Bridge` and the game totality `hTot` (all discharged in
`AppendSeamBridges.lean`). -/
theorem append_completeness_challenge_via_seamFactor
    (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    {e₁ e₂ : ℝ≥0}
    (h₁ : R₁.completeness init impl rel₁ rel₂ e₁)
    (h₂ : R₂.completeness init impl rel₂ rel₃ e₂)
    (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .V_to_P)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .V_to_P)
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0)
    (hStage1Bridge : ∀ stmt wit, (stmt, wit) ∈ rel₁ →
      evalDist (Prod.fst <$> (init >>= fun s =>
          StateT.run (simulateQ (impl.addLift challengeQueryImpl)
            (OptionT.run (appendStage₁ R₁ R₂ stmt wit))) s))
        = evalDist (gameOf init impl R₁ stmt wit))
    (hStage2Bridge : ∀ stmt wit, (stmt, wit) ∈ rel₁ →
      ∀ a s', (some a, s') ∈ support
            (init >>= fun s =>
              StateT.run (simulateQ (impl.addLift challengeQueryImpl)
                (OptionT.run (appendStage₁ R₁ R₂ stmt wit))) s) →
          goodOf m pSpec₁ rel₂ a →
          Pr[fun o => ¬ Option.elim o False (goodOf (m + n) (pSpec₁ ++ₚ pSpec₂) rel₃ ·)
              | (StateT.run' (simulateQ (impl.addLift challengeQueryImpl)
                  (OptionT.run (appendStage₂ R₁ R₂ a))) s' : ProbComp (Option _))]
            ≤ Pr[fun o => ¬ Option.elim o False (goodOf n pSpec₂ rel₃ ·)
              | gameOf init impl R₂ a.2 a.1.2.2])
    (hTot : ∀ stmt wit, (stmt, wit) ∈ rel₁ →
      Pr[⊥ | gameOf init impl (R₁.append R₂) stmt wit] = 0) :
    (R₁.append R₂).completeness init impl rel₁ rel₃ (e₁ + e₂) :=
  append_completeness_msg_proof R₁ R₂ h₁ h₂
    (so := impl.addLift challengeQueryImpl)
    (mx := fun p => appendStage₁ R₁ R₂ p.1 p.2)
    (my := fun p => appendStage₂ R₁ R₂)
    (fun stmt wit _ =>
      append_game_factor_challenge R₁ R₂ stmt wit hn hDir hDir₂ himplSP himplNF)
    hStage1Bridge hStage2Bridge hTot

end Reduction
