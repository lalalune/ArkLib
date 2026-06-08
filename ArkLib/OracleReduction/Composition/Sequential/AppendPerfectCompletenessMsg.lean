/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Composition.Sequential.AppendPerfectCompleteness
import ArkLib.OracleReduction.Composition.Sequential.AppendCompletenessHelper
import ArkLib.OracleReduction.Composition.Sequential.ChallengeSeamBridge

/-!
# Building blocks for the message-seam append perfect-completeness keystone (#114)

Assembles, from the proven bricks, the verified wrapper-collapse step toward discharging
`Reduction.append_perfectCompleteness_msg`:

* `support_run'_simulateQ_addLift_eq` — collapses the whole `simulateQ (impl.addLift
  challengeQueryImpl) … |>.run' s` layer of the honest-execution experiment to the OracleComp-level
  `support (run …)`. Verified composite of `OptionT.support_run_simulateQ_run'_eq` (state-faithful
  collapse) and `Prover.addLift_challenge_support_faithful` (support faithfulness of the appended
  challenge implementation). It is exactly the wrapper-collapse the keystone's docstring records as
  blocking `support_bind`, now packaged for *any* protocol spec, so it applies uniformly to the
  appended run `(R₁.append R₂).run`, to `R₁.run`, and to `R₂.run`.

Once the experiment supports are collapsed to OracleComp level, the keystone reduces to the
order-free support decomposition (`Prover.append_run_msg` + `Verifier.append_run` +
`mem_support_run_of_prover_verifier`) and the component completeness hypotheses `h₁`/`h₂`.
-/

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

namespace Reduction

variable {ι : Type} {oSpec : OracleSpec ι} [oSpec.Fintype] [oSpec.Inhabited]
  {Stmt₁ Wit₁ Stmt₂ Wit₂ : Type}
  {N : ℕ} {pSpec : ProtocolSpec N} [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type} {impl : QueryImpl oSpec (StateT σ ProbComp)}

omit [oSpec.Fintype] [oSpec.Inhabited] in
/-- **Wrapper-collapse for an interactive honest-execution experiment.** Simulating a reduction's run
under the standard `impl.addLift challengeQueryImpl` and projecting the state via `run'` has the same
support as the underlying OracleComp `run` — provided the shared-oracle implementation `impl` is
support-faithful (`hImplSupp`). Verified composite of the state-faithful collapse
`OptionT.support_run_simulateQ_run'_eq` and the appended-challenge support faithfulness
`Prover.addLift_challenge_support_faithful`. It discharges the `OptionT.mk`/`StateT.run'`/`simulateQ`
wrapper layer that blocks `support_bind` in the append perfect-completeness keystone. -/
theorem support_run'_simulateQ_addLift_eq
    [(oSpec + [pSpec.Challenge]ₒ).Fintype] [(oSpec + [pSpec.Challenge]ₒ).Inhabited]
    (R : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β))
    (stmt : Stmt₁) (wit : Wit₁) (s : σ) :
    support (m := ProbComp)
        (StateT.run' (simulateQ (impl.addLift (challengeQueryImpl (pSpec := pSpec)))
          (R.run stmt wit)) s)
      = support (m := OracleComp (oSpec + [pSpec.Challenge]ₒ)) (R.run stmt wit) :=
  OptionT.support_run_simulateQ_run'_eq _ (R.run stmt wit) s
    (Prover.addLift_challenge_support_faithful (pSpec := pSpec) impl hImplSupp)

omit [oSpec.Fintype] [oSpec.Inhabited] in
/-- **Honest-execution experiment support membership reduces to OracleComp `support (run)`.** Any
outcome `x` reachable in the perfect-completeness experiment
`OptionT.mk do (s ← init); (simulateQ (impl.addLift challengeQueryImpl) (R.run …)).run' s` (with the
`init`-bind and the three simulation wrappers) corresponds to `some x ∈ support (R.run …)` at the
OracleComp level. Combines `OptionT.mem_support_iff`, the `init`-bind `support_bind`, and the
wrapper-collapse `support_run'_simulateQ_addLift_eq`. (The `init`-nonemptiness is not even needed for
this direction.) -/
theorem mem_support_experiment_imp_mem_support_run
    [(oSpec + [pSpec.Challenge]ₒ).Fintype] [(oSpec + [pSpec.Challenge]ₒ).Inhabited]
    {init : ProbComp σ}
    (R : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β))
    (stmt : Stmt₁) (wit : Wit₁)
    (x : (FullTranscript pSpec × Stmt₂ × Wit₂) × Stmt₂)
    (hx : x ∈ support (m := OptionT ProbComp)
      (OptionT.mk do
        let s ← init
        (StateT.run' (simulateQ (impl.addLift (challengeQueryImpl (pSpec := pSpec)))
          (R.run stmt wit)) s))) :
    some x ∈ support (m := OracleComp (oSpec + [pSpec.Challenge]ₒ))
      (α := Option ((FullTranscript pSpec × Stmt₂ × Wit₂) × Stmt₂)) (R.run stmt wit) := by
  rw [OptionT.mem_support_iff] at hx
  simp only [OptionT.run_mk, support_bind, Set.mem_iUnion] at hx
  obtain ⟨s, _hs, hx⟩ := hx
  rwa [support_run'_simulateQ_addLift_eq R hImplSupp stmt wit s] at hx

end Reduction
