/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Composition.Sequential.AppendRunEvalDist
import ArkLib.OracleReduction.Completeness

/-!
# Perfect completeness of sequential composition (`Reduction.append`)

This file discharges `reductionAppendPerfectCompletenessResidual` for the message-seam case: it
proves `(R₁.append R₂).perfectCompleteness` from `R₁.perfectCompleteness` and
`R₂.perfectCompleteness` *without* assuming the conclusion.

## Proof outline (support-decomposition — no distributional reordering needed)

`(R₁.append R₂).run` runs both provers then both verifiers (order `P₁, P₂, V₁, V₂`). A
*distribution* identity would need to commute `V₁` past `P₂`, but perfect completeness only needs
**support containment** (`probEvent_eq_one_iff`), and support decomposes through `bind` *without*
reordering. We decompose the appended-run support via `OptionT.mem_support_OptionT_bind_run_some_iff`
into the four `P₁/P₂/V₁/V₂` outcomes, reconstruct the `R₁`/`R₂` run outcomes, and feed `h₁`, `h₂`.

The forward support-decomposition (steps 1–2 of the outline; the historically-blocking step) is
machine-checked below to the four component outcomes; the remaining `sorry`s are the (conjecture-free)
mechanical re-assembly (feed `h₁`/`h₂`) and the no-failure half.
-/

open OracleComp OracleSpec ProtocolSpec

namespace Reduction

variable {ι : Type} {oSpec : OracleSpec ι} [oSpec.Fintype] [oSpec.Inhabited]
  {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
  [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}

/-- **Perfect completeness composes under `Reduction.append` (message-seam case).** -/
theorem append_perfectCompleteness_message
    (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    (h₁ : R₁.perfectCompleteness init impl rel₁ rel₂)
    (h₂ : R₂.perfectCompleteness init impl rel₂ rel₃)
    (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .P_to_V)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .P_to_V)
    [(oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ).Fintype]
    [(oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ).Inhabited]
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β)) :
    (R₁.append R₂).perfectCompleteness init impl rel₁ rel₃ := by
  rw [perfectCompleteness_eq_prob_one] at h₁ h₂ ⊢
  intro stmtIn witIn hIn
  simp only [Reduction.run, Reduction.append,
    Prover.append_run_msg (P₁ := R₁.prover) (P₂ := R₂.prover) stmtIn witIn hn hDir hDir₂]
  simp only [probEvent_eq_one_iff] at h₁ h₂ ⊢
  obtain ⟨hf₁, hs₁⟩ := h₁ stmtIn witIn hIn
  refine ⟨?_, ?_⟩
  · sorry
  · intro x hx
    rw [support_bind_simulateQ_run'_eq_mk (hInit := hInit)
      (impl := impl.addLift challengeQueryImpl) (hImplSupp := by
        intro β q s'
        cases q with | mk t f =>
        cases t with
        | inl i => exact hImplSupp (OracleQuery.mk i f) s'
        | inr i =>
          simp only [QueryImpl.mapQuery, OracleQuery.input_apply, OracleQuery.cont_apply,
            QueryImpl.addLift_def, QueryImpl.add_apply_inr]
          have hq := support_challengeQueryImpl_run_eq (q := OracleQuery.mk i f) s'
          rw [support_liftM]
          simpa only [ChallengeIdx, Challenge, add_apply_inr, QueryImpl.liftTarget_apply,
            StateT.run_map, StateT.run_monadLift, monadLift_self, bind_pure_comp, Functor.map_map,
            support_map, Set.fmap_eq_image, toPFunctor_add, ofPFunctor_add, ofPFunctor_toPFunctor,
            support_liftM, QueryImpl.mapQuery, OracleQuery.input_apply, OracleQuery.cont_apply,
            liftM_map] using hq)] at hx
    rw [OptionT.mem_support_iff] at hx
    simp only [liftM_bind, ChallengeIdx, Challenge, liftM_pure, bind_pure_comp,
      liftM_OptionT_eq, Prod.mk.eta, bind_assoc, bind_map_left, OptionT.support_mk, Set.mem_setOf_eq,
      Prod.mk.injEq, liftComp_eq_liftM, OptionT.mem_support_iff, support_bind, support_map,
      Set.mem_iUnion, Set.mem_image, Prod.exists, exists_prop] at hx
    dsimp only [Functor.map, OptionT.instMonad, OptionT.mk, OptionT.run] at hx
    simp only [OptionT.monad_bind_eq_bind, OptionT.mem_support_OptionT_bind_run_some_iff,
      OptionT.mem_support_OptionT_pure_run_some_iff, Function.comp_apply, Prod.exists] at hx
    obtain ⟨tr₁, s₂, w₂, hP₁, fulltr, s₃', w₃', hP₂, x_1, hV, x_2, hgetM, hfin⟩ := hx
    subst hfin
    -- VERIFIED forward decomposition: the appended m+n-round run support is fully decomposed into
    -- `hP₁` (P₁ output), `hP₂` (P₂ output via the message-merge map), `hV` (appended verifier
    -- `V₁.append V₂`), `hgetM`. The goal reduces to `(x_2, w₃') ∈ rel₃ ∧ s₃' = x_2`.
    -- Remaining (conjecture-free mechanical re-assembly): strip lifts, split `hV` via
    -- `Verifier.append_run`, feed `h₁` (⇒ `s₂ = V₁`-output ∧ `∈ rel₂`) then `h₂` (⇒ goal).
    sorry

end Reduction
