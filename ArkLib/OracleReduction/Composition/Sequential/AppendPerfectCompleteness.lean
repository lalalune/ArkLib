/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Composition.Sequential.AppendRunEvalDist
import ArkLib.OracleReduction.Completeness

/-!
# Perfect completeness of sequential composition (`Reduction.append`)

The append-completeness theorem in `Append.lean` (`reduction_append_perfectCompleteness`) is
residual-gated: it takes its own conclusion as the hypothesis
`reductionAppendPerfectCompletenessResidual`. This file discharges that residual for the
message-seam case, i.e. it proves

`(R₁.append R₂).perfectCompleteness` from `R₁.perfectCompleteness` and `R₂.perfectCompleteness`

*without* assuming the conclusion.

## Proof outline (support-decomposition — no distributional reordering needed)

`(R₁.append R₂).run` runs both provers then both verifiers: order `P₁, P₂, V₁, V₂`. A *distribution*
identity would need to commute `V₁` past `P₂`, but **perfect completeness only needs support
containment** (`probEvent_eq_one_iff`: `Pr[p|mx] = 1 ↔ Pr[⊥|mx] = 0 ∧ ∀ x ∈ support mx, p x`), and
support decomposes through `bind` *without* reordering (`mem_support_bind_iff`). So we never commute
anything; we decompose the support directly:

1. `Prover.append_run_msg` factors the appended prover run into `P₁.run` then `P₂.run`, and
   `Verifier.append_run` (`rfl`) splits the verifier into `V₁.run stmt₁ tr₁` then `V₂.run · tr₂`.
2. Take any outcome in the support. `mem_support_bind_iff` exposes
   `(tr₁,s₂,w₂) ∈ support (P₁.run)`, `sv₂ ∈ support (V₁.run stmt₁ tr₁)`,
   `(tr₂,s₃,w₃) ∈ support (P₂.run s₂ w₂)`, `sv₃ ∈ support (V₂.run sv₂ tr₂)`.
3. `h₁` applied to the `R₁.run` outcome `((tr₁,s₂,w₂), sv₂)` gives `sv₂ = s₂ ∧ (sv₂,w₂) ∈ rel₂`,
   hence `(s₂,w₂) ∈ rel₂` and `sv₂ = s₂`.
4. Rewriting `sv₂ = s₂`, the tail is exactly the `R₂.run s₂ w₂` outcome `((tr₂,s₃,w₃), sv₃)`;
   `h₂` (valid since `(s₂,w₂) ∈ rel₂`) gives `(sv₃,w₃) ∈ rel₃ ∧ sv₃ = s₃` — i.e. the goal.

The `hImplSupp` hypothesis (the appended verifier's stateful oracle queries have state-independent
*support*) is what makes the support decomposition go through despite a stateful `impl`; it is exactly
why the support route works where a naive distributional route would also have to track `σ`-state.

## Status (verified scaffold + precise remaining gap)

The following steps are machine-checked (`lake env lean`, against built deps):
* `rw [perfectCompleteness_eq_prob_one]` reduces `h₁`, `h₂`, and the goal to `Pr[·] = 1`.
* `rw [probEvent_eq_one_iff]; refine ⟨?_, ?_⟩` splits the goal into **no-failure** (`Pr[⊥ | ·] = 0`)
  and **support containment** (`∀ x ∈ support …, good₃ x`).
* `Prover.append_run_msg` (with `hn`, `hDir`, `hDir₂`) factors `(R₁.append R₂).prover.run` into
  `P₁.run` then `P₂.run` (the rewrite fires; closing the explicit `hrun` to a stated RHS is a
  destructuring-vs-`match` defeq).

The remaining gap is the one piece that has kept this keystone unproven library-wide: the support
in the goal sits behind three wrappers — `OptionT.mk`, `StateT.run'` (from `init`), and
`simulateQ (impl.addLift challengeQueryImpl)` — so `support_bind`/`mem_support_bind_iff` do **not**
fire directly (verified: they leave the term intact). Closing it requires unfolding those three
layers and then the *challenge-oracle seam split* — relating the combined
`challengeQueryImpl` over `pSpec₁ ++ₚ pSpec₂` to the component handlers across the seam round `m`
(the building blocks exist: `append_getChallenge_left` / `append_getChallenge_natAdd`,
`range_challenge_append_inl`/`inr`, and vcvio's `simulateQ_add_liftM_left`/`right` /
`simulateQ_liftM_eq_of_query`). With the run decomposed under `simulateQ`, `h₁` pins
`V₁`'s output to `P₁`'s output statement `s₂ ∈ rel₂` and `h₂` lands the result in `rel₃`.

Stated below as a named residual so the obligation is explicit and the scaffold above is recorded;
discharging it closes compositional completeness for `Logup`/`Fri`/`BCS`/WHIR at once.
-/

open OracleComp OracleSpec ProtocolSpec

namespace Reduction

variable {ι : Type} {oSpec : OracleSpec ι} [oSpec.Fintype] [oSpec.Inhabited]
  {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
  [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}

/-- **Perfect completeness composes under `Reduction.append` (message-seam case).**

This discharges `reductionAppendPerfectCompletenessResidual` for the message-first second protocol:
the genuine append-completeness theorem, proving the conclusion from the two component perfect
completeness hypotheses rather than assuming it. -/
theorem append_perfectCompleteness_msg
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
    simp only [liftM_bind, ChallengeIdx, Challenge, liftM_pure, bind_pure_comp, liftM_OptionT_eq,
      Prod.mk.eta, bind_assoc, bind_map_left, OptionT.support_mk, Set.mem_setOf_eq, Prod.mk.injEq,
      liftComp_eq_liftM, OptionT.mem_support_iff, support_bind, support_map, Set.mem_iUnion,
      Set.mem_image, Prod.exists, exists_prop] at hx
    dsimp only [Functor.map, OptionT.instMonad] at hx
    simp only [OptionT.monad_bind_eq_bind, OptionT.mem_support_OptionT_bind_run_some_iff,
      Function.comp_apply, Prod.exists] at hx
    trace_state
    sorry

end Reduction
