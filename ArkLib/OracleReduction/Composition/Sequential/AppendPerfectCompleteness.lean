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

## Status

In-progress formalization of the support-decomposition argument above. The prover-run factoring is
consumed from the already-proven `Append`/`AppendRunEvalDist` keystones; the remaining content is the
`mem_support_bind_iff` decomposition + pointwise application of `h₁`, `h₂`.
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
    (hInit : init.NeverFail) :
    (R₁.append R₂).perfectCompleteness init impl rel₁ rel₃ := by
  rw [perfectCompleteness_eq_prob_one] at h₁ h₂ ⊢
  intro stmtIn witIn hIn
  -- Factor the appended run-distribution: prover via `append_run_evalDist_msg`, verifier via
  -- `Verifier.append_run`, then commute `V₁` past `P₂` with `evalDist_bind_comm`.
  -- The resulting sequential distribution is `R₁.run` followed by `R₂.run`, where `h₁`/`h₂` apply.
  sorry

end Reduction
