/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArkLib.ProofSystem.Sumcheck.Spec.SingleRoundFlipImp

/-! # Discharging `hIndep` for the single-round sum-check knowledge state function (#13)

`SingleRoundFlipImp.lean` reduced the all-prover-witness-type per-round knowledge-flip bound
(`hKnowFlip`, the last residual of the RBR-knowledge ⇒ RBR-plain soundness weakening) to the single
named hypothesis `hIndep : TranscriptIndependent kSF` — transcript-independence of the single-round
sum-check knowledge state function. That fact was left as a hypothesis only because
`Simple.simpleKnowledgeStateFunction` was `private` and so could not be named from a downstream
file.

It is now public, and its transcript-independence is immediate: its `toFun` is
`fun _ stmtIn _ _ => (stmtIn, ()) ∈ inputRelation R deg D`, which ignores the message index,
transcript, and mid-witness. So the statement-predicate witness is the input-relation membership
and the per-round equivalence is `Iff.rfl`. This closes `hIndep`, hence `hKnowFlip`, hence the
per-round plain round-by-round soundness of the single-round sum-check oracle verifier. -/

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

namespace Sumcheck.Spec.SingleRound.Simple

variable {R : Type} [CommSemiring R] [DecidableEq R] [SampleableType R] {deg : ℕ} {m : ℕ}
  {D : Fin m ↪ R} {ι : Type} {oSpec : OracleSpec ι}

/-- **`hIndep`, discharged.** The single-round sum-check knowledge state function is
transcript-independent: its `toFun` returns only whether the statement lies in the input relation,
ignoring the message index, transcript, and intermediate witness. -/
theorem simpleKnowledgeStateFunction_transcriptIndependent {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp)) :
    KnowFlip.TranscriptIndependent
      (simpleKnowledgeStateFunction (init := init) (impl := impl) R deg D oSpec) :=
  ⟨fun stmtIn => (stmtIn, ()) ∈ inputRelation R deg D, fun _ _ _ _ => Iff.rfl⟩

end Sumcheck.Spec.SingleRound.Simple
