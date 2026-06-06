/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Defs
import ArkLib.OracleReduction.Security.Basic

/-!
# Theorem about completeness

This file contains the theorem that duplex sponge Fiat-Shamir is complete, assuming the underlying
interactive protocol is complete.

(do we even have to go through basic Fiat-Shamir? any complication with handling completeness
error?)
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

namespace Verifier

section Execution

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn StmtOut : Type}
  [VCVCompatible StmtIn]
  {U : Type} [SpongeUnit U] [SpongeSize]
  [HasMessageSize pSpec] [∀ i, Serialize (pSpec.Message i) (Vector U (messageSize i))]
  [HasChallengeSize pSpec] [∀ i, Deserialize (pSpec.Challenge i) (Vector U (challengeSize i))]

/-- The transcript type of the one-message non-interactive proof produced by the unsalted DSFS
transform. -/
abbrev DuplexSpongeProofTranscript :=
  FullTranscript ⟨!v[Direction.P_to_V], !v[pSpec.Messages]⟩

/-- The transcript type of the one-message non-interactive proof produced by the salted DSFS
transform. -/
abbrev DuplexSpongeSaltedProofTranscript (δ : Nat) :=
  FullTranscript
    ⟨!v[Direction.P_to_V],
      !v[ProtocolSpec.Messages.SaltedProof (pSpec := pSpec) (U := U) δ]⟩

/-- Expanding the DSFS verifier shows that it verifies by re-deriving the transcript from the proof
messages via the duplex sponge. -/
@[simp]
theorem duplexSpongeFiatShamir_verify_eq
    (V : Verifier oSpec StmtIn StmtOut pSpec) (stmtIn : StmtIn)
    (proof : DuplexSpongeProofTranscript (pSpec := pSpec)) :
    (V.duplexSpongeFiatShamir (U := U)).verify stmtIn proof =
      (do
      let messages : pSpec.Messages := proof 0
      let ⟨_, transcript⟩ ← messages.deriveTranscriptDSFS (oSpec := oSpec) (U := U) stmtIn
      let v ← (V.verify stmtIn transcript).run
      v.getM) := by
  rfl

/-- The salted DSFS verifier is the same verifier-side computation, with an initial salt-absorb
step before transcript derivation. -/
@[simp]
theorem duplexSpongeFiatShamirSalted_verify_eq {δ : Nat}
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (stmtIn : StmtIn)
    (proof : DuplexSpongeSaltedProofTranscript (pSpec := pSpec) (U := U) δ) :
    (V.duplexSpongeFiatShamirSalted (U := U)).verify stmtIn proof =
      (do
      let ⟨salt, messages⟩ :
          ProtocolSpec.Messages.SaltedProof (pSpec := pSpec) (U := U) δ := proof 0
      let ⟨_, transcript⟩ ←
        messages.deriveTranscriptDSFSSalted (oSpec := oSpec) (U := U) stmtIn salt
      let v ← (V.verify stmtIn transcript).run
      v.getM) := by
  rfl

end Execution

end Verifier

namespace Reduction

section Execution

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  {U : Type} [SpongeUnit U] [SpongeSize]
  [HasMessageSize pSpec] [∀ i, Serialize (pSpec.Message i) (Vector U (messageSize i))]
  [HasChallengeSize pSpec] [∀ i, Deserialize (pSpec.Challenge i) (Vector U (challengeSize i))]

/-- The explicit honest execution underlying the unsalted DSFS transform. This packages the honest
prover's DSFS-generated proof together with the verifier's acceptance check on that proof. -/
def duplexSpongeFiatShamirHonestRun
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmtIn : StmtIn) (witIn : WitIn) :
    OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (Verifier.DuplexSpongeProofTranscript (pSpec := pSpec) ×
        (StmtOut × WitOut) × Option StmtOut) := do
  let state := R.prover.input (stmtIn, witIn)
  let ⟨messages, _, state⟩ ← R.prover.runToRoundDSFS (U := U) (Fin.last n) stmtIn state
  let ctxOut ← (R.prover.output state).liftComp _
  let proof : Verifier.DuplexSpongeProofTranscript (pSpec := pSpec) := fun
    | ⟨0, _⟩ => messages
  let stmtOut ← ((R.verifier.duplexSpongeFiatShamir (U := U)).run stmtIn proof).run
  return ⟨proof, ctxOut, stmtOut⟩

/-- The explicit honest execution underlying the salted DSFS transform. -/
def duplexSpongeFiatShamirSaltedHonestRun {δ : Nat}
    (sampleSalt : OracleComp oSpec (Vector U δ))
    -- TODO: how to restrict that this is uniform salts sampling?
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmtIn : StmtIn) (witIn : WitIn) :
    OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (Verifier.DuplexSpongeSaltedProofTranscript (pSpec := pSpec) (U := U) δ ×
        (StmtOut × WitOut) × Option StmtOut) := do
  let salt ← sampleSalt.liftComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
  let state := R.prover.input (stmtIn, witIn)
  let ⟨messages, _, state⟩ ←
    R.prover.runToRoundDSFSSalted (U := U) (i := Fin.last n) stmtIn salt state
  let ctxOut ← (R.prover.output state).liftComp _
  let proof : Verifier.DuplexSpongeSaltedProofTranscript (pSpec := pSpec) (U := U) δ := fun
    | ⟨0, _⟩ => (salt, messages)
  let stmtOut ← ((R.verifier.duplexSpongeFiatShamirSalted (U := U)).run stmtIn proof).run
  return ⟨proof, ctxOut, stmtOut⟩

end Execution

section Completeness

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [∀ i, SampleableType (pSpec.Challenge i)]
  {U : Type} [SpongeUnit U] [SpongeSize]
  [HasMessageSize pSpec] [∀ i, Serialize (pSpec.Message i) (Vector U (messageSize i))]
  [HasChallengeSize pSpec] [∀ i, Deserialize (pSpec.Challenge i) (Vector U (challengeSize i))]

/-- The unsalted DSFS honest execution packaged in the generic `completenessFromRun` format. -/
def duplexSpongeFiatShamirHonestExecution
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmtIn : StmtIn) (witIn : WitIn) :
    OptionT (OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U))
      ((Verifier.DuplexSpongeProofTranscript (pSpec := pSpec) × StmtOut × WitOut) ×
        StmtOut) := do
  let ⟨proof, ⟨prvStmtOut, witOut⟩, stmtOut?⟩ ←
    R.duplexSpongeFiatShamirHonestRun (U := U) stmtIn witIn
  let stmtOut ← OptionT.mk (pure stmtOut?)
  return ⟨⟨proof, prvStmtOut, witOut⟩, stmtOut⟩

/-- The salted DSFS honest execution packaged in the generic `completenessFromRun` format. -/
def duplexSpongeFiatShamirSaltedHonestExecution {δ : Nat}
    (sampleSalt : OracleComp oSpec (Vector U δ))
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmtIn : StmtIn) (witIn : WitIn) :
    OptionT (OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U))
      ((Verifier.DuplexSpongeSaltedProofTranscript (pSpec := pSpec) (U := U) δ ×
          StmtOut × WitOut) × StmtOut) := do
  let ⟨proof, ⟨prvStmtOut, witOut⟩, stmtOut?⟩ ←
    R.duplexSpongeFiatShamirSaltedHonestRun (U := U) sampleSalt stmtIn witIn
  let stmtOut ← OptionT.mk (pure stmtOut?)
  return ⟨⟨proof, prvStmtOut, witOut⟩, stmtOut⟩

/-- The transformed unsalted DSFS run is the lifted explicit honest execution.

The lift is the canonical one-step subspec lift `liftComp` of the honest execution's `.run` into the
reduction's run oracle spec `oSpec + dsc + [FSspec.Challenge]ₒ`; pinning it (rather than relying on
`MonadLiftT` synthesis, which may route through the associativity-reassociating path
`oSpec + dsc → oSpec + (dsc + [c]) → oSpec + dsc + [c]`) keeps this named residual unambiguous. -/
def duplexSpongeFiatShamir_run_eq_honestExecution
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmtIn : StmtIn) (witIn : WitIn) :
    Prop :=
    (R.duplexSpongeFiatShamir (U := U)).run stmtIn witIn =
      OptionT.mk (OracleComp.liftComp
        (R.duplexSpongeFiatShamirHonestExecution (U := U) stmtIn witIn).run _)


/-- The transformed salted DSFS run is the lifted explicit honest execution. -/
def duplexSpongeFiatShamirSalted_run_eq_honestExecution {δ : Nat}
    (sampleSalt : OracleComp oSpec (Vector U δ))
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmtIn : StmtIn) (witIn : WitIn) :
    Prop :=
    (R.duplexSpongeFiatShamirSalted (U := U) sampleSalt).run stmtIn witIn =
      liftM (R.duplexSpongeFiatShamirSaltedHonestExecution (U := U) sampleSalt stmtIn witIn)

/-- Completeness of the unsalted DSFS transform is equivalent to the explicit honest execution
packaged via `Reduction.duplexSpongeFiatShamirHonestExecution`. -/
def duplexSpongeFiatShamir_completeness_unroll
    {σ : Type}
    (init : ProbComp σ)
    (impl : QueryImpl (oSpec + duplexSpongeChallengeOracle StmtIn U) (StateT σ ProbComp))
    (relIn : Set (StmtIn × WitIn))
    (relOut : Set (StmtOut × WitOut))
    (completenessError : ℝ≥0)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) :
    Prop :=
    (R.duplexSpongeFiatShamir (U := U)).completeness init impl relIn relOut completenessError ↔
      Reduction.completenessFromRun init impl relIn relOut
        (R.duplexSpongeFiatShamirHonestExecution (U := U)) completenessError

/-- Completeness of the salted DSFS transform is equivalent to the explicit honest execution
packaged via `Reduction.duplexSpongeFiatShamirSaltedHonestExecution`. -/
def duplexSpongeFiatShamirSalted_completeness_unroll {δ : Nat}
    {σ : Type}
    (init : ProbComp σ)
    (impl : QueryImpl (oSpec + duplexSpongeChallengeOracle StmtIn U) (StateT σ ProbComp))
    (sampleSalt : OracleComp oSpec (Vector U δ))
    (relIn : Set (StmtIn × WitIn))
    (relOut : Set (StmtOut × WitOut))
    (completenessError : ℝ≥0)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) :
    Prop :=
    (R.duplexSpongeFiatShamirSalted (U := U) sampleSalt).completeness
      init impl relIn relOut completenessError ↔
      Reduction.completenessFromRun init impl relIn relOut
        (R.duplexSpongeFiatShamirSaltedHonestExecution (U := U) sampleSalt)
        completenessError

/-- The `NonInteractiveReduction` produced by the DSFS transform is prover-first: its single round
is a `P_to_V` message. -/
local instance dsfsProverOnly :
    ProtocolSpec.ProverOnly ⟨!v[Direction.P_to_V], !v[pSpec.Messages]⟩ where
  prover_first' := by simp

/-- **Reduction of `duplexSpongeFiatShamir_completeness_unroll` to the run-equality residual.**

Given the per-input run-equality `duplexSpongeFiatShamir_run_eq_honestExecution` (that the
non-interactive DSFS reduction's `run` is the lifted explicit honest execution), completeness of the
unsalted DSFS transform is *definitionally* the generic `completenessFromRun` predicate over the
honest execution.

This is the proven `_of_residual` brick: it discharges the `↔` in
`duplexSpongeFiatShamir_completeness_unroll` outright, shrinking the open surface to the single named
run-equality residual.

The collapse of the outer (empty) Fiat-Shamir challenge oracle implementation is handled by
`simulateQ_add_run_liftM_left`: the lifted honest execution never queries that oracle, so
`simulateQ (impl + challengeQueryImpl) (liftM honest).run = simulateQ impl honest.run`. -/
theorem duplexSpongeFiatShamir_completeness_unroll_of_run_eq
    {σ : Type}
    (init : ProbComp σ)
    (impl : QueryImpl (oSpec + duplexSpongeChallengeOracle StmtIn U) (StateT σ ProbComp))
    (relIn : Set (StmtIn × WitIn))
    (relOut : Set (StmtOut × WitOut))
    (completenessError : ℝ≥0)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hRun : ∀ stmtIn witIn,
      duplexSpongeFiatShamir_run_eq_honestExecution (U := U) R stmtIn witIn) :
    duplexSpongeFiatShamir_completeness_unroll (U := U)
      init impl relIn relOut completenessError R := by
  unfold duplexSpongeFiatShamir_completeness_unroll
  rw [Reduction.completeness_iff_completenessFromRun]
  unfold Reduction.completenessFromRun
  simp only [duplexSpongeFiatShamir_run_eq_honestExecution] at hRun
  refine forall_congr' fun stmtIn => forall_congr' fun witIn => ?_
  refine imp_congr_right fun _ => ?_
  -- The two probability expressions agree pointwise: rewrite the DSFS run as the lifted honest
  -- execution, then collapse the outer empty challenge oracle implementation. The collapse uses
  -- `simulateQ_add_run_liftM_left`: the lifted honest execution never queries the (empty) outer
  -- Fiat-Shamir challenge oracle.
  have hcollapse :
      simulateQ (QueryImpl.addLift impl challengeQueryImpl)
          ((R.duplexSpongeFiatShamir (U := U)).run stmtIn witIn).run =
        simulateQ impl
          (R.duplexSpongeFiatShamirHonestExecution (U := U) stmtIn witIn).run := by
    rw [hRun stmtIn witIn]
    rw [QueryImpl.addLift_def, QueryImpl.liftTarget_self]
    -- The run-equality residual is stated with the canonical one-step subspec lift `liftComp` of the
    -- honest execution's `.run`, so the appended (never-queried) challenge oracle implementation
    -- collapses directly via `simulateQ_add_liftComp_left`.
    rw [OptionT.run_mk]
    exact QueryImpl.simulateQ_add_liftComp_left impl
      (QueryImpl.liftTarget (StateT σ ProbComp)
        (challengeQueryImpl (pSpec := ⟨!v[Direction.P_to_V], !v[pSpec.Messages]⟩)))
      (R.duplexSpongeFiatShamirHonestExecution (U := U) stmtIn witIn).run
  rw [hcollapse]

/-- **Reduction of `duplexSpongeFiatShamirSalted_completeness_unroll` to the run-equality
residual.** The salted analogue of `duplexSpongeFiatShamir_completeness_unroll_of_run_eq`. -/
theorem duplexSpongeFiatShamirSalted_completeness_unroll_of_run_eq {δ : Nat}
    {σ : Type}
    (init : ProbComp σ)
    (impl : QueryImpl (oSpec + duplexSpongeChallengeOracle StmtIn U) (StateT σ ProbComp))
    (sampleSalt : OracleComp oSpec (Vector U δ))
    (relIn : Set (StmtIn × WitIn))
    (relOut : Set (StmtOut × WitOut))
    (completenessError : ℝ≥0)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hRun : ∀ stmtIn witIn,
      duplexSpongeFiatShamirSalted_run_eq_honestExecution (U := U) sampleSalt R stmtIn witIn) :
    duplexSpongeFiatShamirSalted_completeness_unroll (U := U)
      init impl sampleSalt relIn relOut completenessError R := by
  unfold duplexSpongeFiatShamirSalted_completeness_unroll
  rw [Reduction.completeness_iff_completenessFromRun]
  unfold Reduction.completenessFromRun
  simp only [duplexSpongeFiatShamirSalted_run_eq_honestExecution] at hRun
  refine forall_congr' fun stmtIn => forall_congr' fun witIn => ?_
  refine imp_congr_right fun _ => ?_
  have hcollapse :
      simulateQ (QueryImpl.addLift impl challengeQueryImpl)
          ((R.duplexSpongeFiatShamirSalted (U := U) sampleSalt).run stmtIn witIn).run =
        simulateQ impl
          (R.duplexSpongeFiatShamirSaltedHonestExecution (U := U)
            sampleSalt stmtIn witIn).run := by
    rw [hRun stmtIn witIn, QueryImpl.addLift_def, QueryImpl.liftTarget_self]
    convert simulateQ_add_run_liftM_left impl
      (QueryImpl.liftTarget (StateT σ ProbComp)
        (challengeQueryImpl
          (pSpec := ⟨!v[Direction.P_to_V],
            !v[ProtocolSpec.Messages.SaltedProof (pSpec := pSpec) (U := U) δ]⟩)))
      (R.duplexSpongeFiatShamirSaltedHonestExecution (U := U) sampleSalt stmtIn witIn) using 3
    rfl
  rw [hcollapse]

end Completeness

end Reduction
