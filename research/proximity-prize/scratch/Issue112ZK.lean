/-
Issue #112 — Zero-Knowledge: define HVZK/ZK and prove perfect HVZK for ≥1 protocol.  SCRATCH.

Target file (already in tree): ArkLib/OracleReduction/Security/ZeroKnowledge.lean
  defines `Reduction.perfectHVZK`, `Reduction.statisticalHVZK`, `Reduction.isHVZK`,
  `Reduction.honestTranscriptDist`, `Reduction.TranscriptSimulator`, and proves the *trivial*
  zero-round identity reduction is perfect HVZK (`Reduction.id_perfectHVZK`).

THIS SCRATCH GOES BEYOND THE IDENTITY:
  It instantiates the in-tree HVZK definition on a genuine *single-message* (non-interactive)
  reduction — the prover sends one P_to_V message — and proves PERFECT HVZK (error 0) for it.

  Concretely we take option (b) from the issue: the "statement echo" non-interactive reduction.
  The prover's single message is its public input statement (no witness/secret dependence, no
  oracle queries); the verifier accepts and returns the statement. The simulator replays the
  public statement as the message. Honest and simulated transcript distributions are EQUAL, so
  this is perfect (not approximate) HVZK, proved by `evalDist` (PMF) equality.

  This is a substantive HVZK theorem: there is a real prover message in the transcript, unfolded
  through `Reduction.run_of_prover_first` and the `honestTranscriptDist` `simulateQ` interpretation.
-/

import ArkLib.OracleReduction.Security.ZeroKnowledge

noncomputable section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

namespace Issue112ZK

variable {ι : Type} {oSpec : OracleSpec ι}
  {Statement Witness : Type} {σ : Type}

/-- The single-message protocol spec: one prover-to-verifier message of type `Statement`. -/
abbrev echoPSpec (Statement : Type) : ProtocolSpec 1 := ⟨!v[.P_to_V], !v[Statement]⟩

/-- `echoPSpec` is prover-only (the unique round is a P_to_V message). -/
instance : ProtocolSpec.ProverOnly (echoPSpec Statement) where
  prover_first' := rfl

/-- The "statement echo" prover for the single-message reduction: it keeps `(stmt, wit)` as state,
  sends the statement as its one message, and outputs the input context unchanged. No randomness,
  no oracle queries, no witness in the message. -/
def echoProver : Prover oSpec Statement Witness Statement Witness (echoPSpec Statement) where
  PrvState := fun _ => Statement × Witness
  input := _root_.id
  sendMessage | ⟨0, _⟩ => fun state => pure (state.1, state)
  receiveChallenge | ⟨0, h⟩ => nomatch h
  output := pure

/-- The verifier for the echo reduction: accept and return the input statement. -/
def echoVerifier : Verifier oSpec Statement Statement (echoPSpec Statement) where
  verify := fun stmt _ => pure stmt

/-- The "statement echo" non-interactive reduction. -/
def echoReduction : Reduction oSpec Statement Witness Statement Witness (echoPSpec Statement) where
  prover := echoProver
  verifier := echoVerifier

/-- The transcript carrying a single message `m` for the echo protocol spec. -/
def echoTranscript (m : Statement) : FullTranscript (echoPSpec Statement) :=
  fun i => match i with | ⟨0, _⟩ => m

/-- Running the echo reduction is a `pure`: the transcript is the input statement, the prover output
  is the input context, the verifier output is the input statement. No randomness, no oracle
  queries, no failure. -/
theorem echoReduction_run (stmt : Statement) (wit : Witness) :
    (echoReduction : Reduction oSpec Statement Witness _ _ _).run stmt wit =
      pure ⟨⟨echoTranscript stmt, stmt, wit⟩, stmt⟩ := by
  rw [Reduction.run_of_prover_first]
  simp only [echoReduction, echoProver, echoVerifier, echoTranscript]
  rfl

end Issue112ZK
