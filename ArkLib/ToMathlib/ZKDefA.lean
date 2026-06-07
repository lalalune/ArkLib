/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.Security.Basic

/-!
  # Brick A (scratch): Honest-Verifier Zero-Knowledge over the in-tree execution semantics

  This scratch file develops the *definition* of (honest-verifier) zero-knowledge for
  `Reduction`s, stated against the existing `Reduction.run` execution semantics and the existing
  probability vocabulary (`evalDist`, `tvDist`, `probEvent`).

  ## Design

  The honest interaction produces, for a given `(stmtIn, witIn)`, a full transcript
  `FullTranscript pSpec` together with the prover/verifier outputs.  We interpret that computation
  (which lives in `OracleComp (oSpec + [pSpec.Challenge]ₒ)`) into `ProbComp` by `simulateQ`-ing the
  shared-oracle implementation `impl` together with the honest challenge sampler
  `challengeQueryImpl`.  Projecting onto the transcript yields the **honest transcript
  distribution** `honestTranscriptDist`, an `OptionT ProbComp (FullTranscript pSpec)`.

  A **transcript simulator** `TranscriptSimulator` produces, from the input statement *alone* (no
  witness), an `OptionT ProbComp (FullTranscript pSpec)`.  This is the natural specialization of the
  in-tree `Reduction.Simulator` structure to the case where we only care about transcript-level
  indistinguishability and have already interpreted the shared oracle.

  Then:
  - `perfectHVZK`: for every `(stmtIn, witIn) ∈ rel`, the simulator's distribution equals the
    honest transcript distribution (as `SPMF`s, i.e. `evalDist` agreement).
  - `statisticalHVZK ε`: the total-variation distance between the two distributions is at most `ε`.

  Perfect HVZK is the `ε = 0` case (`tvDist = 0 ↔ evalDist`-agreement).
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

namespace Reduction

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type}
  {n : ℕ} {pSpec : ProtocolSpec n} [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type}

/-- The **honest transcript distribution** of a reduction on input `(stmtIn, witIn)`: run the
  reduction under the honest challenge sampler `challengeQueryImpl` and the shared-oracle
  implementation `impl` (threaded through ambient state `σ` sampled from `init`), then project onto
  the full transcript.  Lives in `OptionT ProbComp (FullTranscript pSpec)` since the verifier may
  reject (the `OptionT` failure). -/
def honestTranscriptDist
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmtIn : StmtIn) (witIn : WitIn) :
    OptionT ProbComp (FullTranscript pSpec) :=
  OptionT.mk do
    let pImpl : QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp) :=
      impl.addLift challengeQueryImpl
    (simulateQ pImpl
      ((fun result => result.1.1) <$> (reduction.run stmtIn witIn)).run).run' (← init)

/-- A **transcript simulator** for a reduction produces, from the input statement alone (no
  witness, no honest prover), a distribution over full transcripts in `OptionT ProbComp`.

  This is the post-interpretation form of `Reduction.Simulator`: the shared oracle `oSpec` has
  already been interpreted into `ProbComp` (so the simulator may itself sample / program oracles
  internally), and we expose only the transcript-level output, which is exactly what
  zero-knowledge constrains. -/
def TranscriptSimulator (oSpec : OracleSpec ι) (StmtIn : Type) {n : ℕ} (pSpec : ProtocolSpec n) :=
  StmtIn → OptionT ProbComp (FullTranscript pSpec)

/-- A reduction satisfies **perfect honest-verifier zero-knowledge** with respect to a simulator
  `sim` and input relation `rel`, if for every `(stmtIn, witIn) ∈ rel` the simulator's transcript
  distribution agrees with the honest transcript distribution (as sub-probability mass functions). -/
def perfectHVZK
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (rel : Set (StmtIn × WitIn))
    (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (sim : TranscriptSimulator oSpec StmtIn pSpec) : Prop :=
  ∀ stmtIn : StmtIn, ∀ witIn : WitIn, (stmtIn, witIn) ∈ rel →
    evalDist (sim stmtIn) = evalDist (honestTranscriptDist init impl reduction stmtIn witIn)

/-- A reduction satisfies **statistical honest-verifier zero-knowledge** with error `ε ≥ 0` with
  respect to a simulator `sim` and input relation `rel`, if for every `(stmtIn, witIn) ∈ rel` the
  total-variation distance between the simulator's and the honest transcript distributions is at
  most `ε`. -/
def statisticalHVZK
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (rel : Set (StmtIn × WitIn))
    (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (sim : TranscriptSimulator oSpec StmtIn pSpec) (ε : ℝ≥0) : Prop :=
  ∀ stmtIn : StmtIn, ∀ witIn : WitIn, (stmtIn, witIn) ∈ rel →
    tvDist (sim stmtIn) (honestTranscriptDist init impl reduction stmtIn witIn) ≤ (ε : ℝ)

/-- A reduction is **honest-verifier zero-knowledge** (existential form) for relation `rel` if there
  exists a simulator achieving perfect HVZK. -/
def isHVZK
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (rel : Set (StmtIn × WitIn))
    (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) : Prop :=
  ∃ sim : TranscriptSimulator oSpec StmtIn pSpec, perfectHVZK init impl rel reduction sim

/-- Perfect HVZK is exactly statistical HVZK with error `0`. -/
theorem perfectHVZK_iff_statisticalHVZK_zero
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (rel : Set (StmtIn × WitIn))
    (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (sim : TranscriptSimulator oSpec StmtIn pSpec) :
    perfectHVZK init impl rel reduction sim ↔
      statisticalHVZK init impl rel reduction sim 0 := by
  unfold perfectHVZK statisticalHVZK
  constructor
  · intro h stmtIn witIn hMem
    have heq := h stmtIn witIn hMem
    simp only [NNReal.coe_zero]
    rw [show (0 : ℝ) = tvDist (honestTranscriptDist init impl reduction stmtIn witIn)
        (honestTranscriptDist init impl reduction stmtIn witIn) from (tvDist_self _).symm]
    rw [tvDist, tvDist, heq]
  · intro h stmtIn witIn hMem
    have := h stmtIn witIn hMem
    simp only [NNReal.coe_zero] at this
    have hle : tvDist (sim stmtIn) (honestTranscriptDist init impl reduction stmtIn witIn) ≤ 0 :=
      this
    have hge : 0 ≤ tvDist (sim stmtIn) (honestTranscriptDist init impl reduction stmtIn witIn) :=
      tvDist_nonneg _ _
    have hzero : tvDist (sim stmtIn) (honestTranscriptDist init impl reduction stmtIn witIn) = 0 :=
      le_antisymm hle hge
    rw [tvDist_eq_zero_iff] at hzero
    exact hzero

/-- Perfect HVZK implies statistical HVZK with any error `ε ≥ 0`. -/
theorem perfectHVZK.statisticalHVZK
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set (StmtIn × WitIn)}
    {reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec}
    {sim : TranscriptSimulator oSpec StmtIn pSpec}
    (h : perfectHVZK init impl rel reduction sim) (ε : ℝ≥0) :
    statisticalHVZK init impl rel reduction sim ε := by
  intro stmtIn witIn hMem
  have heq := h stmtIn witIn hMem
  have hzero :
      tvDist (sim stmtIn) (honestTranscriptDist init impl reduction stmtIn witIn) = 0 := by
    rw [tvDist_eq_zero_iff]; exact heq
  rw [hzero]
  positivity

end Reduction
