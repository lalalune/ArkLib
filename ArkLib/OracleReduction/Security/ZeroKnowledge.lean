/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.Security.Basic

/-!
  # Honest-Verifier Zero-Knowledge for Reductions

  This file defines transcript-level honest-verifier zero-knowledge for `Reduction`s, stated against
  the existing `Reduction.run` execution semantics and the existing probability vocabulary
  (`evalDist`, `tvDist`, `probEvent`).

  The honest interaction produces, for a given `(stmtIn, witIn)`, a full transcript
  `FullTranscript pSpec` together with prover and verifier outputs. We interpret that computation
  into `ProbComp` by `simulateQ`-ing the shared-oracle implementation `impl` together with the
  honest challenge sampler `challengeQueryImpl`, then project onto the transcript.

  A `TranscriptSimulator` produces a transcript distribution from the input statement alone. The
  predicates below compare that simulator distribution with the honest transcript distribution:

  - `perfectHVZK`: equality of `evalDist`s for every related statement-witness pair.
  - `statisticalHVZK`: total-variation distance at most `ε`.

  The file also records the zero-round identity reduction as the first concrete perfect-HVZK
  instance.
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

namespace Reduction

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type}
  {n : ℕ} {pSpec : ProtocolSpec n} [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type}

section Definitions

/-- The honest transcript distribution of a reduction on input `(stmtIn, witIn)`: run the reduction
  with honest verifier challenges and the shared-oracle implementation `impl`, then project onto the
  full transcript. The computation lives in `OptionT ProbComp` because the reduction execution may
  fail. -/
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

/-- A transcript simulator produces, from the input statement alone, a distribution over full
  transcripts. This is the post-interpretation transcript-level form of `Reduction.Simulator`. -/
def TranscriptSimulator (_oSpec : OracleSpec ι) (StmtIn : Type) {n : ℕ}
    (pSpec : ProtocolSpec n) :=
  StmtIn → OptionT ProbComp (FullTranscript pSpec)

/-- A reduction satisfies perfect honest-verifier zero-knowledge with respect to a simulator and
  relation `rel` if the simulator's transcript distribution agrees with the honest transcript
  distribution for every related statement-witness pair. -/
def perfectHVZK
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (rel : Set (StmtIn × WitIn))
    (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (sim : TranscriptSimulator oSpec StmtIn pSpec) : Prop :=
  ∀ stmtIn : StmtIn, ∀ witIn : WitIn, (stmtIn, witIn) ∈ rel →
    evalDist (sim stmtIn) = evalDist (honestTranscriptDist init impl reduction stmtIn witIn)

/-- A reduction satisfies statistical honest-verifier zero-knowledge with error `ε` if the
  simulator's transcript distribution is within total-variation distance `ε` of the honest
  transcript distribution for every related statement-witness pair. -/
def statisticalHVZK
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (rel : Set (StmtIn × WitIn))
    (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (sim : TranscriptSimulator oSpec StmtIn pSpec) (ε : ℝ≥0) : Prop :=
  ∀ stmtIn : StmtIn, ∀ witIn : WitIn, (stmtIn, witIn) ∈ rel →
    tvDist (sim stmtIn) (honestTranscriptDist init impl reduction stmtIn witIn) ≤ (ε : ℝ)

/-- A reduction is honest-verifier zero-knowledge for relation `rel` if some simulator achieves
  perfect HVZK. -/
def isHVZK
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (rel : Set (StmtIn × WitIn))
    (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) : Prop :=
  ∃ sim : TranscriptSimulator oSpec StmtIn pSpec, perfectHVZK init impl rel reduction sim

end Definitions

section BasicLemmas

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

/-- Perfect HVZK implies statistical HVZK with any error `ε`. -/
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
    rw [tvDist_eq_zero_iff]
    exact heq
  rw [hzero]
  positivity

end BasicLemmas

section Identity

variable {StmtIn WitIn : Type}

/-- The simulator for the zero-round identity reduction: ignore the statement and emit the unique
  empty transcript. -/
def idTranscriptSimulator :
    TranscriptSimulator oSpec StmtIn (!p[] : ProtocolSpec 0) :=
  fun _ => pure default

/-- The honest transcript distribution of the zero-round identity reduction is distributionally
  equal to `pure default`. The computation still samples and discards the ambient initialization
  state, so this is intentionally an `evalDist` equality rather than a raw term equality. -/
theorem honestTranscriptDist_id_evalDist
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (stmtIn : StmtIn) (witIn : WitIn) :
    evalDist (honestTranscriptDist init impl
        (Reduction.id : Reduction oSpec StmtIn WitIn StmtIn WitIn !p[]) stmtIn witIn) =
      evalDist (pure default : OptionT ProbComp (FullTranscript !p[])) := by
  apply evalDist_ext
  intro transcript
  classical
  unfold honestTranscriptDist
  simp only [Reduction.id_run, map_pure, OptionT.run_pure, simulateQ_pure, StateT.run'_eq,
    StateT.run_pure, bind_pure_comp]
  rw [OptionT.probOutput_eq, OptionT.probOutput_eq]
  simp [probOutput_map_const, HasEvalPMF.probFailure_eq_zero]

/-- The zero-round identity reduction satisfies perfect honest-verifier zero-knowledge for any
  input relation. -/
theorem id_perfectHVZK
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (rel : Set (StmtIn × WitIn)) :
    perfectHVZK init impl rel
      (Reduction.id : Reduction oSpec StmtIn WitIn StmtIn WitIn !p[])
      idTranscriptSimulator := by
  intro stmtIn witIn _
  exact (honestTranscriptDist_id_evalDist init impl stmtIn witIn).symm

/-- The zero-round identity reduction is honest-verifier zero-knowledge for any relation. -/
theorem id_isHVZK
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (rel : Set (StmtIn × WitIn)) :
    isHVZK init impl rel
      (Reduction.id : Reduction oSpec StmtIn WitIn StmtIn WitIn !p[]) :=
  ⟨idTranscriptSimulator, id_perfectHVZK init impl rel⟩

end Identity

#print axioms honestTranscriptDist
#print axioms TranscriptSimulator
#print axioms perfectHVZK_iff_statisticalHVZK_zero
#print axioms perfectHVZK.statisticalHVZK
#print axioms honestTranscriptDist_id_evalDist
#print axioms id_perfectHVZK
#print axioms id_isHVZK

end Reduction
