/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.Security.Basic

/-!
# Issue #112 scratch: ZK Concrete Simulator Preservation

This file isolates the mathematical kernels of the ZK Concrete Simulator Preservation.
The core mathematical property states that for specific concrete zero-knowledge reductions
(such as polynomial commitments or sumcheck), there exists an explicit simulator `S` whose
output distribution is identical to the true prover-verifier transcript distribution, 
meaning the reduction preserves the HVZK property.
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace ProximityGap
namespace Issue112

open OracleComp OracleSpec ProtocolSpec
open scoped ProbabilityTheory

/-- Public transcript data exposed by an oracle-reduction run for simulator comparison. -/
abbrev ZKConcretePublicView {ιₛₒ : Type} (OStmtOut : ιₛₒ → Type)
    {n : ℕ} (pSpec : ProtocolSpec n) (StmtOut : Type) : Type :=
  pSpec.FullTranscript × StmtOut × (∀ i, OStmtOut i)

/-- Project the full oracle-reduction run to the public transcript/output view. -/
def oracleReductionPublicRun
    {ι : Type} {oSpec : OracleSpec ι}
    {StmtIn : Type} {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} {WitIn : Type}
    {StmtOut : Type} {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type} {WitOut : Type}
    {n : ℕ} {pSpec : ProtocolSpec n}
    [∀ i, OracleInterface (OStmtIn i)] [∀ i, OracleInterface (pSpec.Message i)]
    (stmtIn : StmtIn) (oStmtIn : ∀ i, OStmtIn i) (witIn : WitIn)
    (R : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec) :
    OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ))
      (ZKConcretePublicView OStmtOut pSpec StmtOut) := do
  let out ← OracleReduction.run stmtIn oStmtIn witIn R
  let ⟨⟨transcript, _proverOut, _witOut⟩, verifierOut⟩ := out
  return (transcript, verifierOut.1, verifierOut.2)

/-- **Explicit Simulator Construction Kernel.**
This states the existence of a simulator for the `isHVZK` definition. The mathematics here
is isolating the simulator's explicit construction and bounding the statistical distance
(which for perfect HVZK is exactly 0) between the simulator's output and the true transcript.
This isolates the `zk_concrete_simulator_residual` mathematics in a pure algebraic form.
-/
def ZKConcreteSimulatorKernel
    {ι : Type} {oSpec : OracleSpec ι}
    {StmtIn : Type} {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} {WitIn : Type}
    {StmtOut : Type} {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type} {WitOut : Type}
    {n : ℕ} {pSpec : ProtocolSpec n}
    [∀ i, OracleInterface (OStmtIn i)] [∀ i, OracleInterface (pSpec.Message i)]
    [∀ i, SampleableType (pSpec.Challenge i)]
    {σ : Type}
    (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (rel : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn))
    (R : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec) : Prop :=
  ∃ (simulator : StmtIn → (∀ i, OStmtIn i) →
      OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ))
        (ZKConcretePublicView OStmtOut pSpec StmtOut)),
    ∀ stmtIn oStmtIn witIn, (((stmtIn, oStmtIn), witIn) ∈ rel) →
      -- The simulated transcript distribution equals the real execution distribution
      (init >>= fun s =>
          (simulateQ
            (QueryImpl.addLift impl (challengeQueryImpl (pSpec := pSpec)) :
              QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp))
            (simulator stmtIn oStmtIn).run).run' s) =
        (init >>= fun s =>
          (simulateQ
            (QueryImpl.addLift impl (challengeQueryImpl (pSpec := pSpec)) :
              QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp))
            (oracleReductionPublicRun stmtIn oStmtIn witIn R).run).run' s)

end Issue112
end ProximityGap
