/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.Security.ZeroKnowledge

/-!
  # Honest-Verifier Zero-Knowledge for Oracle Reductions

  This module exposes the transcript-level HVZK predicates from
  `ArkLib.OracleReduction.Security.ZeroKnowledge` at the `OracleReduction` API boundary. As with
  completeness and soundness, the oracle-reduction predicate delegates to the associated
  non-oracle `Reduction` obtained by `OracleReduction.toReduction`.
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

namespace OracleReduction

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn : Type} {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} {WitIn : Type}
  {StmtOut : Type} {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type} {WitOut : Type}
  {n : ℕ} {pSpec : ProtocolSpec n}
  [∀ i, OracleInterface (OStmtIn i)] [∀ i, OracleInterface (pSpec.Message i)]
  [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type}

section Definitions

/-- Transcript simulators for oracle reductions are simulators for the associated non-oracle
  reduction, whose input statement packages the public statement together with the input oracle
  statements. -/
abbrev TranscriptSimulator
    (oSpec : OracleSpec ι) (StmtIn : Type) {ιₛᵢ : Type} (OStmtIn : ιₛᵢ → Type)
    {n : ℕ} (pSpec : ProtocolSpec n) :=
  Reduction.TranscriptSimulator oSpec (StmtIn × (∀ i, OStmtIn i)) pSpec

/-- Perfect HVZK for an oracle reduction, delegated through `OracleReduction.toReduction`. -/
def perfectHVZK
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (rel : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn))
    (oracleReduction :
      OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec)
    (sim : TranscriptSimulator oSpec StmtIn OStmtIn pSpec) : Prop :=
  Reduction.perfectHVZK init impl rel oracleReduction.toReduction sim

/-- Statistical HVZK for an oracle reduction, delegated through `OracleReduction.toReduction`. -/
def statisticalHVZK
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (rel : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn))
    (oracleReduction :
      OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec)
    (sim : TranscriptSimulator oSpec StmtIn OStmtIn pSpec) (ε : ℝ≥0) : Prop :=
  Reduction.statisticalHVZK init impl rel oracleReduction.toReduction sim ε

/-- Existential perfect HVZK for an oracle reduction. -/
def isHVZK
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (rel : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn))
    (oracleReduction :
      OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec) : Prop :=
  ∃ sim : TranscriptSimulator oSpec StmtIn OStmtIn pSpec,
    perfectHVZK init impl rel oracleReduction sim

/-- Existential statistical HVZK for an oracle reduction. -/
def isStatHVZK
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (rel : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn))
    (oracleReduction :
      OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec)
    (ε : ℝ≥0) : Prop :=
  ∃ sim : TranscriptSimulator oSpec StmtIn OStmtIn pSpec,
    statisticalHVZK init impl rel oracleReduction sim ε

end Definitions

section Identity

variable {Statement : Type} {ιₛ : Type} {OStatement : ιₛ → Type} {Witness : Type}
  [∀ i, OracleInterface (OStatement i)]

/-- The zero-round identity oracle reduction is perfect HVZK for any oracle-input relation. -/
theorem id_perfectHVZK
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (rel : Set ((Statement × (∀ i, OStatement i)) × Witness)) :
    perfectHVZK init impl rel
      (OracleReduction.id :
        OracleReduction oSpec Statement OStatement Witness Statement OStatement Witness !p[])
      Reduction.idTranscriptSimulator := by
  unfold perfectHVZK
  simpa [OracleReduction.id_toReduction] using
    (Reduction.id_perfectHVZK (oSpec := oSpec) (StmtIn := Statement × (∀ i, OStatement i))
      (WitIn := Witness) (σ := σ) init impl rel)

/-- The zero-round identity oracle reduction is statistical HVZK for any oracle-input relation and
  any error bound. -/
theorem id_statisticalHVZK
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (rel : Set ((Statement × (∀ i, OStatement i)) × Witness)) (ε : ℝ≥0) :
    statisticalHVZK init impl rel
      (OracleReduction.id :
        OracleReduction oSpec Statement OStatement Witness Statement OStatement Witness !p[])
      Reduction.idTranscriptSimulator ε := by
  unfold statisticalHVZK
  simpa [OracleReduction.id_toReduction] using
    (Reduction.id_statisticalHVZK (oSpec := oSpec)
      (StmtIn := Statement × (∀ i, OStatement i)) (WitIn := Witness) (σ := σ)
      init impl rel ε)

/-- The zero-round identity oracle reduction is HVZK for any oracle-input relation. -/
theorem id_isHVZK
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (rel : Set ((Statement × (∀ i, OStatement i)) × Witness)) :
    isHVZK init impl rel
      (OracleReduction.id :
        OracleReduction oSpec Statement OStatement Witness Statement OStatement Witness !p[]) := by
  exact ⟨Reduction.idTranscriptSimulator, id_perfectHVZK init impl rel⟩

/-- The zero-round identity oracle reduction is statistical HVZK for any oracle-input relation and
  any error bound. -/
theorem id_isStatHVZK
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (rel : Set ((Statement × (∀ i, OStatement i)) × Witness)) (ε : ℝ≥0) :
    isStatHVZK init impl rel
      (OracleReduction.id :
        OracleReduction oSpec Statement OStatement Witness Statement OStatement Witness !p[])
      ε := by
  exact ⟨Reduction.idTranscriptSimulator, id_statisticalHVZK init impl rel ε⟩

end Identity

#print axioms TranscriptSimulator
#print axioms perfectHVZK
#print axioms statisticalHVZK
#print axioms isHVZK
#print axioms isStatHVZK
#print axioms id_perfectHVZK
#print axioms id_statisticalHVZK
#print axioms id_isHVZK
#print axioms id_isStatHVZK

end OracleReduction
