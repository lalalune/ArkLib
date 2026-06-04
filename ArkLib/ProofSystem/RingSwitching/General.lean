/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.ProofSystem.RingSwitching.Spec
import ArkLib.ProofSystem.RingSwitching.BatchingPhase
import ArkLib.ProofSystem.RingSwitching.SumcheckPhase
import ArkLib.OracleReduction.Security.RoundByRound
import ArkLib.OracleReduction.Composition.Sequential.Append

/-!
# Full Ring-Switching Protocol

This module contains specifications and security properties for the full
ring-switching protocol. The protocol is a sequential composition of:
1. **Batching Phase** (polynomial packing and batching via tensor algebra operations)
2. **Sumcheck Phase** (ℓ' rounds of sumcheck, and the final sumcheck step)
3. **Large Field Invocation** (invocation to underlying large-field IOPCS)

## References

- [DP24] Diamond, Benjamin E., and Jim Posen. "Polylogarithmic Proofs for Multilinears over Binary
  Towers." Cryptology ePrint Archive (2024).
-/

namespace RingSwitching.FullRingSwitching
noncomputable section
open Polynomial MvPolynomial OracleSpec OracleComp ProtocolSpec Finset Module

variable (κ : ℕ) [NeZero κ]
variable (L : Type) [CommRing L] [Nontrivial L] [Fintype L] [DecidableEq L]
  [SampleableType L]
variable (K : Type) [CommRing K] [Fintype K] [DecidableEq K]
variable [Algebra K L]
variable (P : RingSwitchingProfile K L κ)
variable (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ']
variable (h_l : ℓ = ℓ' + κ)
variable (mlIOPCS : MLIOPCS L ℓ')

def batchingCoreVerifier :
  OracleVerifier []ₒ
    (BatchingStmtIn (L := L) (ℓ := ℓ)) mlIOPCS.OStmtIn
    (MLPEvalStatement L ℓ') mlIOPCS.toAbstractOStmtIn.OStmtIn
    (pSpecLargeFieldReduction κ L K P ℓ') := by
  have _ := h_l
  sorry

/-- The oracle verifier for the full Binary Basefold protocol -/
@[reducible]
def fullOracleVerifier :
  OracleVerifier []ₒ
    (BatchingStmtIn (L := L) (ℓ := ℓ)) mlIOPCS.OStmtIn
    Bool (fun _ : Empty => Unit)
    (fullPspec κ L K P ℓ' mlIOPCS) := by
  have _ := h_l
  sorry

def batchingCoreReduction :
  OracleReduction []ₒ
    (BatchingStmtIn (L := L) (ℓ := ℓ)) mlIOPCS.OStmtIn
    (BatchingWitIn (L := L) (K := K) (ℓ := ℓ) (ℓ' := ℓ'))
    (MLPEvalStatement L ℓ') mlIOPCS.toAbstractOStmtIn.OStmtIn
    (WitMLP L ℓ') (pSpecLargeFieldReduction κ L K P ℓ') := by
  have _ := h_l
  sorry

/-- The reduction for the full Binary Basefold protocol -/
@[reducible]
def fullOracleReduction :
  OracleReduction (oSpec:=[]ₒ)
    (StmtIn := BatchingStmtIn (L:=L) (ℓ := ℓ)) (StmtOut := Bool)
    (OStmtIn:= mlIOPCS.OStmtIn)
    (OStmtOut := fun _ : Empty => Unit)
    (pSpec := fullPspec κ L K P ℓ' mlIOPCS)
    (WitIn := BatchingWitIn (L:=L) (K:=K) (ℓ := ℓ) (ℓ' := ℓ')) (WitOut := Unit)
    := by
  have _ := h_l
  sorry

/-- The full Binary Basefold protocol as a Proof -/
@[reducible]
def fullOracleProof :
  OracleProof []ₒ
    (Statement := BatchingStmtIn (L:=L) (ℓ := ℓ))
    (OStatement := mlIOPCS.OStmtIn)
    (Witness := BatchingWitIn (L:=L) (K:=K) (ℓ := ℓ) (ℓ' := ℓ'))
    (pSpec:= fullPspec κ L K P ℓ' mlIOPCS) :=
    fullOracleReduction κ L K P ℓ ℓ' h_l mlIOPCS

variable [∀ i, SampleableType (mlIOPCS.pSpec.Challenge i)]

/-- Input relation for the full ring-switching protocol -/
abbrev fullInputRelation := BatchingPhase.batchingInputRelation κ L K P ℓ ℓ'
  h_l mlIOPCS.toAbstractOStmtIn
abbrev fullOutputRelation := acceptRejectOracleRel

open scoped NNReal
open Sumcheck.Structured

section SecurityProperties
variable {σ : Type} (init : ProbComp σ) {impl : QueryImpl []ₒ (StateT σ ProbComp)}

omit [(i : mlIOPCS.pSpec.ChallengeIdx) → SampleableType (mlIOPCS.pSpec.Challenge i)] in
-- `[IsDomain L] [IsDomain K]` are needed by the core-interaction (final-sumcheck) completeness,
-- which invokes the DP24 capstone `A_MLE_eval_eq_compute_final_eq_value` (an `IsDomain` algebra
-- lemma). They hold in every real instantiation (`binaryTowerProfile` builds from fields `K`, `L`).
lemma batchingCore_perfectCompleteness [IsDomain L] [IsDomain K] :
  (batchingCoreReduction κ L K P ℓ ℓ' h_l mlIOPCS).perfectCompleteness
  (pSpec := pSpecLargeFieldReduction κ L K P ℓ')
  (relIn := BatchingPhase.batchingInputRelation κ L K P ℓ ℓ' h_l mlIOPCS.toAbstractOStmtIn)
  (relOut := mlIOPCS.toRelInput)
  (init:=init) (impl:=impl) := by
  sorry

omit [(i : mlIOPCS.pSpec.ChallengeIdx) → SampleableType (mlIOPCS.pSpec.Challenge i)] in
theorem fullOracleReduction_perfectCompleteness [IsDomain L] [IsDomain K] :
  (fullOracleReduction κ L K P ℓ ℓ' h_l mlIOPCS).perfectCompleteness
    (relIn := BatchingPhase.batchingInputRelation κ L K P ℓ ℓ' h_l mlIOPCS.toAbstractOStmtIn)
    (relOut := acceptRejectOracleRel)
    (init := init)
    (impl := impl)
     := by
  sorry

def batchingCoreRbrKnowledgeError
    (i : (pSpecBatching κ L K P ++ₚ pSpecCoreInteraction L ℓ').ChallengeIdx) : ℝ≥0 :=
  Sum.elim (f:=BatchingPhase.batchingRBRKnowledgeError κ L K P)
    (g:=SumcheckPhase.coreInteractionRbrKnowledgeError L ℓ')
    (ChallengeIdx.sumEquiv.symm i)

def fullRbrKnowledgeError (i : (fullPspec κ L K P ℓ' mlIOPCS).ChallengeIdx) : ℝ≥0
  := Sum.elim (f:=batchingCoreRbrKnowledgeError κ L K P ℓ')
  (g:=mlIOPCS.rbrKnowledgeError)
  (ChallengeIdx.sumEquiv.symm i)

omit [(i : mlIOPCS.pSpec.ChallengeIdx) → SampleableType (mlIOPCS.pSpec.Challenge i)] in
/-- Round-by-round knowledge soundness for the full ring-switching oracle verifier.
`IsDomain K` (with the existing `IsDomain L`) is inherited from the batching phase's knowledge
soundness, where it backs the DP24 row-extraction capstone; it holds in every real instantiation
(`binaryTowerProfile` builds from a field `K`). -/
theorem fullOracleVerifier_rbrKnowledgeSoundness [IsDomain L] [IsDomain K] {𝓑 : Fin 2 ↪ L} :
  OracleVerifier.rbrKnowledgeSoundness
    (verifier := fullOracleVerifier κ L K P ℓ ℓ' h_l mlIOPCS)
    (init := init)
    (impl := impl)
    (relIn := fullInputRelation κ L K P ℓ ℓ' h_l mlIOPCS)
    (relOut := fullOutputRelation)
    (rbrKnowledgeError := fun i => fullRbrKnowledgeError κ L K P ℓ' mlIOPCS i) := by
  sorry

end SecurityProperties
end
end RingSwitching.FullRingSwitching
