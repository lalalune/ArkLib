/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.ProofSystem.Binius.BinaryBasefold.CoreInteractionPhase
import ArkLib.ProofSystem.Binius.BinaryBasefold.QueryPhase

/-!
## Full Binary Basefold Protocol

Sequential composition of:
1. Core Interaction Phase
2. Query Phase
-/

open AdditiveNTT Polynomial

namespace Binius.BinaryBasefold.FullBinaryBasefold
open Polynomial MvPolynomial OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT
open scoped NNReal

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
  [SampleableType L]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))] [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ 𝓡 ϑ : ℕ} (γ_repetitions : ℕ) [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ]
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r}
variable [hdiv : Fact (ϑ ∣ ℓ)]

instance : OracleInterface Unit := OracleInterface.instDefault

/-- The oracle verifier for the full Binary Basefold protocol: the core interaction phase
(`pSpecCoreInteraction`) appended with the final query phase (`pSpecQuery`), matching
`fullPSpec = pSpecCoreInteraction ++ₚ pSpecQuery`. -/
@[reducible]
noncomputable def fullOracleVerifier :
  OracleVerifier (oSpec := []ₒ)
    (StmtIn := Statement (L := L) (ℓ := ℓ) (SumcheckBaseContext L ℓ) 0)
    (OStmtIn := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
    (StmtOut := Bool)
    (OStmtOut := fun _ : Empty => Unit)
    (pSpec := fullPSpec 𝔽q β γ_repetitions (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) :=
  OracleVerifier.append (oSpec := []ₒ)
    (Stmt₁ := Statement (L := L) (ℓ := ℓ) (SumcheckBaseContext L ℓ) 0)
    (Stmt₂ := FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (Stmt₃ := Bool)
    (OStmt₁ := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
    (OStmt₂ := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ))
    (OStmt₃ := fun _ : Empty => Unit)
    (pSpec₁ := pSpecCoreInteraction 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (pSpec₂ := pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (V₁ := CoreInteraction.coreInteractionOracleVerifier 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (V₂ := QueryPhase.queryOracleVerifier 𝔽q β (ϑ := ϑ) γ_repetitions
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate))

/-- The reduction for the full Binary Basefold protocol: the core interaction phase appended with
the final query phase, matching `fullPSpec = pSpecCoreInteraction ++ₚ pSpecQuery`. -/
@[reducible]
noncomputable def fullOracleReduction :
  OracleReduction (oSpec := []ₒ)
    (StmtIn := Statement (L := L) (ℓ := ℓ) (SumcheckBaseContext L ℓ) 0)
    (OStmtIn := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
    (StmtOut := Bool)
    (OStmtOut := fun _ : Empty => Unit)
    (WitIn := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) 0)
    (WitOut := Unit)
    (pSpec := fullPSpec 𝔽q β γ_repetitions (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) :=
  OracleReduction.append (oSpec := []ₒ)
    (Stmt₁ := Statement (L := L) (ℓ := ℓ) (SumcheckBaseContext L ℓ) 0)
    (Stmt₂ := FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (Stmt₃ := Bool)
    (Wit₁ := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) 0)
    (Wit₂ := Unit)
    (Wit₃ := Unit)
    (OStmt₁ := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
    (OStmt₂ := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ))
    (OStmt₃ := fun _ : Empty => Unit)
    (pSpec₁ := pSpecCoreInteraction 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (pSpec₂ := pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (R₁ := CoreInteraction.coreInteractionOracleReduction 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (R₂ := QueryPhase.queryOracleReduction 𝔽q β (ϑ := ϑ) γ_repetitions
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate))

/-- The full Binary Basefold protocol as a proof object. -/
@[reducible]
noncomputable def fullOracleProof :
  OracleProof []ₒ
    (Statement := Statement (L := L) (ℓ := ℓ) (SumcheckBaseContext L ℓ) 0)
    (OStatement := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
    (Witness := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) 0)
    (pSpec := fullPSpec 𝔽q β γ_repetitions (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) :=
  fullOracleReduction 𝔽q β γ_repetitions (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate)

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}

/-- Perfect completeness for the full Binary Basefold protocol. -/
theorem fullOracleReduction_perfectCompleteness :
  OracleReduction.perfectCompleteness
    (oracleReduction := fullOracleReduction 𝔽q β γ_repetitions (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (relIn := roundRelation (mp := BBF_SumcheckMultiplierParam) 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0)
    (relOut := acceptRejectOracleRel)
    (init := init)
    (impl := impl) := by
  haveI : ∀ _ : Empty, OracleInterface Unit := fun i => Empty.elim i
  unfold fullOracleReduction fullPSpec
  apply OracleReduction.append_perfectCompleteness
  · exact CoreInteraction.coreInteractionOracleReduction_perfectCompleteness 𝔽q β
      (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (init := init) (impl := impl)
  · exact QueryPhase.queryOracleProof_perfectCompleteness 𝔽q β
      (ϑ := ϑ) (γ_repetitions := γ_repetitions)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) init impl

/-- Combined RBR knowledge soundness error for the full protocol. -/
noncomputable def fullRbrKnowledgeError
    (j : (fullPSpec 𝔽q β γ_repetitions (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).ChallengeIdx) : ℝ≥0 :=
    Sum.elim
      (f := fun i => CoreInteraction.coreInteractionOracleRbrKnowledgeError 𝔽q β
        (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
      (g := fun i => QueryPhase.queryRbrKnowledgeError 𝔽q β γ_repetitions
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
      (ChallengeIdx.sumEquiv.symm j)

/-- Round-by-round knowledge soundness for the full Binary Basefold oracle verifier. -/
theorem fullOracleVerifier_rbrKnowledgeSoundness :
  (fullOracleVerifier 𝔽q β γ_repetitions (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).rbrKnowledgeSoundness init impl
    (relIn := roundRelation (mp := BBF_SumcheckMultiplierParam) 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0)
    (relOut := acceptRejectOracleRel)
    (rbrKnowledgeError := fullRbrKnowledgeError 𝔽q β γ_repetitions (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) := by
  haveI : ∀ _ : Empty, OracleInterface Unit := fun i => Empty.elim i
  unfold fullOracleVerifier fullPSpec
  apply OracleVerifier.append_rbrKnowledgeSoundness
    (init := init) (impl := impl)
    (rel₁ := roundRelation (mp := BBF_SumcheckMultiplierParam) 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0)
    (rel₂ := finalSumcheckRelOut 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (rel₃ := acceptRejectOracleRel)
    (V₁ := CoreInteraction.coreInteractionOracleVerifier 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ))
    (V₂ := QueryPhase.queryOracleVerifier 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ) γ_repetitions)
    (rbrKnowledgeError₁ := CoreInteraction.coreInteractionOracleRbrKnowledgeError 𝔽q β
      (ϑ := ϑ))
    (rbrKnowledgeError₂ := QueryPhase.queryRbrKnowledgeError 𝔽q β
      γ_repetitions)
    (h₁ := by apply CoreInteraction.coreInteractionOracleVerifier_rbrKnowledgeSoundness)
    (h₂ := by apply QueryPhase.queryOracleVerifier_rbrKnowledgeSoundness)

end Binius.BinaryBasefold.FullBinaryBasefold
