/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.ProofSystem.Binius.BinaryBasefold.Steps

/-!
## Binary Basefold Core Interaction Phase

This module exposes the core interaction phase interfaces. The detailed dependent
block composition remains pending, but the public verifier/reduction and security
statements are kept available for the full Binary Basefold and FRI-Binius layers.
-/

namespace Binius.BinaryBasefold.CoreInteraction

noncomputable section
open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial
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

section ComponentReductions
variable {Context : Type} {mp : SumcheckMultiplierParam L ℓ Context}

/-- Sumcheck-fold verifier, from round `0` to the last sumcheck round. -/
@[reducible]
def sumcheckFoldOracleVerifier :
  OracleVerifier []ₒ
    (Statement (L := L) (ℓ := ℓ) Context 0)
    (OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
    (Statement (L := L) (ℓ := ℓ) Context (Fin.last ℓ))
    (OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ))
    (pSpecSumcheckFold 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) := by
  sorry

/-- Sumcheck-fold reduction, from round `0` to the last sumcheck round. -/
@[reducible]
def sumcheckFoldOracleReduction :
  OracleReduction []ₒ
    (Statement (L := L) (ℓ := ℓ) Context 0)
    (OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
    (Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) 0)
    (Statement (L := L) (ℓ := ℓ) Context (Fin.last ℓ))
    (OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ))
    (Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (Fin.last ℓ))
    (pSpecSumcheckFold 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) := by
  sorry

def NBlockMessages : ℕ := 2 * (ϑ - 1) + 3

def sumcheckFoldKnowledgeError
    (_ : (pSpecSumcheckFold 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).ChallengeIdx) : ℝ≥0 := 0

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}

/-- Perfect completeness for the sumcheck-fold reduction. -/
theorem sumcheckFoldOracleReduction_perfectCompleteness :
    OracleReduction.perfectCompleteness
      (pSpec := pSpecSumcheckFold 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      (relIn := roundRelation (mp := mp) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0)
      (relOut := roundRelation (mp := mp) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ))
      (oracleReduction := sumcheckFoldOracleReduction 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      (init := init)
      (impl := impl) := by
  sorry

/-- Round-by-round knowledge soundness for the sumcheck-fold verifier. -/
theorem sumcheckFoldOracleVerifier_rbrKnowledgeSoundness :
    (sumcheckFoldOracleVerifier 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).rbrKnowledgeSoundness init impl
      (pSpec := pSpecSumcheckFold 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      (relIn := roundRelation (mp := mp) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0)
      (relOut := roundRelation (mp := mp) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ))
      (rbrKnowledgeError := sumcheckFoldKnowledgeError 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) := by
  sorry

end ComponentReductions

section CoreInteractionPhaseReduction

/-- The core interaction verifier, composed of sumcheck-fold and final sumcheck. -/
@[reducible]
def coreInteractionOracleVerifier :
  OracleVerifier []ₒ
    (Statement (L := L) (ℓ := ℓ) (SumcheckBaseContext L ℓ) 0)
    (OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
    (FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ))
    (pSpecCoreInteraction 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) := by
  sorry

/-- The core interaction reduction, composed of sumcheck-fold and final sumcheck. -/
@[reducible]
def coreInteractionOracleReduction :
  OracleReduction []ₒ
    (Statement (L := L) (ℓ := ℓ) (SumcheckBaseContext L ℓ) 0)
    (OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
    (Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) 0)
    (FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ))
    Unit
    (pSpecCoreInteraction 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) := by
  sorry

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}

/-- Perfect completeness for the core interaction reduction. -/
theorem coreInteractionOracleReduction_perfectCompleteness :
    OracleReduction.perfectCompleteness
      (pSpec := pSpecCoreInteraction 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      (relIn := roundRelation (mp := BBF_SumcheckMultiplierParam) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0)
      (relOut := finalSumcheckRelOut 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      (oracleReduction := coreInteractionOracleReduction 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      (init := init)
      (impl := impl) := by
  sorry

def coreInteractionOracleRbrKnowledgeError
    (_ : (pSpecCoreInteraction 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).ChallengeIdx) : ℝ≥0 := 0

/-- Round-by-round knowledge soundness for the core interaction verifier. -/
theorem coreInteractionOracleVerifier_rbrKnowledgeSoundness :
    (coreInteractionOracleVerifier 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).rbrKnowledgeSoundness init impl
      (pSpec := pSpecCoreInteraction 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      (relIn := roundRelation (mp := BBF_SumcheckMultiplierParam) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0)
      (relOut := finalSumcheckRelOut 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      (rbrKnowledgeError := coreInteractionOracleRbrKnowledgeError 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) := by
  sorry

end CoreInteractionPhaseReduction

end
end Binius.BinaryBasefold.CoreInteraction
