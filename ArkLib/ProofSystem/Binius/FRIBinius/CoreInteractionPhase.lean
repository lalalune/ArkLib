/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.ProofSystem.Binius.BinaryBasefold.CoreInteractionPhase
import ArkLib.ProofSystem.Binius.FRIBinius.Prelude

/-!
# Core Interaction Phase of FRI-Binius IOPCS

This module exposes the FRI-Binius core interaction interfaces that lift the
Binary Basefold core interaction into the ring-switching context.
-/

namespace Binius.FRIBinius.CoreInteractionPhase
noncomputable section

open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial
  MvPolynomial TensorProduct Module Binius.BinaryBasefold RingSwitching
open scoped NNReal

variable (κ : ℕ) [NeZero κ]
variable (L : Type) [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
  [SampleableType L]
variable (K : Type) [Field K] [Fintype K] [DecidableEq K]
variable [h_Fq_char_prime : Fact (Nat.Prime (ringChar K))] [hF₂ : Fact (Fintype.card K = 2)]
variable [Algebra K L]
variable (β : Basis (Fin (2 ^ κ)) K L)
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable (ℓ ℓ' 𝓡 ϑ γ_repetitions : ℕ) [NeZero ℓ] [NeZero ℓ'] [NeZero 𝓡] [NeZero ϑ]
variable (h_ℓ_add_R_rate : ℓ' + 𝓡 < 2 ^ κ)
variable (h_l : ℓ = ℓ' + κ)
variable [hdiv : Fact (ϑ ∣ ℓ')]

/-- The Binius ring-switching profile, built from the boolean-hypercube basis derived from `β`. -/
def biniusProfile (β : Basis (Fin (2 ^ κ)) K L) : RingSwitching.RingSwitchingProfile K L κ :=
  by
    sorry

section SumcheckFold

/-- Statement lens for the identity-shaped sumcheck-fold lift. -/
def sumcheckFoldStmtLens : OracleStatement.Lens
    (OuterStmtIn := Statement (L := L) (ℓ := ℓ')
      (RingSwitchingBaseContext κ L K ℓ (biniusProfile κ L K β)) 0)
    (OuterStmtOut := Statement (L := L) (ℓ := ℓ')
      (RingSwitchingBaseContext κ L K ℓ (biniusProfile κ L K β)) (Fin.last ℓ'))
    (InnerStmtIn := Statement (L := L) (ℓ := ℓ')
      (RingSwitchingBaseContext κ L K ℓ (biniusProfile κ L K β)) 0)
    (InnerStmtOut := Statement (L := L) (ℓ := ℓ')
      (RingSwitchingBaseContext κ L K ℓ (biniusProfile κ L K β)) (Fin.last ℓ'))
    (OuterOStmtIn := BinaryBasefold.OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
    (OuterOStmtOut := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (InnerOStmtIn := BinaryBasefold.OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
    (InnerOStmtOut := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ')) := by
  sorry

/-- Oracle-routing lens for the sumcheck-fold lift. -/
def sumcheckFoldOracleLens : OracleStatement.OracleLens ([]ₒ)
    (OuterStmtIn := Statement (L := L) (ℓ := ℓ')
      (RingSwitchingBaseContext κ L K ℓ (biniusProfile κ L K β)) 0)
    (OuterStmtOut := Statement (L := L) (ℓ := ℓ')
      (RingSwitchingBaseContext κ L K ℓ (biniusProfile κ L K β)) (Fin.last ℓ'))
    (InnerStmtIn := Statement (L := L) (ℓ := ℓ')
      (RingSwitchingBaseContext κ L K ℓ (biniusProfile κ L K β)) 0)
    (InnerStmtOut := Statement (L := L) (ℓ := ℓ')
      (RingSwitchingBaseContext κ L K ℓ (biniusProfile κ L K β)) (Fin.last ℓ'))
    (OuterOStmtIn := BinaryBasefold.OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
    (OuterOStmtOut := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (InnerOStmtIn := BinaryBasefold.OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
    (InnerOStmtOut := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (pSpec := BinaryBasefold.pSpecSumcheckFold K β
      (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) := by
  sorry

/-- Oracle context lens for the sumcheck-fold lift. -/
def sumcheckFoldCtxLens : OracleContext.Lens
    (OuterStmtIn := Statement (L := L) (ℓ := ℓ')
      (RingSwitchingBaseContext κ L K ℓ (biniusProfile κ L K β)) 0)
    (OuterStmtOut := Statement (L := L) (ℓ := ℓ')
      (RingSwitchingBaseContext κ L K ℓ (biniusProfile κ L K β)) (Fin.last ℓ'))
    (InnerStmtIn := Statement (L := L) (ℓ := ℓ')
      (RingSwitchingBaseContext κ L K ℓ (biniusProfile κ L K β)) 0)
    (InnerStmtOut := Statement (L := L) (ℓ := ℓ')
      (RingSwitchingBaseContext κ L K ℓ (biniusProfile κ L K β)) (Fin.last ℓ'))
    (OuterOStmtIn := BinaryBasefold.OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
    (OuterOStmtOut := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (InnerOStmtIn := BinaryBasefold.OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
    (InnerOStmtOut := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (OuterWitIn := RingSwitching.SumcheckWitness L ℓ' 0)
    (OuterWitOut := BinaryBasefold.Witness K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ') (Fin.last ℓ'))
    (InnerWitIn := BinaryBasefold.Witness K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ') 0)
    (InnerWitOut := BinaryBasefold.Witness K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ') (Fin.last ℓ')) := by
  have _ := h_l
  sorry

/-- The lifted sumcheck-fold oracle verifier. -/
def sumcheckFoldOracleVerifier :
  OracleVerifier []ₒ
    (Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ (biniusProfile κ L K β)) 0)
    (BinaryBasefold.OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
    (Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ (biniusProfile κ L K β))
      (Fin.last ℓ'))
    (BinaryBasefold.OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (BinaryBasefold.pSpecSumcheckFold K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) := by
  have _ := h_l
  sorry

/-- The lifted sumcheck-fold oracle reduction. -/
def sumcheckFoldOracleReduction :
  OracleReduction []ₒ
    (Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ (biniusProfile κ L K β)) 0)
    (BinaryBasefold.OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
    (RingSwitching.SumcheckWitness L ℓ' 0)
    (Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ (biniusProfile κ L K β))
      (Fin.last ℓ'))
    (BinaryBasefold.OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (BinaryBasefold.Witness K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ') (Fin.last ℓ'))
    (BinaryBasefold.pSpecSumcheckFold K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) := by
  have _ := h_l
  sorry

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}

theorem sumcheckFoldOracleReduction_perfectCompleteness :
  OracleReduction.perfectCompleteness
    (oracleReduction := sumcheckFoldOracleReduction κ L K β ℓ ℓ' 𝓡 ϑ
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) h_l)
    (relIn := RingSwitching.sumcheckRoundRelation κ L K (biniusProfile κ L K β)
      ℓ ℓ' h_l (aOStmtIn := BinaryBasefoldAbstractOStmtIn κ L K β ℓ'
        𝓡 ϑ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) 0)
    (relOut := BinaryBasefold.roundRelation (mp := RingSwitching_SumcheckMultParam κ L K
      (biniusProfile κ L K β) ℓ ℓ' h_l) K β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ'))
    (init := init) (impl := impl) := by
  sorry

theorem sumcheckFoldOracleVerifier_rbrKnowledgeSoundness :
  (sumcheckFoldOracleVerifier κ L K β ℓ ℓ' 𝓡 ϑ
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) h_l).rbrKnowledgeSoundness init impl
    (relIn := RingSwitching.sumcheckRoundRelation κ L K (biniusProfile κ L K β)
      ℓ ℓ' h_l (aOStmtIn := BinaryBasefoldAbstractOStmtIn κ L K β ℓ'
        𝓡 ϑ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) 0)
    (relOut := BinaryBasefold.roundRelation (mp := RingSwitching_SumcheckMultParam κ L K
      (biniusProfile κ L K β) ℓ ℓ' h_l) K β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ'))
    (rbrKnowledgeError := BinaryBasefold.CoreInteraction.sumcheckFoldKnowledgeError K β
      (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) := by
  sorry

end SumcheckFold

section CoreInteractionPhaseReduction

/-- The FRI-Binius core interaction oracle verifier. -/
@[reducible]
def coreInteractionOracleVerifier :
  OracleVerifier []ₒ
    (Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ (biniusProfile κ L K β)) 0)
    (BinaryBasefold.OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
    (BinaryBasefold.FinalSumcheckStatementOut (L := L) (ℓ := ℓ'))
    (BinaryBasefold.OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (BinaryBasefold.pSpecCoreInteraction K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) := by
  have _ := h_l
  sorry

/-- The FRI-Binius core interaction oracle reduction. -/
@[reducible]
def coreInteractionOracleReduction :
  OracleReduction []ₒ
    (Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ (biniusProfile κ L K β)) 0)
    (BinaryBasefold.OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
    (RingSwitching.SumcheckWitness L ℓ' 0)
    (BinaryBasefold.FinalSumcheckStatementOut (L := L) (ℓ := ℓ'))
    (BinaryBasefold.OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    Unit
    (BinaryBasefold.pSpecCoreInteraction K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) := by
  have _ := h_l
  sorry

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}

theorem coreInteractionOracleReduction_perfectCompleteness :
    OracleReduction.perfectCompleteness
      (oracleReduction := coreInteractionOracleReduction κ L K β ℓ ℓ' 𝓡 ϑ
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) h_l)
      (relIn := RingSwitching.sumcheckRoundRelation κ L K (biniusProfile κ L K β)
        ℓ ℓ' h_l (aOStmtIn := BinaryBasefoldAbstractOStmtIn κ L K β ℓ'
          𝓡 ϑ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) 0)
      (relOut := BinaryBasefold.finalSumcheckRelOut K β
        (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      (init := init)
      (impl := impl) := by
  sorry

def coreInteractionOracleRbrKnowledgeError
    (_ : (BinaryBasefold.pSpecCoreInteraction K β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).ChallengeIdx) : ℝ≥0 := 0

theorem coreInteractionOracleVerifier_rbrKnowledgeSoundness :
    (coreInteractionOracleVerifier κ L K β ℓ ℓ' 𝓡 ϑ
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) h_l).rbrKnowledgeSoundness init impl
      (relIn := RingSwitching.sumcheckRoundRelation κ L K (biniusProfile κ L K β)
        ℓ ℓ' h_l (aOStmtIn := BinaryBasefoldAbstractOStmtIn κ L K β ℓ'
          𝓡 ϑ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) 0)
      (relOut := BinaryBasefold.finalSumcheckRelOut K β
        (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      (rbrKnowledgeError := coreInteractionOracleRbrKnowledgeError κ L K β ℓ' 𝓡 ϑ
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) := by
  sorry

end CoreInteractionPhaseReduction

end
end Binius.FRIBinius.CoreInteractionPhase
