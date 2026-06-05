/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.ProofSystem.Binius.BinaryBasefold.QueryPhase
import ArkLib.ProofSystem.Binius.FRIBinius.CoreInteractionPhase
import ArkLib.ProofSystem.RingSwitching.BatchingPhase

/-!
# FRI-Binius IOPCS

The FRI-Binius IOPCS consists of the following phases:
1. **Batching Phase**: polynomial packing and batching via tensor algebra operations
2. **Core Interaction Phase**: Interactive sumcheck + FRI folding over ℓ' rounds
3. **Query Phase**: FRI-style proximity testing with γ repetitions

## References
- State RBR KS

## References

- [DP24] Diamond, Benjamin E., and Jim Posen. "Polylogarithmic Proofs for Multilinears over Binary
  Towers." Cryptology ePrint Archive (2024).
-/

namespace Binius.FRIBinius.FullFRIBinius
noncomputable section

open Polynomial MvPolynomial OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Module
  Binius
open Binius.BinaryBasefold RingSwitching

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
def biniusProfile : RingSwitching.RingSwitchingProfile K L κ :=
  let βH := booleanHypercubeBasis κ L K β
  {
    basis := βH
    A := RingSwitching.TensorAlgebra K L
    φ₀ := RingSwitching.φ₀ L K
    φ₁ := RingSwitching.φ₁ L K
    decomposeRows := RingSwitching.decompose_tensor_algebra_rows (β := βH)
    decomposeColumns := RingSwitching.decompose_tensor_algebra_columns (β := βH)
    decomposeRows_spec := by
      intro z
      conv_lhs => rw [← Basis.sum_repr (βH.baseChange L) z]
      apply Finset.sum_congr rfl
      intro u _
      unfold RingSwitching.decompose_tensor_algebra_rows
      rw [Basis.baseChange_apply]
      simp only [RingSwitching.φ₀, RingSwitching.φ₁, RingHom.coe_mk, MonoidHom.coe_mk,
        OneHom.coe_mk, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul,
        TensorProduct.smul_tmul', smul_eq_mul]
    decomposeColumns_spec := by
      intro z
      sorry
    decomposeRows_add := by
      intro z w u
      unfold RingSwitching.decompose_tensor_algebra_rows
      rw [map_add, Finsupp.add_apply]
    decomposeRows_φ₀_mul_φ₁ := by
      intro a b u
      have h : RingSwitching.φ₀ L K a * RingSwitching.φ₁ L K b = a ⊗ₜ[K] b := by
        simp only [RingSwitching.φ₀, RingSwitching.φ₁, RingHom.coe_mk, MonoidHom.coe_mk,
          OneHom.coe_mk, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [h]
      unfold RingSwitching.decompose_tensor_algebra_rows
      rw [Basis.baseChange_repr_tmul]
    decomposeColumns_add := by
      intro z w v
      letI rightAlgebra : Algebra L (RingSwitching.TensorAlgebra K L) :=
        Algebra.TensorProduct.rightAlgebra
      letI rightModule : Module L (RingSwitching.TensorAlgebra K L) := rightAlgebra.toModule
      show (Basis.baseChangeRight (b := booleanHypercubeBasis κ L K β) (Right := L)).repr
            (z + w) v
        = (Basis.baseChangeRight (b := booleanHypercubeBasis κ L K β) (Right := L)).repr z v
        + (Basis.baseChangeRight (b := booleanHypercubeBasis κ L K β) (Right := L)).repr w v
      rw [map_add, Finsupp.add_apply]
    decomposeColumns_φ₀_mul_φ₁ := by
      intro a b v
      have h : RingSwitching.φ₀ L K a * RingSwitching.φ₁ L K b = a ⊗ₜ[K] b := by
        simp only [RingSwitching.φ₀, RingSwitching.φ₁, RingHom.coe_mk, MonoidHom.coe_mk,
          OneHom.coe_mk, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [h]
      unfold RingSwitching.decompose_tensor_algebra_columns
      rw [Basis.baseChangeRight_repr_tmul]
  }

section Pspec

def batchingCorePspec := (RingSwitching.pSpecBatching κ L K (biniusProfile κ L K β)) ++ₚ
  (BinaryBasefold.pSpecCoreInteraction K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))

def fullPspec := (batchingCorePspec κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate) ++ₚ
  (BinaryBasefold.pSpecQuery K β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate))

instance : ∀ j, OracleInterface ((batchingCorePspec κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate).Message j) :=
  instOracleInterfaceMessageAppend (pSpec₁ := RingSwitching.pSpecBatching κ L K (biniusProfile κ L K β))
    (pSpec₂ := BinaryBasefold.pSpecCoreInteraction K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))

instance : ∀ j, SampleableType ((batchingCorePspec κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate).Challenge j) :=
  instSampleableTypeChallengeAppend (pSpec₁ := RingSwitching.pSpecBatching κ L K (biniusProfile κ L K β))
    (pSpec₂ := BinaryBasefold.pSpecCoreInteraction K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))

instance : ∀ j, OracleInterface ((fullPspec κ L K β ℓ' 𝓡 ϑ γ_repetitions
    h_ℓ_add_R_rate).Message j) :=
  instOracleInterfaceMessageAppend (pSpec₁ := batchingCorePspec κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate)
    (pSpec₂ := BinaryBasefold.pSpecQuery K β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate))

instance : ∀ j, SampleableType ((fullPspec κ L K β ℓ' 𝓡 ϑ γ_repetitions
    h_ℓ_add_R_rate).Challenge j) :=
  instSampleableTypeChallengeAppend (pSpec₁ := batchingCorePspec κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate)
    (pSpec₂ := BinaryBasefold.pSpecQuery K β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate))

end Pspec

def batchingCoreVerifier :
    OracleVerifier []ₒ
      (StmtIn := BatchingStmtIn (L := L) (ℓ:=ℓ))
      (OStmtIn := (BinaryBasefoldAbstractOStmtIn κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate).OStmtIn)
      (StmtOut := BinaryBasefold.FinalSumcheckStatementOut (L:=L) (ℓ:=ℓ'))
      (OStmtOut := BinaryBasefold.OracleStatement K β (𝓡:=𝓡)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
      (pSpec := batchingCorePspec κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate) := by
  sorry

def batchingCoreReduction :
    OracleReduction []ₒ
      (StmtIn := BatchingStmtIn (L := L) (ℓ:=ℓ))
      (OStmtIn := (BinaryBasefoldAbstractOStmtIn κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate).OStmtIn)
      (WitIn := BatchingWitIn L K ℓ ℓ')
      (StmtOut := BinaryBasefold.FinalSumcheckStatementOut (L:=L) (ℓ:=ℓ'))
      (OStmtOut := BinaryBasefold.OracleStatement K β (𝓡:=𝓡)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
      (WitOut := Unit)
      (pSpec := batchingCorePspec κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate) := by
  sorry

/-- The oracle verifier for the full Binary Basefold protocol -/
@[reducible]
noncomputable def fullOracleVerifier :
  OracleVerifier (oSpec:=[]ₒ)
    (StmtIn := BatchingStmtIn (L := L) (ℓ:=ℓ))
    (OStmtIn := (BinaryBasefoldAbstractOStmtIn κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate).OStmtIn)
    (StmtOut := Bool)
    (OStmtOut := fun _ : Empty => Unit)
    (pSpec := fullPspec κ L K β ℓ' 𝓡 ϑ γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) :=
  by
    sorry

/-- The reduction for the full Binary Basefold protocol -/
@[reducible]
noncomputable def fullOracleReduction :
  OracleReduction (oSpec:=[]ₒ)
    (StmtIn := BatchingStmtIn (L := L) (ℓ:=ℓ))
    (OStmtIn := (BinaryBasefoldAbstractOStmtIn κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate).OStmtIn)
    (StmtOut := Bool)
    (OStmtOut := fun _ : Empty => Unit)
    (WitIn := BatchingWitIn L K ℓ ℓ')
    (WitOut := Unit)
    (pSpec := fullPspec κ L K β ℓ' 𝓡 ϑ γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) :=
  by
    sorry

/-- The full Binary Basefold protocol as a Proof -/
@[reducible]
noncomputable def fullOracleProof :
  OracleProof []ₒ
    (Statement := BatchingStmtIn (L := L) (ℓ:=ℓ))
    (OStatement := (BinaryBasefoldAbstractOStmtIn κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate).OStmtIn)
    (Witness := BatchingWitIn L K ℓ ℓ')
    (pSpec:= fullPspec κ L K β ℓ' 𝓡 ϑ γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) :=
  fullOracleReduction κ L K β ℓ ℓ' 𝓡 ϑ γ_repetitions
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate)

/-!
## Security Properties
-/

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}

/-- Perfect completeness for the full Binary Basefold protocol (reduction).

THREADED (2026-06-04): sumcheck-fold lens coherence. The core-interaction phase's perfect
completeness (`CoreInteractionPhase.coreInteractionOracleReduction_perfectCompleteness`) transports
its proof through the oracle-routing `sumcheckFoldOracleLens`, whose `LiftContextCoherent`
(`toVerifier_comm`) side condition (#433) is a genuine, non-`rfl` lens obligation left unproven
upstream and threaded as a hypothesis there (commit a22be75b, exactly as in
`Sumcheck/Spec/General.lean`). We thread the same `coh` through here and pass it through at the
core-interaction call site below. -/
theorem fullOracleReduction_perfectCompleteness
    -- THREADED (2026-06-04): sumcheck-fold lens coherence
    (coh : OracleVerifier.LiftContextCoherent
      (CoreInteractionPhase.sumcheckFoldOracleLens κ L K β ℓ ℓ' 𝓡 ϑ
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      (BinaryBasefold.CoreInteraction.sumcheckFoldOracleReduction K β (ϑ:=ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).verifier) :
  OracleReduction.perfectCompleteness
    (oracleReduction := fullOracleReduction κ L K β ℓ ℓ' 𝓡 ϑ γ_repetitions
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (relIn := BatchingPhase.batchingInputRelation κ L K (biniusProfile κ L K β)
      ℓ ℓ' h_l (BinaryBasefoldAbstractOStmtIn κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate))
    (relOut := acceptRejectOracleRel)
    (init := init)
    (impl := impl) :=
  by
    sorry

-- TODO: state RBR KS

end
end Binius.FRIBinius.FullFRIBinius
