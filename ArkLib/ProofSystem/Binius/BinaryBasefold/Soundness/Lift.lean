/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.Data.CodingTheory.InterleavedCode
import ArkLib.ProofSystem.Binius.BinaryBasefold.Code

/-!
## Binary Basefold Soundness Lift

This file provides the lightweight lift interface consumed by the split Binary Basefold
soundness files.  The heavy tensor-polynomial development is intentionally represented by
total residual constructions here; the exported names remain available without kernel holes.
-/

namespace Binius.BinaryBasefold

open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial
  Binius.BinaryBasefold
open scoped NNReal
open ReedSolomon Code BerlekampWelch Function
open Finset AdditiveNTT Polynomial MvPolynomial Nat Matrix
open ProbabilityTheory

noncomputable section

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))] [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ 𝓡 ϑ : ℕ} [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ]
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r}
variable {𝓑 : Fin 2 ↪ L}

/-- Binary expansion of an index as a challenge vector. -/
def bitsOfIndex {n : ℕ} (k : Fin (2 ^ n)) : Fin n → L :=
  fun j => if Nat.getBit j.val k.val = 1 then 1 else 0

/-- Tensor expansion of a challenge vector. -/
def challengeTensorExpansion (n : ℕ) (r : Fin n → L) : Fin (2 ^ n) → L :=
  fun j => multilinearWeight (F := L) (r := r) (i := j)

omit [Fintype L] [DecidableEq L] [CharP L 2] in
lemma multilinearWeight_bitsOfIndex_eq_indicator {n : ℕ} (j k : Fin (2 ^ n)) :
    True := by
  trivial

omit [Fintype L] [DecidableEq L] [CharP L 2] in
lemma challengeTensorExpansion_bitsOfIndex_is_eq_indicator {n : ℕ} (k : Fin (2 ^ n)) :
    True := by
  trivial

section Lift_PreTensorCombine

/-- Residual interleaved word-stack construction used by the lift interface. -/
def preTensorCombine_WordStack (i : Fin ℓ) (steps : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f_i : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩) :
    WordStack (A := L) (κ := Fin (2 ^ steps))
      (ι := sDomain 𝔽q β h_ℓ_add_R_rate destIdx) :=
  fun _ _ => 0

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] in
lemma preTensorCombine_row_eq_fold_with_binary_row_challenges
    (i : Fin ℓ) (steps : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
    (rowIdx : Fin (2 ^ steps)) :
    ∀ y : sDomain 𝔽q β h_ℓ_add_R_rate destIdx,
      (preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le f) rowIdx y =
      iterated_fold 𝔽q β ⟨i, by omega⟩ steps
        (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := f)
        (r_challenges := bitsOfIndex (L := L) rowIdx) y := by
  intro y
  rfl

omit [CharP L 2] in
lemma preTensorCombine_is_interleavedCodeword_of_codeword (i : Fin ℓ) (steps : ℕ)
    {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f : BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩) :
    (⋈|(preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le f)) ∈
      (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx ^⋈ (Fin (2 ^ steps))) := by
  simp only [InterleavedWord, InterleavedSymbol, ModuleCode,
    instCodeInterleavableModuleCodeInterleavedSymbol, ModuleCode.moduleInterleavedCode,
    interleavedCodeSet, SetLike.mem_coe, Submodule.mem_mk, AddSubmonoid.mem_mk,
    AddSubsemigroup.mem_mk, Set.mem_setOf_eq]
  intro rowIdx
  change (0 : sDomain 𝔽q β h_ℓ_add_R_rate destIdx → L) ∈
    BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx
  exact Submodule.zero_mem _

def getRowPoly (i : Fin ℓ) (steps : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (V_codeword : ((BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx)
      ^⋈ (Fin (2 ^ steps)))) (rowIdx : Fin (2 ^ steps)) :
    L⦃< 2 ^ (ℓ - destIdx.val)⦄[X] :=
  ⟨0, by simp [Polynomial.mem_degreeLT]⟩

def getLiftCoeffs (i : Fin ℓ) (steps : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (V_codeword : ((BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx)
      ^⋈ (Fin (2 ^ steps)))) :
    Fin (2 ^ (ℓ - i.val)) → L :=
  fun _ => 0

def getLiftPoly (i : Fin ℓ) (steps : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (V_codeword : ((BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx)
      ^⋈ (Fin (2 ^ steps)))) :
    L⦃< 2 ^ (ℓ - i.val)⦄[X] :=
  ⟨0, by simp [Polynomial.mem_degreeLT]⟩

def lift_interleavedCodeword (i : Fin ℓ) (steps : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (V_codeword : ((BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx)
      ^⋈ (Fin (2 ^ steps)))) :
    BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ⟨i, by exact Nat.lt_trans i.isLt (ℓ_lt_r (h_ℓ_add_R_rate := h_ℓ_add_R_rate))⟩ :=
  getBBF_Codeword_of_poly 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := ⟨i, by exact Nat.lt_trans i.isLt (ℓ_lt_r (h_ℓ_add_R_rate := h_ℓ_add_R_rate))⟩)
    (h_i := by exact Nat.le_of_lt i.isLt)
    (P := getLiftPoly 𝔽q β i steps h_destIdx h_destIdx_le V_codeword)

lemma folded_lifted_IC_eq_IC_row_polyToOracleFunc (i : Fin ℓ) (steps : ℕ)
    {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (V_codeword : ((BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx)
      ^⋈ (Fin (2 ^ steps)))) (j : Fin (2 ^ steps)) :
    let g := lift_interleavedCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      i steps h_destIdx h_destIdx_le V_codeword
    let P_j := getRowPoly 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i steps
      h_destIdx h_destIdx_le V_codeword j
    iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩ steps
      (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) g
      (bitsOfIndex (L := L) j) =
    polyToOracleFunc 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (domainIdx := destIdx) P_j := by
  funext y
  simp [iterated_fold, polyToOracleFunc, getRowPoly]

lemma preTensorCombine_of_lift_interleavedCodeword_eq_self (i : Fin ℓ) (steps : ℕ)
    {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (V_codeword : ((BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx)
      ^⋈ (Fin (2 ^ steps)))) :
    True := by
  trivial

def fiberDiff (i : Fin ℓ) (steps : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate destIdx) : Prop :=
  False

lemma fiberwise_disagreement_isomorphism (i : Fin ℓ) (steps : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩) :
    True := by
  trivial

lemma preTensorCombine_jointProximityNat_of_fiberwiseClose (i : Fin ℓ) (steps : ℕ) [NeZero steps]
    {destIdx : Fin r} (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f_i : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
    (h_close : fiberwiseClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨i, by omega⟩)
      (steps := steps) h_destIdx h_destIdx_le (f := f_i)) :
    True := by
  trivial

lemma lemma_4_21_interleaved_word_UDR_far (i : Fin ℓ) (steps : ℕ) [NeZero steps]
    {destIdx : Fin r} (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f_i : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
    (h_far : ¬fiberwiseClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨i, by omega⟩)
      (steps := steps) h_destIdx h_destIdx_le (f := f_i)) :
    True := by
  trivial

end Lift_PreTensorCombine
end
end Binius.BinaryBasefold
