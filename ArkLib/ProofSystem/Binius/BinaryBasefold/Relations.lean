/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.ProofSystem.Binius.BinaryBasefold.Basic

/-! ## Binary Basefold relations and bad-event layer -/

namespace Binius.BinaryBasefold

open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial
  Binius.BinaryBasefold
open scoped NNReal
open ReedSolomon Code BerlekampWelch
open Finset AdditiveNTT Polynomial MvPolynomial Nat Matrix

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
variable [hdiv : Fact (ϑ ∣ ℓ)]

section SecurityRelations
-- (moved to Basic.lean) declarations canonicalized in Basic: removed duplicates here.
-- NOTE: `getMidCodewords` (in `Basic.lean`) folds from level 0 over `steps := i.val` using
-- the new-API `iterated_fold` (`steps : ℕ`, `{destIdx : Fin r}`, `h_destIdx`/`h_destIdx_le`).
-- This lemma is stated against that same new-API signature (one extra fold step,
-- `steps := 1`, `destIdx := ⟨i.val + 1, _⟩`) so that it stays in sync with
-- `Basic.getMidCodewords` (issue #37: the legacy `Fin (ℓ+1)`-stepped signature is now
-- `iterated_fold_steps`, Prelude-internal only). While `iterated_fold` carries the #32
-- transitional stub body both sides reduce definitionally; once the cast-based body lands,
-- restore the `Fin.dfoldl_succ_last` peel (via `iterated_fold_succ_last_gen`) here.
lemma getMidCodewords_succ (t : L⦃≤ 1⦄[X Fin ℓ]) (i : Fin ℓ)
    (challenges : Fin i.castSucc → L) (r_i' : L) :
  (getMidCodewords 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := i.succ) (t := t) (challenges := Fin.snoc challenges r_i')) =
  (iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := ⟨i, by omega⟩)
    (steps := 1)
    (destIdx := ⟨i.val + 1, by omega⟩)
    (h_destIdx := rfl)
    (h_destIdx_le := by simp only [Fin.mk_le_mk]; omega)
    (f := getMidCodewords 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := i.castSucc) (t := t) (challenges := challenges))
    (r_challenges := fun _ => r_i'))
  := by
  ext y
  unfold getMidCodewords iterated_fold
  rfl

section FoldStepLogic
variable {Context : Type} {mp : SumcheckMultiplierParam L ℓ Context}

def foldPrvState (i : Fin ℓ) : Fin (2 + 1) → Type := fun
  | ⟨0, _⟩ => (Statement (L := L) Context i.castSucc ×
    (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j) ×
    Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
  | ⟨1, _⟩ => Statement (L := L) Context i.castSucc ×
    (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j) ×
    Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc ×
      FoldMessage L
  | _ => Statement (L := L) Context i.castSucc ×
    (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j) ×
    Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc ×
      FoldMessage L × L

private def foldPointToGlobalIndex
    (domainIdx : Fin r)
    (x : AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := 𝓡)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) domainIdx) :
    Fin (2 ^ (ℓ + 𝓡)) :=
  match (List.finRange (2 ^ (ℓ + 𝓡))).find? (fun vIdx =>
      decide ((AdditiveNTT.Comp.indexToSDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := 𝓡)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := domainIdx) vIdx).1 = x.1)) with
  | some vIdx => vIdx
  | none => 0

@[reducible]
def getFoldProverFinalOutput (i : Fin ℓ)
    (finalPrvState : foldPrvState 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      i 2 (Context := Context)) :
  ((Statement (L := L) Context i.succ × ((j : Fin (toOutCodewordsCount ℓ ϑ i.castSucc)) →
    OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j))
      × Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
  := by
  let (stmtIn, oStmtIn, witIn, h_i, r_i') := finalPrvState
  let stmtOut : Statement (L := L) Context i.succ := {
    ctx := stmtIn.ctx,
    sumcheck_target := FoldMessage.eval h_i r_i',
    challenges := Fin.snoc stmtIn.challenges r_i'
  }
  let sourceIdx : Fin r := ⟨i.val, by omega⟩
  let destIdx : Fin r := ⟨i.succ.val, by omega⟩
  have h_source_plus_one_le : sourceIdx.val + 1 ≤ ℓ + 𝓡 := by
    dsimp [sourceIdx]
    omega
  let fᵢ_succ : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (domainIdx := destIdx) :=
    fun y =>
      let yIdx := foldPointToGlobalIndex (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (𝓡 := 𝓡)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx y
      let x₀ := getFiberPointCompFromIndex (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (𝓡 := 𝓡)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (vIdx := yIdx) (i := sourceIdx) (steps := 1)
        (h_i_steps_le := h_source_plus_one_le) 0
      let x₁ := getFiberPointCompFromIndex (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (𝓡 := 𝓡)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (vIdx := yIdx) (i := sourceIdx) (steps := 1)
        (h_i_steps_le := h_source_plus_one_le) 1
      witIn.f x₀ * ((1 - r_i') * x₁.val - r_i') +
        witIn.f x₁ * (r_i' - (1 - r_i') * x₀.val)
  let projectedH := projectToNextSumcheckPoly (L := L) (ℓ := ℓ)
    (i := i) (Hᵢ := witIn.H) (rᵢ := r_i')
  let witOut : Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) i.succ := {
    t := witIn.t,
    H := projectedH,
    f := fᵢ_succ
  }
  exact ⟨⟨stmtOut, oStmtIn⟩, witOut⟩

@[reducible]
def foldProverComputeMsg (i : Fin ℓ)
    (witIn : Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc) :
    FoldMessage L :=
  getSumcheckRoundPoly (L := L) (ℓ := ℓ) (𝓑 := 𝓑) (i := i) witIn.H

@[reducible]
def foldVerifierCheck (i : Fin ℓ)
    (stmtIn : Statement (L := L) Context i.castSucc)
    (msg0 : FoldMessage L) : Prop :=
  FoldMessage.eval msg0 (𝓑 0) + FoldMessage.eval msg0 (𝓑 1) = stmtIn.sumcheck_target

@[reducible]
def foldVerifierStmtOut (i : Fin ℓ)
    (stmtIn : Statement (L := L) Context i.castSucc)
    (msg0 : FoldMessage L)
    (chal1 : L) :
    Statement (L := L) Context i.succ :=
  {
    ctx := stmtIn.ctx,
    sumcheck_target := FoldMessage.eval msg0 chal1,
    challenges := Fin.snoc stmtIn.challenges chal1
  }

end FoldStepLogic

section SumcheckContextIncluded_Relations
variable {Context : Type} {mp : SumcheckMultiplierParam L ℓ Context}

-- (moved to Basic.lean) declarations canonicalized in Basic: removed duplicates here.
lemma firstOracleWitnessConsistencyProp_unique (t₁ t₂ : MultilinearPoly L ℓ)
    (f₀ : OracleFunction (𝔽q := 𝔽q) (β := β)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (𝓡 := 𝓡) 0)
    (h₁ : firstOracleWitnessConsistencyProp 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) t₁ f₀)
    (h₂ : firstOracleWitnessConsistencyProp 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) t₂ f₀) :
    t₁ = t₂ := by
  classical
  have h₁_some :
      extractMLP 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0 f₀ = some t₁ :=
    (extractMLP_eq_some_iff_pair_UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (f := f₀) (tpoly := t₁)).2 h₁
  have h₂_some :
      extractMLP 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0 f₀ = some t₂ :=
    (extractMLP_eq_some_iff_pair_UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (f := f₀) (tpoly := t₂)).2 h₂
  rw [h₁_some] at h₂_some
  injection h₂_some

-- (moved to Basic.lean) declarations canonicalized in Basic: removed duplicates here.
lemma foldingBadEventAtBlock_snoc_castSucc_eq (i : Fin ℓ)
    (oStmt : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (ϑ := ϑ) (i := i.castSucc) j)
    (challenges : Fin i.castSucc → L) (r_new : L)
    (j : Fin (toOutCodewordsCount ℓ ϑ i.castSucc))
    (hj_le : j.val * ϑ + ϑ ≤ i.castSucc.val) :
    foldingBadEventAtBlock 𝔽q β (stmtIdx := i.succ)
      (oracleIdx := OracleFrontierIndex.mkFromStmtIdxCastSuccOfSucc i)
      (oStmt := oStmt)
      (challenges := Fin.snoc challenges r_new) j =
    foldingBadEventAtBlock 𝔽q β (stmtIdx := i.castSucc)
      (oracleIdx := OracleFrontierIndex.mkFromStmtIdx i.castSucc)
      (oStmt := oStmt)
      (challenges := challenges) j := by
  unfold foldingBadEventAtBlock
  simp only [OracleFrontierIndex.val_mkFromStmtIdxCastSuccOfSucc,
    Fin.val_castSucc, OracleFrontierIndex.val_mkFromStmtIdx,
    Fin.val_succ]
  have h_guard_succ : oraclePositionToDomainIndex (positionIdx := j) + ϑ ≤ i.val + 1 := by
    simp only [Fin.val_castSucc] at ⊢ hj_le
    omega
  have h_guard_cast : oraclePositionToDomainIndex (positionIdx := j) + ϑ ≤ i.val := by
    simp only [Fin.val_castSucc] at ⊢ hj_le
    omega
  simp only [h_guard_succ, h_guard_cast, ↓reduceDIte]
  congr 1
  unfold getFoldingChallenges
  ext cId
  simp only [Fin.snoc]
  split
  · rfl
  · exfalso
    rename_i h_lt
    simp only [not_lt] at h_lt
    simp only at h_guard_cast
    omega

-- `foldingBadEventAtBlock` (and its `[irreducible]` attribute) now live in `Basic.lean`.

open Classical in
def blockBadEventExistsProp
    (stmtIdx : Fin (ℓ + 1)) (oracleIdx : OracleFrontierIndex stmtIdx)
    (oStmt : ∀ j, (OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ)
      (i := oracleIdx.val) j)) (challenges : Fin stmtIdx → L) : Prop :=
  ∃ j, foldingBadEventAtBlock 𝔽q β (stmtIdx := stmtIdx) (oracleIdx := oracleIdx)
    (oStmt := oStmt) (challenges := challenges) j

def incrementalBadEventExistsProp
    (stmtIdx : Fin (ℓ + 1)) (oracleIdx : OracleFrontierIndex stmtIdx)
    (oStmt : ∀ j, (OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ)
      (i := oracleIdx.val) j)) (challenges : Fin stmtIdx → L) : Prop :=
  ∃ j : Fin (toOutCodewordsCount ℓ ϑ oracleIdx.val),
    let curOracleDomainIdx : Fin r := ⟨oraclePositionToDomainIndex (positionIdx := j), by omega⟩
    let k : ℕ := min ϑ (stmtIdx.val - curOracleDomainIdx.val)
    have h1 := oracle_index_add_steps_le_ℓ ℓ ϑ (i := oracleIdx.val) (j := j)
    have h2 : ℓ + 𝓡 < r := h_ℓ_add_R_rate
    have _ : 𝓡 > 0 := pos_of_neZero 𝓡
    let midIdx : Fin r := ⟨curOracleDomainIdx.val + k, by omega⟩
    let destIdx : Fin r := ⟨curOracleDomainIdx.val + ϑ, by
      dsimp only [oraclePositionToDomainIndex, curOracleDomainIdx]; omega⟩
    Binius.BinaryBasefold.incrementalFoldingBadEvent 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (block_start_idx := curOracleDomainIdx) (k := k)
      (h_k_le := Nat.min_le_left ϑ (stmtIdx.val - curOracleDomainIdx.val))
      (midIdx := midIdx) (destIdx := destIdx) (h_midIdx := rfl) (h_destIdx := rfl)
      (h_destIdx_le := oracle_index_add_steps_le_ℓ ℓ ϑ (i := oracleIdx.val) (j := j))
      (f_block_start := by
        simpa [OracleStatement, oraclePositionToDomainIndex] using oStmt j)
      (r_challenges := fun cId => challenges ⟨curOracleDomainIdx.val + cId.val, by
        have h_k_le_stmt : k ≤ stmtIdx.val - curOracleDomainIdx.val :=
          Nat.min_le_right ϑ (stmtIdx.val - curOracleDomainIdx.val)
        have h_cId_lt_k : cId.val < k := cId.isLt
        omega
      ⟩)

def incrementalBadEventAtLast
    (oStmt : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j)
    (challenges : Fin (Fin.last ℓ) → L)
    (j : Fin (toOutCodewordsCount ℓ ϑ (OracleFrontierIndex.mkFromStmtIdx (Fin.last ℓ)).val)) :
    Prop :=
    let curOracleDomainIdx : Fin r := ⟨oraclePositionToDomainIndex (ℓ := ℓ) (ϑ := ϑ) (positionIdx := j), by omega⟩
    let k : ℕ := min ϑ ((Fin.last ℓ).val - curOracleDomainIdx.val)
    have h1 := oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ)
      (i := (OracleFrontierIndex.mkFromStmtIdx (Fin.last ℓ)).val) (j := j)
    have h2 : ℓ + 𝓡 < r := h_ℓ_add_R_rate
    have _ : 𝓡 > 0 := pos_of_neZero 𝓡
    let midIdx : Fin r := ⟨curOracleDomainIdx.val + k, by omega⟩
    let destIdx : Fin r := ⟨curOracleDomainIdx.val + ϑ, by
      dsimp only [curOracleDomainIdx, oraclePositionToDomainIndex]
      omega⟩
    incrementalFoldingBadEvent 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (block_start_idx := curOracleDomainIdx) (k := k)
      (h_k_le := Nat.min_le_left ϑ ((Fin.last ℓ).val - curOracleDomainIdx.val))
      (midIdx := midIdx) (destIdx := destIdx) (h_midIdx := rfl) (h_destIdx := rfl)
      (h_destIdx_le := oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ)
        (i := (OracleFrontierIndex.mkFromStmtIdx (Fin.last ℓ)).val) (j := j))
      (f_block_start := by
        simpa [OracleStatement, oraclePositionToDomainIndex] using oStmt j)
      (r_challenges := fun cId => challenges ⟨curOracleDomainIdx.val + cId.val, by
        have h_k_le_stmt : k ≤ (Fin.last ℓ).val - curOracleDomainIdx.val :=
          Nat.min_le_right ϑ ((Fin.last ℓ).val - curOracleDomainIdx.val)
        have h_cId_lt_k : cId.val < k := cId.isLt
        omega⟩)

omit [NeZero r] [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q] h_Fq_char_prime hF₂
  [Algebra 𝔽q L] β hβ_lin_indep h_β₀_eq_1 [NeZero 𝓡] hdiv in
lemma lastRoundChallengeSlice_heq
    (challenges : Fin (Fin.last ℓ) → L)
    (j : Fin (toOutCodewordsCount ℓ ϑ (OracleFrontierIndex.mkFromStmtIdx (Fin.last ℓ)).val))
    {k : ℕ} (h : k = ϑ)
    (h_k_le_stmt : k ≤ ℓ - j.val * ϑ)
    (h_le : j.val * ϑ + ϑ ≤ ℓ) :
    HEq
      (fun cId : Fin k => challenges ⟨j.val * ϑ + cId.val, by
        have h_k_le_stmt' : k ≤ ℓ - j.val * ϑ := h_k_le_stmt
        have h_cId_lt_k : cId.val < k := cId.isLt
        change j.val * ϑ + cId.val < ℓ
        omega⟩)
      (fun cId : Fin ϑ => challenges ⟨j.val * ϑ + cId.val, by
        have h_le' : j.val * ϑ + ϑ ≤ ℓ := h_le
        change j.val * ϑ + cId.val < ℓ
        omega⟩) := by
  cases h
  apply heq_of_eq
  funext cId
  apply congrArg challenges
  apply Fin.ext
  rfl

set_option maxHeartbeats 200000 in
lemma foldingBadEventAtBlock_imp_incrementalBadEvent_last
    (oStmt : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j)
    (challenges : Fin (Fin.last ℓ) → L)
    (j : Fin (toOutCodewordsCount ℓ ϑ (OracleFrontierIndex.mkFromStmtIdx (Fin.last ℓ)).val)) :
    foldingBadEventAtBlock 𝔽q β
      (stmtIdx := Fin.last ℓ) (oracleIdx := OracleFrontierIndex.mkFromStmtIdx (Fin.last ℓ))
      (oStmt := oStmt) (challenges := challenges) j →
    incrementalBadEventAtLast 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (ϑ := ϑ) oStmt challenges j := by
  intro h_j_bad
  unfold incrementalBadEventAtLast
  unfold foldingBadEventAtBlock at h_j_bad
  dsimp [oraclePositionToDomainIndex] at h_j_bad ⊢
  have h_le : j.val * ϑ + ϑ ≤ ℓ := by
    exact oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ) (i := Fin.last ℓ) (j := j)
  have hk : min ϑ (ℓ - j.val * ϑ) = ϑ := by
    omega
  simp only [OracleFrontierIndex.val_mkFromStmtIdx, Fin.val_last, h_le, ↓reduceDIte] at h_j_bad
  let blockStartIdx : Fin r := ⟨j.val * ϑ, by
    exact lt_r_of_lt_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ((oraclePositionToDomainIndex (ℓ := ℓ) (ϑ := ϑ) j).isLt)⟩
  let destIdx : Fin r := ⟨j.val * ϑ + ϑ, by
    exact lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) h_le⟩
  let rChallenges : Fin ϑ → L := fun cId => challenges ⟨j.val * ϑ + cId.val, by
    change j.val * ϑ + cId.val < ℓ
    omega⟩
  convert
      (incrementalFoldingBadEvent_eq_foldingBadEvent_of_k_eq_ϑ
        (𝔽q := 𝔽q) (β := β) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (ϑ := ϑ) (block_start_idx := blockStartIdx)
        (midIdx := destIdx) (destIdx := destIdx)
        (h_midIdx := rfl) (h_destIdx := rfl) (h_destIdx_le := h_le)
        (f_block_start := oStmt j)
        (r_challenges := rChallenges)).2 h_j_bad using 1
  · apply Fin.ext
    simp [destIdx, hk]
  · exact
      @lastRoundChallengeSlice_heq r L _ _ _ _ ℓ 𝓡 ϑ ‹NeZero ℓ› ‹NeZero ϑ›
        challenges j (min ϑ (ℓ - j.val * ϑ)) hk
        (Nat.min_le_right ϑ (ℓ - j.val * ϑ)) h_le

set_option maxHeartbeats 200000 in
lemma incrementalBadEvent_last_imp_foldingBadEventAtBlock
    (oStmt : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j)
    (challenges : Fin (Fin.last ℓ) → L)
    (j : Fin (toOutCodewordsCount ℓ ϑ (OracleFrontierIndex.mkFromStmtIdx (Fin.last ℓ)).val))
    (h_j_inc_bad : incrementalBadEventAtLast 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (ϑ := ϑ) oStmt challenges j) :
    foldingBadEventAtBlock 𝔽q β
      (stmtIdx := Fin.last ℓ) (oracleIdx := OracleFrontierIndex.mkFromStmtIdx (Fin.last ℓ))
      (oStmt := oStmt) (challenges := challenges) j := by
  unfold incrementalBadEventAtLast at h_j_inc_bad
  dsimp [oraclePositionToDomainIndex] at h_j_inc_bad
  have h_le : j.val * ϑ + ϑ ≤ ℓ := by
    exact oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ) (i := Fin.last ℓ) (j := j)
  have hk : min ϑ (ℓ - j.val * ϑ) = ϑ := by
    omega
  let blockStartIdx : Fin r := ⟨j.val * ϑ, by
    exact lt_r_of_lt_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ((oraclePositionToDomainIndex (ℓ := ℓ) (ϑ := ϑ) j).isLt)⟩
  let destIdx : Fin r := ⟨j.val * ϑ + ϑ, by
    exact lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) h_le⟩
  let rChallenges : Fin ϑ → L := fun cId => challenges ⟨j.val * ϑ + cId.val, by
    change j.val * ϑ + cId.val < ℓ
    omega⟩
  have h_j_inc_bad' :
      incrementalFoldingBadEvent 𝔽q β blockStartIdx ϑ (h_k_le := le_refl ϑ)
        (midIdx := destIdx) (destIdx := destIdx)
        (h_midIdx := rfl) (h_destIdx := rfl) (h_destIdx_le := h_le)
        (f_block_start := oStmt j)
        (r_challenges := rChallenges) := by
    convert h_j_inc_bad using 1
    · apply Fin.ext
      simp [destIdx, hk]
    · exact hk.symm
    · exact HEq.symm <|
        @lastRoundChallengeSlice_heq r L _ _ _ _ ℓ 𝓡 ϑ ‹NeZero ℓ› ‹NeZero ϑ›
          challenges j (min ϑ (ℓ - j.val * ϑ)) hk
          (Nat.min_le_right ϑ (ℓ - j.val * ϑ)) h_le
  have h_bad :
      foldingBadEvent 𝔽q β blockStartIdx ϑ
        (destIdx := destIdx)
        (h_destIdx := rfl) (h_destIdx_le := by exact h_le)
        (f_i := oStmt j)
        (r_challenges := rChallenges) := by
    exact
      (incrementalFoldingBadEvent_eq_foldingBadEvent_of_k_eq_ϑ
        (𝔽q := 𝔽q) (β := β) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (ϑ := ϑ) (block_start_idx := blockStartIdx)
        (midIdx := destIdx) (destIdx := destIdx)
        (h_midIdx := rfl) (h_destIdx := rfl) (h_destIdx_le := by
          exact h_le)
        (f_block_start := oStmt j)
        (r_challenges := rChallenges)).1 h_j_inc_bad'
  unfold foldingBadEventAtBlock
  dsimp [oraclePositionToDomainIndex]
  simp only [OracleFrontierIndex.val_mkFromStmtIdx, Fin.val_last, h_le, ↓reduceDIte]
  exact h_bad

lemma badEventExistsProp_iff_incrementalBadEventExistsProp_last
    (oStmt : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j)
    (challenges : Fin (Fin.last ℓ) → L) :
    blockBadEventExistsProp 𝔽q β
      (stmtIdx := Fin.last ℓ) (oracleIdx := OracleFrontierIndex.mkFromStmtIdx (Fin.last ℓ))
      (oStmt := oStmt) (challenges := challenges) ↔
    incrementalBadEventExistsProp 𝔽q β
      (stmtIdx := Fin.last ℓ) (oracleIdx := OracleFrontierIndex.mkFromStmtIdx (Fin.last ℓ))
      (oStmt := oStmt) (challenges := challenges) := by
  constructor
  · intro h_bad
    rcases h_bad with ⟨j, h_j_bad⟩
    refine ⟨j, ?_⟩
    exact foldingBadEventAtBlock_imp_incrementalBadEvent_last
      (𝔽q := 𝔽q) (β := β) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (ϑ := ϑ) oStmt challenges j h_j_bad
  · intro h_inc_bad
    rcases h_inc_bad with ⟨j, h_j_inc_bad⟩
    refine ⟨j, ?_⟩
    exact incrementalBadEvent_last_imp_foldingBadEventAtBlock
      (𝔽q := 𝔽q) (β := β) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (ϑ := ϑ) oStmt challenges j h_j_inc_bad

def badSumcheckEventProp
    (r_i' : L) (h_i h_star : L → L) :=
  h_i ≠ h_star ∧ h_i r_i' = h_star r_i'
section SingleStepRelationPreservationLemmas

section FoldStepPreservationLemmas
variable {Context : Type} {mp : SumcheckMultiplierParam L ℓ Context}

end FoldStepPreservationLemmas

section CommitStepPreservationLemmas

lemma incrementalBadEventExistsProp_relay_preserved (i : Fin ℓ) (hNCR : ¬ isCommitmentRound ℓ ϑ i)
    (oStmt : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j)
    (challenges : Fin i.succ → L) :
    incrementalBadEventExistsProp 𝔽q β i.succ (OracleFrontierIndex.mkFromStmtIdxCastSuccOfSucc i)
      oStmt challenges ↔
    incrementalBadEventExistsProp 𝔽q β i.succ (OracleFrontierIndex.mkFromStmtIdx i.succ)
      (mapOStmtOutRelayStep 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hNCR oStmt) challenges := by
  have h_count : toOutCodewordsCount ℓ ϑ i.castSucc = toOutCodewordsCount ℓ ϑ i.succ := by
    simp [toOutCodewordsCount_succ_eq, hNCR]
  constructor
  · rintro ⟨j, hj⟩
    refine ⟨Fin.cast h_count j, ?_⟩
    have hj' := hj
    simp only [incrementalBadEventExistsProp, mapOStmtOutRelayStep,
      OracleFrontierIndex.val_mkFromStmtIdx, OracleFrontierIndex.val_mkFromStmtIdxCastSuccOfSucc,
      h_count] at hj' ⊢
    exact hj'
  · rintro ⟨j, hj⟩
    refine ⟨Fin.cast h_count.symm j, ?_⟩
    have hj' := hj
    simp only [incrementalBadEventExistsProp, mapOStmtOutRelayStep,
      OracleFrontierIndex.val_mkFromStmtIdx, OracleFrontierIndex.val_mkFromStmtIdxCastSuccOfSucc,
      h_count] at hj' ⊢
    exact hj'

-- (moved to Basic.lean) declarations canonicalized in Basic: removed duplicates here.
lemma incrementalBadEventExistsProp_commit_step_backward (i : Fin ℓ) (hCR : isCommitmentRound ℓ ϑ i)
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j)
    (newOracle : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (domainIdx := ⟨i.val + 1, by omega⟩))
    (challenges : Fin i.succ → L) :
    incrementalBadEventExistsProp 𝔽q β i.succ (OracleFrontierIndex.mkFromStmtIdx i.succ)
      (snoc_oracle 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h_destIdx := rfl)
        oStmtIn newOracle) challenges →
    incrementalBadEventExistsProp 𝔽q β i.succ (OracleFrontierIndex.mkFromStmtIdxCastSuccOfSucc i)
      oStmtIn challenges := by
  intro h_bad
  rcases h_bad with ⟨j, hj_bad⟩
  by_cases hj_lt : j.val < toOutCodewordsCount ℓ ϑ i.castSucc
  · refine ⟨⟨j.val, hj_lt⟩, ?_⟩
    unfold incrementalBadEventExistsProp at hj_bad ⊢
    dsimp [OracleFrontierIndex.val_mkFromStmtIdx,
      OracleFrontierIndex.val_mkFromStmtIdxCastSuccOfSucc] at hj_bad ⊢
    simpa [snoc_oracle, hj_lt] using hj_bad
  · exfalso
    unfold incrementalBadEventExistsProp at hj_bad
    dsimp [OracleFrontierIndex.val_mkFromStmtIdx] at hj_bad
    have h_count_succ :
        toOutCodewordsCount ℓ ϑ i.succ = toOutCodewordsCount ℓ ϑ i.castSucc + 1 := by
      simp only [toOutCodewordsCount_succ_eq, hCR, ↓reduceIte]
    have hj_eq : j.val = toOutCodewordsCount ℓ ϑ i.castSucc := by
      have hj_le : j.val ≤ toOutCodewordsCount ℓ ϑ i.castSucc := by
        rw [← Nat.lt_succ_iff, ← h_count_succ]
        exact j.isLt
      have hj_ge : toOutCodewordsCount ℓ ϑ i.castSucc ≤ j.val := by
        simpa only [not_lt] using hj_lt
      omega
    have h_domain : j.val * ϑ = i.succ.val := by
      rw [hj_eq]
      exact toOutCodewordsCount_mul_ϑ_eq_i_succ ℓ ϑ (i := i) (hCR := hCR)
    have hk : min ϑ (i.succ.val - j.val * ϑ) = 0 := by
      rw [h_domain]
      simp
    exact
      (incrementalFoldingBadEvent_of_k_eq_0_is_false 𝔽q β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (ϑ := ϑ)
        (block_start_idx := ⟨oraclePositionToDomainIndex (ℓ := ℓ) (ϑ := ϑ)
          (positionIdx := j), by omega⟩)
        (k := min ϑ (i.succ.val - j.val * ϑ))
        (h_k := hk)
        (midIdx := ⟨j.val * ϑ + min ϑ (i.succ.val - j.val * ϑ), by omega⟩)
        (destIdx := ⟨j.val * ϑ + ϑ, by
          dsimp only [oraclePositionToDomainIndex]
          omega⟩)
        (h_midIdx := by dsimp [oraclePositionToDomainIndex]; omega)
        (h_destIdx := rfl)
        (h_destIdx_le := oracle_index_add_steps_le_ℓ ℓ ϑ
          (i := (OracleFrontierIndex.mkFromStmtIdx i.succ).val) (j := j))
        (f_block_start := by
          simpa [OracleStatement, oraclePositionToDomainIndex, snoc_oracle, hj_lt, hCR]
            using (snoc_oracle 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              (h_destIdx := rfl) oStmtIn newOracle j))
        (r_challenges := fun cId => challenges ⟨j.val * ϑ + cId.val, by
          have h_k_le_stmt :
              min ϑ (i.succ.val - j.val * ϑ) ≤ i.succ.val - j.val * ϑ :=
            Nat.min_le_right ϑ (i.succ.val - j.val * ϑ)
          have h_cId_lt_k : cId.val < min ϑ (i.succ.val - j.val * ϑ) := cId.isLt
          omega⟩)) hj_bad

lemma oracleFoldingConsistencyProp_commit_step_backward (i : Fin ℓ) (hCR : isCommitmentRound ℓ ϑ i)
    (challenges : Fin i.succ.val → L)
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j)
    (newOracle : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (domainIdx := ⟨i.val + 1, by omega⟩)) :
    oracleFoldingConsistencyProp 𝔽q β (i := i.succ) challenges
      (snoc_oracle 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h_destIdx := rfl)
        oStmtIn newOracle) →
    oracleFoldingConsistencyProp 𝔽q β (i := i.castSucc) (Fin.init challenges) oStmtIn := by
  intro h j hj
  have h_count_succ :
      toOutCodewordsCount ℓ ϑ i.succ = toOutCodewordsCount ℓ ϑ i.castSucc + 1 := by
    simp only [toOutCodewordsCount_succ_eq, hCR, ↓reduceIte]
  let j' : Fin (toOutCodewordsCount ℓ ϑ i.succ) := ⟨j.val, by
    rw [h_count_succ]
    omega⟩
  have hj' : j'.val + 1 < toOutCodewordsCount ℓ ϑ i.succ := by
    dsimp [j']
    rw [h_count_succ]
    omega
  have h_old := h j' hj'
  have hj_lt : j'.val < toOutCodewordsCount ℓ ϑ i.castSucc := by
    dsimp [j']
    exact j.isLt
  have hj_next_lt : j'.val + 1 < toOutCodewordsCount ℓ ϑ i.castSucc := by
    dsimp [j']
    exact hj
  simp only [oracleFoldingConsistencyProp, snoc_oracle, hj_lt, hj_next_lt,
    getFoldingChallenges_init_succ_eq] at h_old ⊢
  exact h_old

end CommitStepPreservationLemmas

end SingleStepRelationPreservationLemmas
-- (moved to Basic.lean) declarations canonicalized in Basic: removed duplicates here.
def finalSumcheckStepOracleConsistencyProp {h_le : ϑ ≤ ℓ}
    (stmtOut : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
  (oStmtOut : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ
    (Fin.last ℓ) j) : Prop :=
  let j := getLastOraclePositionIndex (ℓ := ℓ) (ϑ := ϑ) (Fin.last ℓ)
  let k := j.val * ϑ
  have h_k: k = ℓ - ϑ := by
    dsimp only [k, j]
    rw [getLastOraclePositionIndex_last]
    rw [Nat.sub_mul, Nat.one_mul]
    rw [Nat.div_mul_cancel (hdiv.out)]
  let f_k : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ⟨oraclePositionToDomainIndex ℓ ϑ j, by omega⟩ := by
    simpa [OracleStatement, oraclePositionToDomainIndex] using oStmtOut j
  let challenges : Fin ϑ → L := fun cId => stmtOut.challenges ⟨k + cId, by
      simp only [Fin.val_last, k, j]
      rw [getLastOraclePositionIndex_last, Nat.sub_mul, Nat.one_mul, Nat.div_mul_cancel (hdiv.out)]
      rw [Nat.sub_add_eq_sub_sub_rev (h1:=by omega) (h2:=by omega)]; omega
    ⟩
    let finalOracleFoldingConsistency: Prop := by
      exact isCompliant 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨k, by omega⟩) (steps := ϑ) (destIdx := ⟨k + ϑ, by omega⟩) (by rfl) (by simp only; omega) (f_i := f_k)
        (f_i_plus_steps := fun x => stmtOut.final_constant) (challenges := challenges)
    oracleFoldingConsistencyProp 𝔽q β (i := Fin.last ℓ)
        (challenges := stmtOut.challenges) (oStmt := oStmtOut)
      ∧ finalOracleFoldingConsistency

/-- This is a special case of nonDoomedFoldingProp for `i = ℓ`, where we support
the consistency between the last oracle `ℓ - ϑ` and the final constant `c`.
This definition has form similar to masterKState where there is no localChecks.
-/
def finalSumcheckStepFoldingStateProp {h_le : ϑ ≤ ℓ}
    (input : (FinalSumcheckStatementOut (L := L) (ℓ := ℓ) ×
      (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j)))
  :
    Prop :=
  let stmtOut := input.1
  let oStmtOut := input.2
  let j := getLastOraclePositionIndex (ℓ := ℓ) (ϑ := ϑ) (Fin.last ℓ)
  let k := j.val * ϑ
  have h_k: k = ℓ - ϑ := by
    dsimp only [k, j]
    rw [getLastOraclePositionIndex_last]
    rw [Nat.sub_mul, Nat.one_mul]
    rw [Nat.div_mul_cancel (hdiv.out)]
  let f_k : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ⟨oraclePositionToDomainIndex ℓ ϑ j, by omega⟩ := by
    simpa [OracleStatement, oraclePositionToDomainIndex] using oStmtOut j
  let challenges : Fin ϑ → L := fun cId => stmtOut.challenges ⟨k + cId, by
    simp only [Fin.val_last, k, j]
    rw [getLastOraclePositionIndex_last, Nat.sub_mul, Nat.one_mul, Nat.div_mul_cancel (hdiv.out)]
    rw [Nat.sub_add_eq_sub_sub_rev (h1:=by omega) (h2:=by omega)]; omega
  ⟩
  have h_k_add_ϑ: k + ϑ = ℓ := by rw [h_k]; apply Nat.sub_add_cancel; omega
  let oracleFoldingConsistency: Prop :=
    finalSumcheckStepOracleConsistencyProp 𝔽q β (h_le := h_le) (stmtOut := stmtOut)
      (oStmtOut := oStmtOut)
  let foldingBadEventExists : Prop := (blockBadEventExistsProp 𝔽q β (stmtIdx := Fin.last ℓ)
    (oracleIdx := OracleFrontierIndex.mkFromStmtIdx (Fin.last ℓ))
    (oStmt := oStmtOut) (challenges := stmtOut.challenges))
  oracleFoldingConsistency ∨ foldingBadEventExists

-- (moved to Basic.lean) declarations canonicalized in Basic: removed duplicates here.
def strictOracleFoldingConsistencyProp (t : MultilinearPoly L ℓ) (i : Fin (ℓ + 1))
    (challenges : Fin i → L)
    (oStmt : ∀ j, (OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i) j) : Prop :=
  letI : BEq L := inferInstance
  letI : LawfulBEq L := inferInstance
  let P₀ : CompPoly.CPolynomial L :=
    computablePolynomialFromNovelCoeffsF₂ (𝔽q := 𝔽q) (β := β) ℓ (by omega)
      (fun ω => t.val.eval (bitsOfIndex ω))
  let f₀ : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0 :=
    fun y => P₀.eval y.val
  ∀ (j : Fin (toOutCodewordsCount ℓ ϑ i)),
    let destIdx : Fin r := ⟨oraclePositionToDomainIndex (positionIdx := j), by
      have h_le := oracle_index_le_ℓ (i := i) (j := j); omega
    ⟩
    have h_k_next_le_i := oracle_block_k_le_i (i := i) (j := j);
      let fⱼ : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx := by
        simpa [OracleStatement, oraclePositionToDomainIndex, destIdx] using oStmt j
    let folded_func := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := 0) (steps := j * ϑ) (destIdx := destIdx) (h_destIdx := by
        dsimp only [Fin.coe_ofNat_eq_mod, destIdx]; simp only [zero_mod, zero_add])
      (h_destIdx_le := by have h_le := oracle_index_le_ℓ (i := i) (j := j); omega)
      (f := f₀) (r_challenges := getFoldingChallenges (r := r) (𝓡 := 𝓡) i
        challenges (k := 0) (ϑ := j * ϑ) (h := by omega))
    fⱼ = folded_func

def strictOracleWitnessConsistency
    (stmtIdx : Fin (ℓ + 1)) (oracleIdx : OracleFrontierIndex stmtIdx)
    (stmt : Statement (L := L) (Context := Context) stmtIdx)
    (wit : Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) stmtIdx)
    (oStmt : ∀ j, (OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ϑ (i := oracleIdx.val) j)) : Prop :=
  let witnessStructuralInvariant: Prop := witnessStructuralInvariant (i:=stmtIdx) 𝔽q β (mp := mp)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmt wit
  let strictOracleFoldingConsistency: Prop := strictOracleFoldingConsistencyProp 𝔽q β
    (t := wit.t) (i := oracleIdx.val)
    (challenges := Fin.take (m := oracleIdx.val) (v := stmt.challenges)
    (h := by simp only [Fin.val_fin_le, OracleFrontierIndex.val_le_i]))
    (oStmt := oStmt)
  witnessStructuralInvariant ∧ strictOracleFoldingConsistency

def strictRoundRelationProp (i : Fin (ℓ + 1))
    (input : (Statement (L := L) Context i ×
      (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i j)) ×
      Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) i)
    : Prop :=
  let stmt := input.1.1
  let oStmt := input.1.2
  let wit := input.2
  let sumCheckConsistency: Prop := sumcheckConsistencyProp (𝓑 := 𝓑) stmt.sumcheck_target wit.H
  let strictOracleWitnessConsistency: Prop := strictOracleWitnessConsistency 𝔽q β (mp := mp)
    (stmtIdx := i) (oracleIdx := OracleFrontierIndex.mkFromStmtIdx i) stmt wit oStmt
  sumCheckConsistency ∧ strictOracleWitnessConsistency

def strictFoldStepRelOutProp (i : Fin ℓ)
    (input : (Statement (L := L) Context i.succ ×
      (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j)) ×
      Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ)
        i.succ) : Prop :=
  let stmt := input.1.1
  let oStmt := input.1.2
  let wit := input.2
  let sumCheckConsistency: Prop := sumcheckConsistencyProp (𝓑 := 𝓑) stmt.sumcheck_target wit.H
  let strictOracleWitnessConsistency: Prop := strictOracleWitnessConsistency 𝔽q β (mp := mp)
    (stmtIdx := i.succ) (oracleIdx := OracleFrontierIndex.mkFromStmtIdxCastSuccOfSucc i)
    stmt wit oStmt
  sumCheckConsistency ∧ strictOracleWitnessConsistency

def strictfinalSumcheckStepFoldingStateProp (t : MultilinearPoly L ℓ) {h_le : ϑ ≤ ℓ}
    (input : (FinalSumcheckStatementOut (L := L) (ℓ := ℓ) ×
      (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j))) :
    Prop :=
  let stmt := input.1
  let oStmt := input.2
  let strictOracleFoldingConsistency: Prop :=
    strictOracleFoldingConsistencyProp 𝔽q β (t := t) (i := Fin.last ℓ)
      (challenges := stmt.challenges) (oStmt := oStmt)
  let lastDomainIdx := getLastOracleDomainIndex ℓ ϑ (Fin.last ℓ)
  have h_eq := getLastOracleDomainIndex_last (ℓ := ℓ) (ϑ := ϑ)
  let k := lastDomainIdx.val
  have h_k: k = ℓ - ϑ := by
    dsimp only [k, lastDomainIdx]
    rw [getLastOraclePositionIndex_last, Nat.sub_mul, Nat.one_mul, Nat.div_mul_cancel (hdiv.out)]
  let curDomainIdx : Fin r := ⟨k, by omega⟩
  have h_destIdx_eq: curDomainIdx.val = lastDomainIdx.val := rfl
  let f_k : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) curDomainIdx :=
    getLastOracle (h_destIdx := h_destIdx_eq) (oracleFrontierIdx := Fin.last ℓ)
      𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (oStmt := oStmt)
  let finalChallenges : Fin ϑ → L := fun cId => stmt.challenges ⟨k + cId, by
    rw [h_k]
    have h_le : ϑ ≤ ℓ := by apply Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ) (hdiv.out)
    have h_cId : cId.val < ϑ := cId.isLt
    have h_last : (Fin.last ℓ).val = ℓ := rfl
    omega
  ⟩
  let destDomainIdx : Fin r := ⟨k + ϑ, by omega⟩
  let strictFinalConstantConsistency: Prop :=
    (iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := curDomainIdx) (steps := ϑ)
      (destIdx := destDomainIdx) (h_destIdx := by rfl)
      (h_destIdx_le := by dsimp only [destDomainIdx]; omega) (f := f_k)
      (r_challenges := finalChallenges) = fun x => stmt.final_constant)
  strictOracleFoldingConsistency ∧ strictFinalConstantConsistency

def strictRoundRelation (i : Fin (ℓ + 1)) :
    Set ((Statement (L := L) Context i ×
      (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i j)) ×
      Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) i) :=
  { input | strictRoundRelationProp (mp := mp) (𝓑 := 𝓑) 𝔽q β i input}

def strictFoldStepRelOut (i : Fin ℓ) :
    Set ((Statement (L := L) Context i.succ ×
        (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j)) ×
      Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ)
        i.succ) :=
  { input | strictFoldStepRelOutProp (mp := mp) (𝓑 := 𝓑) 𝔽q β i input}

def strictFinalSumcheckRelOutProp
    (input : ((FinalSumcheckStatementOut (L := L) (ℓ := ℓ) ×
      (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j)) ×
      (Unit))) : Prop :=
  ∃ (t : MultilinearPoly L ℓ), strictfinalSumcheckStepFoldingStateProp 𝔽q β (t := t)
    (h_le := by apply Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ) (hdiv.out))
    (input := input.1)

def strictFinalSumcheckRelOut :
    Set ((FinalSumcheckStatementOut (L := L) (ℓ := ℓ) ×
      (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j)) ×
      (Unit)) :=
  { input | strictFinalSumcheckRelOutProp 𝔽q β input }

end SumcheckContextIncluded_Relations
end SecurityRelations

end Binius.BinaryBasefold
