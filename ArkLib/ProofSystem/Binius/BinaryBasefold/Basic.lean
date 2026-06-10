/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.ProofSystem.Binius.BinaryBasefold.Compliance
import ArkLib.ProofSystem.Sumcheck.Structured.SingleRound
import ArkLib.Data.MvPolynomial.MultilinearComputational

set_option linter.style.longFile 1900

/-!
# Binius binary Basefold: oracle bookkeeping

We set up the round/oracle indexing arithmetic for the binary-field Basefold protocol over `ℓ`
folding rounds committing every `ϑ` rounds. `toOutCodewordsCount` counts the codewords available
as oracles at each round and `isCommitmentRound` marks the commitment rounds; the bulk of the file
proves the arithmetic facts about these counts (e.g. `toOutCodewordsCount_succ_eq`,
`toOutCodewordsCount_last`) and the index-range bounds (`oracle_index_le_ℓ`,
`oracle_block_k_bound`, ...) used to address oracle positions and map them to domain indices via
`oraclePositionToDomainIndex` and `mkLastOracleIndex`.
-/

noncomputable section
namespace Binius.BinaryBasefold

open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial
  Binius.BinaryBasefold
open scoped NNReal
open ReedSolomon Code BerlekampWelch
open Finset AdditiveNTT Polynomial MvPolynomial Nat Matrix

/-- Binary expansion of an index as a challenge vector. -/
def bitsOfIndex {L : Type} [Field L] {n : ℕ} (k : Fin (2 ^ n)) : Fin n → L :=
  fun j => if Nat.getBit j.val k.val = 1 then 1 else 0

/-- Binary expansion of an index in statement-variable order.

The fold recursion consumes challenges in chronological order, while structured-sumcheck statements
store them newest-first. This helper converts a fold-order binary index into the corresponding
statement-order Boolean evaluation point. -/
def statementOrderBitsOfIndex {L : Type} [Field L] {n : ℕ} (k : Fin (2 ^ n)) : Fin n → L :=
  fun j => bitsOfIndex (L := L) k (Fin.rev j)

/-- Statement challenges are stored in the structured-sumcheck order: the newest challenge is at
index `0`. The folding operators consume challenges in chronological fold order, so this helper
exposes the fold-order view of a statement challenge vector. -/
def foldOrderChallenges {ℓ : ℕ} {L : Type} {i : Fin (ℓ + 1)}
    (challenges : Fin i → L) : Fin i → L :=
  fun j => challenges (Fin.rev j)

@[simp]
lemma foldOrderChallenges_cons {ℓ : ℕ} {L : Type} (i : Fin ℓ)
    (challenges : Fin i.castSucc → L) (r_i' : L) :
    foldOrderChallenges (ℓ := ℓ) (L := L) (i := i.succ)
      (Fin.cons (α := fun _ => L) r_i' challenges) =
    (fun j : Fin i.succ =>
        Fin.snoc (n := i.val) (α := fun _ => L)
          (foldOrderChallenges (ℓ := ℓ) (L := L) (i := i.castSucc) challenges) r_i' j) := by
  funext j
  induction j using Fin.lastCases with
  | last =>
      simp [foldOrderChallenges]
  | cast k =>
      simp [foldOrderChallenges, Fin.rev_castSucc]

/-- Extract the challenge vector belonging to an older oracle frontier from a later statement.

If `stmtIdx = oracleIdx + d`, the newest `d` statement challenges are not yet reflected in the
oracle frontier. Since statement vectors are newest-first, the older frontier is the suffix beginning
at offset `d`. -/
def olderStmtChallenges {ℓ : ℕ} {L : Type} {stmtIdx oracleIdx : Fin (ℓ + 1)}
    (h_le : oracleIdx.val ≤ stmtIdx.val) (challenges : Fin stmtIdx → L) :
    Fin oracleIdx → L :=
  fun j => challenges ⟨stmtIdx.val - oracleIdx.val + j.val, by
    have hj : j.val < oracleIdx.val := j.isLt
    omega⟩

@[simp]
lemma olderStmtChallenges_self {ℓ : ℕ} {L : Type} {i : Fin (ℓ + 1)}
    (challenges : Fin i → L) :
    olderStmtChallenges (ℓ := ℓ) (oracleIdx := i) (stmtIdx := i) (by rfl) challenges =
      challenges := by
  funext j
  simp only [olderStmtChallenges, Nat.sub_self, zero_add, Fin.eta]

@[simp]
lemma olderStmtChallenges_cons_castSucc {ℓ : ℕ} {L : Type} (i : Fin ℓ)
    (challenges : Fin i.castSucc → L) (r_i' : L) :
    olderStmtChallenges (ℓ := ℓ) (stmtIdx := i.succ) (oracleIdx := i.castSucc)
      (by simp only [Fin.val_succ, Fin.val_castSucc]; omega)
      (Fin.cons (α := fun _ => L) r_i' challenges) =
      challenges := by
  funext j
  simp only [olderStmtChallenges, Fin.val_succ, Fin.val_castSucc]
  let idx : Fin i.succ := ⟨i.val + 1 - i.val + j.val, by
      have hval : i.val + 1 - i.val + j.val = j.val + 1 := by
        rw [Nat.add_sub_cancel_left]
        exact Nat.add_comm 1 j.val
      simpa only [hval, Fin.val_succ] using j.succ.isLt⟩
  have hidx : idx = j.succ := by
    apply Fin.ext
    simp only [idx, Fin.val_succ]
    rw [Nat.add_sub_cancel_left]
    exact Nat.add_comm 1 j.val
  change (Fin.cons (n := i.val) (α := fun _ => L) r_i' challenges) idx = challenges j
  exact Eq.trans (congrArg (Fin.cons (n := i.val) (α := fun _ => L) r_i' challenges) hidx)
    (Fin.cons_succ (n := i.val) (α := fun _ => L) r_i' challenges j)

@[simp]
lemma olderStmtChallenges_succ_castSucc {ℓ : ℕ} {L : Type} (i : Fin ℓ)
    (challenges : Fin i.succ → L) :
    olderStmtChallenges (ℓ := ℓ) (stmtIdx := i.succ) (oracleIdx := i.castSucc)
      (by simp only [Fin.val_succ, Fin.val_castSucc]; omega) challenges =
      Fin.tail challenges := by
  rw [← Fin.cons_self_tail challenges]
  exact olderStmtChallenges_cons_castSucc i (Fin.tail challenges)
    (challenges ⟨0, by simp only [Fin.val_succ]; omega⟩)

section OracleStatementIndex
variable (ℓ : ℕ) (ϑ : ℕ) [NeZero ℓ] [NeZero ϑ] [hdiv : Fact (ϑ ∣ ℓ)]

lemma div_add_one_eq_if_dvd (i ϑ : ℕ) [NeZero ϑ] :
    (i + 1) / ϑ = if ϑ ∣ i + 1 then i / ϑ + 1 else i / ϑ := by
  split_ifs with h_dvd
  case pos => exact Nat.succ_div_of_dvd h_dvd
  case neg => exact Nat.succ_div_of_not_dvd h_dvd

def toOutCodewordsCount (i : Fin (ℓ + 1)) : ℕ := by
  -- the number of codewords available as oracle at state `i` (at the beginning of round `i`)
  exact i/ϑ + (if (i < ℓ) then 1 else 0)

def isCommitmentRound (i : Fin ℓ) : Prop :=
  ϑ ∣ i.val + 1 ∧ i.val + 1 ≠ ℓ

omit [NeZero ϑ] hdiv in
lemma toOutCodewordsCountOf0 : toOutCodewordsCount ℓ ϑ 0 = 1 := by
  unfold toOutCodewordsCount
  simp only [Fin.coe_ofNat_eq_mod, zero_mod, Nat.zero_div, zero_add, ite_eq_left_iff, not_lt,
    nonpos_iff_eq_zero, zero_ne_one, imp_false]
  exact NeZero.ne ℓ

instance instNeZeroNatToOutCodewordsCount : ∀ i, NeZero (toOutCodewordsCount ℓ ϑ i) := by
  intro i
  have h_ne_0: toOutCodewordsCount ℓ ϑ i ≠ 0 := by
    simp only [toOutCodewordsCount]
    by_cases h_i_lt_ℓ: i.val < ℓ
    · simp only [h_i_lt_ℓ, ↓reduceIte]; apply Nat.succ_ne_zero
    · simp only [h_i_lt_ℓ, ↓reduceIte, add_zero, ne_eq, Nat.div_eq_zero_iff, not_or, not_lt]
      constructor
      · exact NeZero.ne ϑ
      · have h_i: i = ℓ := by omega
        rw [h_i]; apply Nat.le_of_dvd (by exact pos_of_neZero ℓ) (hdiv.out)
  exact NeZero.mk h_ne_0

omit [NeZero ϑ] [NeZero ℓ] hdiv in
lemma toCodewordsCount_mul_ϑ_le_i (i : Fin (ℓ + 1)) :
    ∀ j: Fin (toOutCodewordsCount ℓ ϑ i), j.val * ϑ ≤
    (if i.val < ℓ then i.val else ℓ - ϑ) := by
  intro j
  split_ifs with h_il
  -- Case 1: i.val < ℓ
  case pos =>
    have hj : j.val ≤ i.val / ϑ := by
      apply Nat.lt_succ_iff.mp
      have hj_lt := j.isLt
      unfold toOutCodewordsCount at hj_lt
      simp only [h_il, ↓reduceIte] at hj_lt
      omega
    have h_mul := Nat.mul_le_mul_right ϑ hj
    exact h_mul.trans (Nat.div_mul_le_self i.val ϑ)
  -- Case 2: ¬(i.val < ℓ), which means i.val = ℓ
  case neg =>
    have h_ival_eq_l : i.val = ℓ := by omega
    have hj : j.val < ℓ / ϑ := by
      apply Nat.lt_succ_iff.mp
      have hj_lt := j.isLt
      unfold toOutCodewordsCount at hj_lt
      simp only [h_il, ↓reduceIte, add_zero] at hj_lt
      apply Nat.succ_lt_succ
      calc j.val < i.val / ϑ := by omega
        _ = _ := by congr
    have hj : j.val ≤ ℓ / ϑ - 1 := by apply Nat.le_sub_one_of_lt hj
    have h_mul := Nat.mul_le_mul_right ϑ hj
    rw [Nat.mul_sub_right_distrib, one_mul] at h_mul
    exact h_mul.trans (Nat.sub_le_sub_right (Nat.div_mul_le_self ℓ ϑ) ϑ)

omit hdiv in
lemma toOutCodewordsCount_succ_eq_add_one_iff (i : Fin ℓ) :
    isCommitmentRound ℓ ϑ i ↔
    (toOutCodewordsCount ℓ ϑ i.castSucc) + 1 = toOutCodewordsCount ℓ ϑ i.succ := by
  have h_i_succ: i.val + 1 = i.succ.val := rfl
  rw [isCommitmentRound, h_i_succ]
  constructor
  · intro h_i_transition
    unfold toOutCodewordsCount
    -- We know i.val < ℓ because i : Fin ℓ. We also know i.succ.val < ℓ from the hypothesis.
    have h_i_lt_l : i.val < ℓ := i.isLt
    have h_succ_lt_l : i.succ.val < ℓ := by
      apply Nat.lt_of_le_of_ne
      · omega
      · intro h_eq
        apply h_i_transition.2
        exact h_eq
    -- Simplify the expression using the known inequalities
    simp only [Fin.coe_castSucc, h_i_lt_l, ↓reduceIte, Fin.val_succ]
    ring_nf
    simp only [Fin.val_succ] at h_succ_lt_l
    rw [add_comm] at h_succ_lt_l
    simp only [h_succ_lt_l, ↓reduceIte]
    rw [add_comm 1 i.val]
    let k := (i + 1) / ϑ
    have h_k: (i + 1) / ϑ = k := rfl
    have h_k_mul_v: k * ϑ = i + 1 := by
      rw [mul_comm]
      rw [Nat.mul_div_eq_iff_dvd]
      exact h_i_transition.1
    have h_v_ne_0: ϑ ≠ 0 := by exact Ne.symm (NeZero.ne' ϑ)
    have h_k_gt_0: k > 0 := by
      by_contra h
      simp only [gt_iff_lt, not_lt, nonpos_iff_eq_zero] at h
      have h_i_add_1_eq_0: i.val + 1 = 0 := by
        simp only [h, Nat.div_eq_zero_iff, h_v_ne_0, false_or] at h_k -- h_k : ↑i + 1 < ϑ
        have h_v_ne_i_add_1: ϑ ≤ i.val + 1 := by
          apply Nat.le_of_dvd (by
            simp only [Fin.val_succ, lt_add_iff_pos_left, add_pos_iff, Fin.val_pos_iff, zero_lt_one,
              or_true]
          ) h_i_transition.1
        linarith -- h_v_ne_i_add_1 and h_k
      linarith
    have h_i_div_ϑ : i / ϑ = k - 1 := by
      apply Nat.div_eq_of_lt_le ?_ ?_
      · -- ⊢ (k - 1) * ϑ ≤ ↑i
        apply Nat.le_of_add_le_add_right (b:=ϑ)
        calc
          _ = (k - 1) * ϑ + 1 * ϑ := by omega
          _ = (k - 1 + 1) * ϑ := by exact Eq.symm (Nat.add_mul (k - 1) 1 ϑ)
          _ = i.val + 1 := by rw [←h_k_mul_v]; congr; omega -- uses h_k_gt_0
          _ ≤ i.val + ϑ := by apply Nat.add_le_add_left; omega
      · -- ⊢ ↑i < (k - 1 + 1) * ϑ
        rw [Nat.sub_one_add_one (by omega), h_k_mul_v]; omega
    rw [h_i_div_ϑ, h_k, add_comm]
    omega
  · -- ⊢ toOutCodewordsCount ℓ ϑ i.castSucc + 1 = toOutCodewordsCount ℓ ϑ i.succ →
    -- ϑ ∣ ↑i.succ ∧ i.succ ≠ ⟨ℓ, ⋯⟩
    intro h_eq
    constructor
    · -- Prove ϑ ∣ ↑i.succ
      unfold toOutCodewordsCount at h_eq
      have h_i_lt_l : i.val < ℓ := i.isLt
      simp only [Fin.coe_castSucc, h_i_lt_l, ↓reduceIte, Fin.val_succ] at h_eq
      -- We have: i / ϑ + 1 + 1 = (i + 1) / ϑ + (if i + 1 < ℓ then 1 else 0)
      by_cases h_succ_lt_l : i.val + 1 < ℓ
      · -- Case: i.succ < ℓ
        simp only [h_succ_lt_l, ↓reduceIte] at h_eq
        -- Now we have: i / ϑ + 2 = (i + 1) / ϑ + 1
        -- So: i / ϑ + 1 = (i + 1) / ϑ
        have h_div_eq : i.val / ϑ + 1 = (i.val + 1) / ϑ := by omega
        -- Use div_add_one_eq_if_dvd: (i + 1) / ϑ = if ϑ ∣ i + 1 then i / ϑ + 1 else i / ϑ
        have h_from_lemma := div_add_one_eq_if_dvd i.val ϑ
        rw [h_from_lemma] at h_div_eq
        -- If ϑ ∣ (i + 1), then i / ϑ + 1 = i / ϑ + 1 ✓
        -- If ¬(ϑ ∣ (i + 1)), then i / ϑ + 1 = i / ϑ, which gives 1 = 0 ✗
        by_cases h_dvd_case : ϑ ∣ (i.val + 1)
        · exact h_dvd_case
        · simp [h_dvd_case] at h_div_eq
      · -- Case: ¬(i.succ < ℓ), so i.succ.val = ℓ
        simp only [h_succ_lt_l, ↓reduceIte] at h_eq
        -- Now we have: i / ϑ + 2 = (i + 1) / ϑ
        have h_i_succ_eq_l : i.val + 1 = ℓ := by omega
        -- Use div_add_one_eq_if_dvd: (i + 1) / ϑ = if ϑ ∣ i + 1 then i / ϑ + 1 else i / ϑ
        have h_from_lemma := div_add_one_eq_if_dvd i.val ϑ
        -- Substitute the lemma directly into h_eq
        rw [h_from_lemma] at h_eq
        -- If ϑ ∣ (i + 1), then i / ϑ + 2 = i / ϑ + 1, which gives 2 = 1 ✗
        -- If ¬(ϑ ∣ (i + 1)), then i / ϑ + 2 = i / ϑ, which gives 2 = 0 ✗
        by_cases h_dvd_case : ϑ ∣ (i.val + 1)
        · -- If ϑ ∣ (i + 1), then we have our goal since i.succ.val = i.val + 1
          rw [Fin.val_succ]
          exact h_dvd_case
        · -- If ¬(ϑ ∣ (i + 1)), then h_eq becomes: i / ϑ + 2 = i / ϑ, so 2 = 0
          simp [h_dvd_case] at h_eq
          -- This gives us 2 = 0, which is impossible
          omega
    · -- Prove i.succ ≠ ⟨ℓ, ⋯⟩
      intro h_eq_l
      -- But i : Fin ℓ means i.val < ℓ, so i.succ.val = i.val + 1 ≤ ℓ
      -- If i.succ.val = ℓ, then i.val = ℓ - 1
      have h_i_eq : i.val = ℓ - 1 := by
        have h_succ : i.succ.val = i.val + 1 := by simp [Fin.val_succ]
        rw [h_eq_l] at h_succ
        omega
      -- Now check if the equation can hold
      unfold toOutCodewordsCount at h_eq
      have h_i_lt_l : i.val < ℓ := i.isLt
      simp only [Fin.coe_castSucc, h_i_lt_l, ↓reduceIte, Fin.val_succ] at h_eq
      -- We know that i.succ.val = ℓ, so i.val + 1 = ℓ, which means i.val + 1 ≮ ℓ
      have h_not_lt : ¬(i.val + 1 < ℓ) := by
        have h_succ_val : i.succ.val = i.val + 1 := by
          simp only [Fin.val_succ]
        rw [h_eq_l] at h_succ_val
        omega
      simp only [h_not_lt, ↓reduceIte] at h_eq
      -- We get: i / ϑ + 2 = ℓ / ϑ
      rw [h_i_eq] at h_eq
      -- So: (ℓ - 1) / ϑ + 2 = ℓ / ϑ
      -- Simplify the arithmetic first
      ring_nf at h_eq
      -- Now h_eq is: 2 + (ℓ - 1) / ϑ = (1 + (ℓ - 1)) / ϑ
      -- Note that 1 + (ℓ - 1) = ℓ
      have h_simp : 1 + (ℓ - 1) = ℓ := by omega
      rw [h_simp] at h_eq
      -- Use div_add_one_eq_if_dvd: ℓ / ϑ = if ϑ ∣ ℓ then (ℓ - 1) / ϑ + 1 else (ℓ - 1) / ϑ
      have h_ℓ_pos : 0 < ℓ := by omega -- since i.val < ℓ and i.val = ℓ - 1 ≥ 0
      have h_from_lemma := div_add_one_eq_if_dvd (ℓ - 1) ϑ
      -- Rewrite ℓ as (ℓ - 1) + 1 in the division
      have h_ℓ_div : ℓ = (ℓ - 1) + 1 := by omega
      rw [h_ℓ_div, h_from_lemma] at h_eq
      -- If ϑ ∣ ℓ, then (ℓ - 1) / ϑ + 2 = (ℓ - 1) / ϑ + 1, so 2 = 1 ✗
      -- If ¬(ϑ ∣ ℓ), then (ℓ - 1) / ϑ + 2 = (ℓ - 1) / ϑ, so 2 = 0 ✗
      by_cases h_dvd_ℓ : ϑ ∣ ℓ
      · -- If ϑ ∣ ℓ, then the if-then-else becomes (ℓ - 1) / ϑ + 1
        -- First simplify the arithmetic in h_eq
        have h_arith : ℓ - 1 + 1 - 1 = ℓ - 1 := by omega
        rw [h_arith] at h_eq
        -- Now simplify the if-then-else using h_dvd_ℓ
        have h_ℓ_eq : ℓ - 1 + 1 = ℓ := by omega
        rw [h_ℓ_eq] at h_eq
        simp [h_dvd_ℓ] at h_eq
        -- h_eq is now: 2 + (ℓ - 1) / ϑ = (ℓ - 1) / ϑ + 1
        -- This simplifies to: 2 = 1, which is impossible
        omega
      · -- If ¬(ϑ ∣ ℓ), then the if-then-else becomes (ℓ - 1) / ϑ
        -- First simplify the arithmetic in h_eq
        have h_arith : ℓ - 1 + 1 - 1 = ℓ - 1 := by omega
        rw [h_arith] at h_eq
        -- Now simplify the if-then-else using h_dvd_ℓ
        have h_ℓ_eq : ℓ - 1 + 1 = ℓ := by omega
        rw [h_ℓ_eq] at h_eq
        simp [h_dvd_ℓ] at h_eq
        -- h_eq is now: 2 + (ℓ - 1) / ϑ = (ℓ - 1) / ϑ
        -- This simplifies to: 2 = 0, which is impossible

open Classical in
lemma toOutCodewordsCount_succ_eq (i : Fin ℓ) :
    (toOutCodewordsCount ℓ ϑ i.succ) =
    if isCommitmentRound ℓ ϑ i then (toOutCodewordsCount ℓ ϑ i.castSucc) + 1
    else (toOutCodewordsCount ℓ ϑ i.castSucc) := by
  have h_succ_val: i.succ.val = i.val + 1 := rfl
  by_cases hv: ϑ ∣ i.val + 1 ∧ i.val + 1 ≠ ℓ
  · have h_succ := (toOutCodewordsCount_succ_eq_add_one_iff ℓ ϑ i).mp hv
    rw [←h_succ];
    simp only [left_eq_ite_iff, Nat.add_eq_left, one_ne_zero, imp_false, Decidable.not_not]
    exact hv
  · rw [isCommitmentRound]
    simp [ne_eq, hv, ↓reduceIte]
    unfold toOutCodewordsCount
    have h_i_lt_ℓ: i.castSucc.val < ℓ := by
      change i.val < ℓ
      omega
    simp only [Fin.val_succ, Fin.coe_castSucc, Fin.is_lt, ↓reduceIte]
    rw [div_add_one_eq_if_dvd]
    by_cases hv_div_succ: ϑ ∣ i.val + 1
    · simp only [hv_div_succ, ↓reduceIte, Nat.add_eq_left, ite_eq_right_iff, one_ne_zero,
      imp_false, not_lt, ge_iff_le]
      simp only [hv_div_succ, ne_eq, true_and, Decidable.not_not] at hv
      have h_eq: i.succ.val = ℓ := by
        change i.succ.val = (⟨ℓ, by omega⟩: Fin (ℓ + 1)).val
        exact hv
      omega
    · simp only [hv_div_succ, ↓reduceIte, Nat.add_left_cancel_iff, ite_eq_left_iff, not_lt,
      zero_ne_one, imp_false, not_le, gt_iff_lt]
      if hi_succ_lt: i.succ.val < ℓ then
        omega
      else
        simp only [Fin.val_succ, not_lt] at hi_succ_lt
        have hi_succ_le_ℓ: i.succ.val ≤ ℓ := by omega
        have hi_succ_eq_ℓ: i.val + 1 = ℓ := by omega
        rw [hi_succ_eq_ℓ] at hv_div_succ
        exact False.elim (hv_div_succ (hdiv.out))

lemma toOutCodewordsCount_i_le_of_succ (i : Fin ℓ) :
    toOutCodewordsCount ℓ ϑ i.castSucc ≤ toOutCodewordsCount ℓ ϑ i.succ := by
  rw [toOutCodewordsCount_succ_eq ℓ ϑ]
  split_ifs
  · omega
  · omega

lemma toOutCodewordsCount_last ℓ ϑ : toOutCodewordsCount ℓ ϑ (Fin.last ℓ) = ℓ / ϑ := by
  unfold toOutCodewordsCount
  simp only [Fin.val_last, lt_self_iff_false, ↓reduceIte, add_zero]

omit [NeZero ℓ] hdiv in
/--
If a new oracle is committed at round `i + 1` (i.e., `ϑ ∣ i + 1`), then the index of this
new oracle (which is the count of oracles from the previous round, `i`) multiplied by `ϑ`
equals the current round number `i + 1`.
The proof uses the commitment-round hypothesis to recover divisibility at `i + 1`.
-/
lemma toOutCodewordsCount_mul_ϑ_eq_i_succ (i : Fin ℓ) (hCR : isCommitmentRound ℓ ϑ i) :
    (toOutCodewordsCount ℓ ϑ i.castSucc) * ϑ = i.val + 1 := by
  unfold toOutCodewordsCount
  simp only [Fin.coe_castSucc, i.isLt, ↓reduceIte]
  have h_mod : i.val % ϑ = ϑ - 1 := by
    refine (mod_eq_sub_iff ?_ ?_).mpr hCR.1
    · omega
    · exact NeZero.one_le
  -- After unfolding, we have: (i.val / ϑ + 1) * ϑ = i.val + 1
  rw [Nat.add_mul, one_mul]
  -- Now we have: (i.val / ϑ) * ϑ + ϑ = i.val + 1
  -- Since ϑ ∣ (i.val + 1), we can use Nat.div_mul_cancel
  -- ⊢ ↑i / ϑ * ϑ + ϑ = ↑i + 1
  rw [Nat.div_mul_self_eq_mod_sub_self, h_mod]
  rw [←Nat.sub_add_comm (k:=ϑ - 1) (m:=ϑ) (by
    calc _ = i.val % ϑ := by omega
      _ ≤ i := by exact Nat.mod_le (↑i) ϑ
  )]
  -- ⊢ ↑i + ϑ - (ϑ - 1) = ↑i + 1
  rw [Nat.sub_sub_right (a:=i.val + ϑ) (b:=ϑ) (c:=1) (by exact NeZero.one_le)]
  omega

lemma toCodewordsCount_mul_ϑ_lt_ℓ (ℓ ϑ : ℕ) [NeZero ϑ] [NeZero ℓ] (i : Fin (ℓ + 1)) :
    ∀ j: Fin (toOutCodewordsCount ℓ ϑ i), j.val * ϑ < ℓ := by
  intro j
  unfold toOutCodewordsCount
  have h_j_lt : j.val < i.val / ϑ + if i.val < ℓ then 1 else 0 := j.2
  have h_j_mul_ϑ_lt := toCodewordsCount_mul_ϑ_le_i ℓ ϑ i j
  calc
    ↑j * ϑ ≤ if ↑i < ℓ then ↑i else ℓ - ϑ := by omega
    _ < _ := by
      by_cases h_i_lt_ℓ : i.val < ℓ
      · -- Case 1: i.val < ℓ
        simp only [h_i_lt_ℓ, ↓reduceIte]
      · -- Case 2: ¬(i.val < ℓ), which means i.val = ℓ
        simp only [h_i_lt_ℓ, ↓reduceIte, tsub_lt_self_iff]
        constructor
        · exact pos_of_neZero ℓ
        · exact pos_of_neZero ϑ

omit hdiv in
/-- The base index k = j * ϑ is less than ℓ for valid oracle indices -/
@[simp]
lemma oracle_block_k_bound (i : Fin (ℓ + 1)) (j : Fin (toOutCodewordsCount ℓ ϑ i)) :
    j.val * ϑ < ℓ :=
  toCodewordsCount_mul_ϑ_lt_ℓ ℓ ϑ i j

omit [NeZero ℓ] [NeZero ϑ] hdiv in
/-- The base index k = j * ϑ is less than or equal to i -/
@[simp]
lemma oracle_block_k_le_i (i : Fin (ℓ + 1)) (j : Fin (toOutCodewordsCount ℓ ϑ i))
    : j.val * ϑ ≤ i := by
  have h := toCodewordsCount_mul_ϑ_le_i ℓ ϑ i j
  by_cases hi : i < ℓ <;> simp only [hi, ↓reduceIte] at h <;> omega

/-- The next oracle index k + ϑ = (j+1) * ϑ is at most i -/
@[simp]
lemma oracle_block_k_next_le_i (i : Fin (ℓ + 1)) (j : Fin (toOutCodewordsCount ℓ ϑ i))
    (hj : j.val + 1 < toOutCodewordsCount ℓ ϑ i) : j.val * ϑ + ϑ ≤ i := by
  have h := toCodewordsCount_mul_ϑ_le_i ℓ ϑ i (j + 1)
  rw [Fin.val_add_one' (h_a_add_1:=hj), Nat.add_mul, Nat.one_mul] at h
  by_cases hi : i < ℓ <;> simp only [hi, ↓reduceIte] at h <;> omega

omit [NeZero ℓ] [NeZero ϑ] in
/-- For any oracle position j, the domain index j*ϑ plus ϑ steps is at most ℓ.
This is a key bound for proving fiber-wise closeness requirements. -/
@[simp]
lemma oracle_index_add_steps_le_ℓ (i : Fin (ℓ + 1))
    (j : Fin (toOutCodewordsCount ℓ ϑ i)) :
    j.val * ϑ + ϑ ≤ ℓ := by
  unfold toOutCodewordsCount
  by_cases h : i < ℓ
  · -- Case: i < ℓ, so toOutCodewordsCount = i/ϑ + 1
    have hj_bound : j.val < i / ϑ + 1 := by
      have : toOutCodewordsCount ℓ ϑ i = i / ϑ + 1 := by simp [toOutCodewordsCount, h]
      rw [← this]; exact j.isLt
    rw [← Nat.add_one_mul]
    apply Nat.le_trans (Nat.mul_le_mul_right ϑ (Nat.succ_le_of_lt hj_bound))
    apply Nat.mul_le_of_le_div
    apply Nat.succ_le_of_lt
    apply Nat.div_lt_of_lt_mul; rw [mul_comm]
    rw [Nat.div_mul_cancel hdiv.out]
    exact h
  · -- Case: i ≥ ℓ, so toOutCodewordsCount = i/ϑ
    have hj_bound : j.val < i / ϑ := by
      have : toOutCodewordsCount ℓ ϑ i = i / ϑ := by simp [toOutCodewordsCount, h]
      rw [← this]; exact j.isLt
    calc j.val * ϑ + ϑ
        = (j.val + 1) * ϑ := by rw [Nat.add_mul, Nat.one_mul]
      _ ≤ (i / ϑ) * ϑ := by gcongr; omega
      _ ≤ i := Nat.div_mul_le_self i ϑ
      _ ≤ ℓ := Fin.is_le i

omit [NeZero ℓ] [NeZero ϑ] in
/-- For any oracle position j, the domain index j*ϑ is at most ℓ.
This is a key bound for proving fiber-wise closeness requirements. -/
@[simp]
lemma oracle_index_le_ℓ (i : Fin (ℓ + 1))
    (j : Fin (toOutCodewordsCount ℓ ϑ i)) :
    j.val * ϑ ≤ ℓ := by
  have h_le := oracle_index_add_steps_le_ℓ ℓ ϑ i j
  omega

/-- Convert oracle position index to oracle domain index by multiplying by ϑ.
The position index j corresponds to the j-th oracle in the list of committed oracles,
and the domain index is j*ϑ, which is the actual index in the Fin ℓ domain. -/
@[reducible]
def oraclePositionToDomainIndex {i : Fin (ℓ + 1)}
    (positionIdx : Fin (toOutCodewordsCount ℓ ϑ i)) : Fin ℓ :=
  ⟨positionIdx.val * ϑ, oracle_block_k_bound ℓ ϑ i positionIdx⟩

def mkLastOracleIndex (i : Fin (ℓ + 1)) : Fin (toOutCodewordsCount ℓ ϑ i) := by
  have hv: ϑ ∣ ℓ := by exact hdiv.out
  rw [toOutCodewordsCount]
  if hi: i.val < ℓ then
    exact ⟨i.val / ϑ, by simp only [hi, ↓reduceIte, lt_add_iff_pos_right, zero_lt_one];⟩
  else
    have hi_eq_ℓ: i.val = ℓ := by omega
    exact ⟨ℓ/ϑ - 1 , by
      simp_rw [hi_eq_ℓ]
      simp only [lt_self_iff_false, ↓reduceIte, add_zero, tsub_lt_self_iff, Nat.div_pos_iff,
        zero_lt_one, and_true]
      constructor
      · exact pos_of_neZero ϑ
      · apply Nat.le_of_dvd (h:=by exact pos_of_neZero ℓ); omega
    ⟩

lemma mkLastOracleIndex_last : mkLastOracleIndex ℓ ϑ (Fin.last ℓ) = ℓ / ϑ - 1 := by
  dsimp only [mkLastOracleIndex, Fin.val_last, lt_self_iff_false, Lean.Elab.WF.paramLet,
    eq_mpr_eq_cast, cast_eq]
  simp only [lt_self_iff_false, ↓reduceDIte]
  rfl

def getLastOraclePositionIndex (i : Fin (ℓ + 1)) :
    Fin (toOutCodewordsCount ℓ ϑ i) := by
  let ne0 := (instNeZeroNatToOutCodewordsCount ℓ ϑ i).out
  exact ⟨(toOutCodewordsCount ℓ ϑ i) - 1, by omega⟩

@[reducible]
def getLastOracleDomainIndex (oracleFrontierIdx : Fin (ℓ + 1)) :
    Fin (ℓ) :=
  oraclePositionToDomainIndex (positionIdx := (getLastOraclePositionIndex ℓ ϑ oracleFrontierIdx))

lemma mkLastOracleIndex_eq_getLastOraclePositionIndex (i : Fin (ℓ + 1)) :
    mkLastOracleIndex ℓ ϑ i = getLastOraclePositionIndex ℓ ϑ i := by
  unfold mkLastOracleIndex getLastOraclePositionIndex
  apply Fin.eq_of_val_eq
  by_cases hi : i.val < ℓ
  · simp only [hi, ↓reduceDIte]
    unfold toOutCodewordsCount
    simp only [hi, ↓reduceIte]
    rfl
  · simp only [hi, ↓reduceDIte]
    unfold toOutCodewordsCount
    simp only [hi, eq_mpr_eq_cast, cast_eq, ↓reduceIte, add_zero];
    have h_eq: i.val = ℓ := by omega
    rw [h_eq]

lemma getLastOraclePositionIndex_last : getLastOraclePositionIndex ℓ ϑ (Fin.last ℓ)
    = ⟨ℓ / ϑ - 1, by
    dsimp only [toOutCodewordsCount, Fin.val_last, lt_self_iff_false];
    simp only [lt_self_iff_false,
      ↓reduceIte, add_zero, tsub_lt_self_iff, Nat.div_pos_iff, zero_lt_one, and_true]
    constructor
    · exact pos_of_neZero ϑ
    · apply Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ); exact hdiv.out
    ⟩ := by
  apply Fin.eq_of_val_eq
  dsimp only [getLastOraclePositionIndex, Fin.val_last, lt_self_iff_false, Lean.Elab.WF.paramLet]
  rw [toOutCodewordsCount_last]

lemma getLastOracleDomainIndex_last : getLastOracleDomainIndex ℓ ϑ (Fin.last ℓ)
    = ⟨ℓ - ϑ, by
    have h_ne_0 : 0 < ϑ := by exact pos_of_neZero ϑ
    have h_lt: ϑ ≤ ℓ := by apply Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ); exact hdiv.out
    omega⟩ := by
  apply Fin.eq_of_val_eq
  dsimp only [getLastOracleDomainIndex]
  rw [getLastOraclePositionIndex_last]; simp only;
  rw [Nat.sub_mul, Nat.one_mul]
  rw [Nat.div_mul_cancel (hdiv.out)]

lemma getLastOracleDomainIndex_add_ϑ_le (i : Fin (ℓ + 1)) :
    (getLastOracleDomainIndex ℓ ϑ i).val + ϑ ≤ ℓ := by
  rw [getLastOracleDomainIndex, oraclePositionToDomainIndex]
  simp only [oracle_index_add_steps_le_ℓ]

end OracleStatementIndex

-- The structured-sumcheck primitives (`MultilinearPoly`, `MultiquadraticPoly`,
-- `SumcheckMultiplierParam`, `computeInitialSumcheckPoly`, `projectToMidSumcheckPoly`,
-- `projectToNextSumcheckPoly`) now live in `ArkLib.ProofSystem.Sumcheck.Structured`.
-- We re-export them under the `Binius.BinaryBasefold` namespace so that existing
-- references — qualified or unqualified — continue to resolve.
-- See `GENERIC_RING_SWITCHING_PLAN.md` §1.5 for the rationale.
export Sumcheck.Structured (MultilinearPoly MultiquadraticPoly
  SumcheckMultiplierParam computeInitialSumcheckPoly
  projectToMidSumcheckPoly projectToNextSumcheckPoly)

/-- Computable multilinear polynomial from hypercube evaluations (`CMvPolynomial` / `CMLE'`).
See `MvPolynomial.Computational.fromCMvPolynomial_CMLE'_eq_MLE'`. -/
def MultilinearPoly.ofCMLEEvals {L : Type} [CommRing L] [BEq L] [LawfulBEq L] {ℓ : ℕ}
    (evals : Fin (2 ^ ℓ) → L) : MultilinearPoly L ℓ :=
  ⟨CPoly.fromCMvPolynomial (MvPolynomial.Computational.CMLE' evals), by
    rw [MvPolynomial.Computational.fromCMvPolynomial_CMLE'_eq_MLE']
    unfold MLE'
    exact MLE_mem_restrictDegree (evals ∘ finFunctionFinEquiv)⟩

theorem MultilinearPoly.ofCMLEEvals_val {L : Type} [CommRing L] [BEq L] [LawfulBEq L] {ℓ : ℕ}
    (evals : Fin (2 ^ ℓ) → L) :
    (ofCMLEEvals evals).val = MLE' evals := by
  simpa [ofCMLEEvals] using MvPolynomial.Computational.fromCMvPolynomial_CMLE'_eq_MLE' evals

/-- Same carrier as `⟨MLE evals, MLE_mem_restrictDegree evals⟩`, built via `CMLE'`. -/
def MultilinearPoly.ofHypercubeEvals {L : Type} [CommRing L] [BEq L] [LawfulBEq L] {ℓ : ℕ}
    (evals : (Fin ℓ → Fin 2) → L) : MultilinearPoly L ℓ :=
  ofCMLEEvals (fun i => evals (finFunctionFinEquiv.symm i))

theorem MultilinearPoly.ofHypercubeEvals_val {L : Type} [CommRing L] [BEq L] [LawfulBEq L] {ℓ : ℕ}
    (evals : (Fin ℓ → Fin 2) → L) :
    (ofHypercubeEvals evals).val = MLE evals := by
  rw [ofHypercubeEvals, ofCMLEEvals_val, MLE']
  congr 1
  funext x
  simp only [Function.comp_apply, Equiv.symm_apply_apply]

theorem MultilinearPoly.ofCMLEEvals_eval_zeroOne {L : Type} [CommRing L] [BEq L] [LawfulBEq L] {ℓ : ℕ}
    (evals : Fin (2 ^ ℓ) → L) (x : Fin ℓ → Fin 2) :
    MvPolynomial.eval (x : Fin ℓ → L) (ofCMLEEvals evals).val = evals (finFunctionFinEquiv x) := by
  simpa [ofCMLEEvals_val] using MLE'_eval_zeroOne x evals

theorem MultilinearPoly.ofCMLEEvals_cmEval_eq_val_eval {L : Type} [CommRing L] [BEq L] [LawfulBEq L]
    {ℓ : ℕ} (evals : Fin (2 ^ ℓ) → L) (x : Fin ℓ → Fin 2) :
    CPoly.CMvPolynomial.eval (x : Fin ℓ → L) (MvPolynomial.Computational.CMLE' evals) =
      MvPolynomial.eval (x : Fin ℓ → L) (ofCMLEEvals evals).val := by
  rw [CPoly.eval_equiv]
  simpa [ofCMLEEvals]

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
  -- [SampleableType L] => not used
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))] [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ 𝓡 ϑ : ℕ} (γ_repetitions : ℕ) [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ] -- Should we allow ℓ = 0?
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r} -- ℓ ∈ {1, ..., r-1}
variable {𝓑 : Fin 2 ↪ L}
variable [hdiv : Fact (ϑ ∣ ℓ)]

section IndexBounds
omit hdiv in
/-- ϑ is positive -/
lemma folding_steps_pos : (ϑ : ℕ) > 0 := pos_of_neZero ϑ

omit hdiv in
/-- ℓ - ϑ < ℓ when both are positive -/
lemma rounds_sub_steps_lt : ℓ - ϑ < ℓ :=
  Nat.sub_lt (pos_of_neZero ℓ) (folding_steps_pos)

lemma ϑ_sub_one_le_self : ϑ - 1 < ϑ := by
  have lt_0: ϑ > 0 := by exact Nat.pos_of_neZero ϑ
  exact Nat.sub_one_lt_of_lt lt_0

@[simp] -- main lemma for bIdx: Fin (ℓ / ϑ - 1) bounds
lemma bIdx_mul_ϑ_add_x_lt_ℓ_sub_ϑ (bIdx : Fin (ℓ / ϑ - 1)) (x : ℕ) {hx : x ≤ ϑ} :
    ↑bIdx * ϑ + x ≤ ℓ - ϑ := by
  have h_x_lt : x < ϑ + 1 := Nat.lt_succ_of_le hx
  have h_fin : x < ϑ ∨ x = ϑ := Nat.lt_or_eq_of_le hx
  calc
    ↑bIdx * ϑ + x ≤ ↑bIdx * ϑ + ϑ := by omega
    _ = (↑bIdx + 1) * ϑ := by rw [Nat.add_mul, Nat.one_mul]
    _ ≤ (ℓ / ϑ - 1) * ϑ := by gcongr; omega
    _ = ℓ - ϑ := by
      have h_bound : 1 ≤ ℓ / ϑ := by
        have h_le: ϑ ≤ ℓ := by apply Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ); exact hdiv.out
        rw [Nat.one_le_div_iff (by exact Nat.pos_of_neZero ϑ)]; exact h_le
      rw [Nat.sub_mul, Nat.one_mul, Nat.div_mul_cancel (hdiv.out)]
    _ ≤ ℓ - ϑ := by omega

@[simp]
lemma bIdx_mul_ϑ_add_i_lt_ℓ_succ {m : ℕ} (bIdx : Fin (ℓ / ϑ - 1)) (i : Fin ϑ) :
    ↑bIdx * ϑ + ↑i < ℓ + m :=
  calc
    _ ≤ ℓ - ϑ := by apply bIdx_mul_ϑ_add_x_lt_ℓ_sub_ϑ bIdx i.val (hx:=by omega)
    _ < ℓ := by exact rounds_sub_steps_lt
    _ ≤ ℓ + m := by omega

@[simp]
lemma bIdx_mul_ϑ_add_i_cast_lt_ℓ_succ (bIdx : Fin (ℓ / ϑ - 1)) (i : Fin (ϑ - 1 + 1))
    : ↑bIdx * ϑ + i < ℓ + 1 := by
  calc
    ↑bIdx * ϑ + i ≤ ℓ - ϑ := by apply bIdx_mul_ϑ_add_x_lt_ℓ_sub_ϑ bIdx (x:=i.val) (hx:=by omega)
    _ < ℓ + 1 := by omega

@[simp]
lemma bIdx_mul_ϑ_add_x_lt_ℓ_succ (bIdx : Fin (ℓ / ϑ - 1)) (x : ℕ) {hx : x ≤ ϑ} :
    ↑bIdx * ϑ + x < ℓ + 1 := by
  calc
    _ ≤ ℓ - ϑ := by apply bIdx_mul_ϑ_add_x_lt_ℓ_sub_ϑ bIdx x (hx:=hx)
    _ < ℓ + 1 := by omega

@[simp]
lemma bIdx_mul_ϑ_add_i_fin_ℓ_pred_lt_ℓ (bIdx : Fin (ℓ / ϑ - 1)) (i : Fin (ϑ - 1))
    : ↑bIdx * ϑ + ↑i < ℓ := by
  calc
    _ ≤ ℓ - ϑ := by apply bIdx_mul_ϑ_add_x_lt_ℓ_sub_ϑ bIdx i.val (hx:=by omega)
    _ < ℓ := by exact rounds_sub_steps_lt

/-- When the block size allows it, we can get a strict inequality -/
lemma bIdx_succ_mul_ϑ_lt_ℓ_succ (bIdx : Fin (ℓ / ϑ - 1)) :
    (↑bIdx + 1) * ϑ < ℓ + 1 := by
  calc
    (↑bIdx + 1) * ϑ = ↑bIdx * ϑ + ϑ := by rw [Nat.add_mul, Nat.one_mul]
    _ ≤ ℓ - ϑ := by apply bIdx_mul_ϑ_add_x_lt_ℓ_sub_ϑ bIdx ϑ (hx:=by omega)
    _ < ℓ + 1 := by omega

lemma bIdx_succ_mul_ϑ_le_ℓ_succ (bIdx : Fin (ℓ / ϑ - 1)) : (↑bIdx + 1) * ϑ ≤ ℓ + 1 := by
  exact Nat.le_of_lt (bIdx_succ_mul_ϑ_lt_ℓ_succ bIdx)
end IndexBounds

omit r L 𝔽q ℓ 𝓡 ϑ γ_repetitions [NeZero r] [Field L] [Fintype L]
  [DecidableEq L] [CharP L 2] [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  h_Fq_char_prime hF₂ [Algebra 𝔽q L] β hβ_lin_indep h_β₀_eq_1 [NeZero ℓ]
  [NeZero 𝓡] [NeZero ϑ] h_ℓ_add_R_rate 𝓑 hdiv in
/-- Oracle frontier index: captures valid oracle indices for a given statement index.
    In Binary Basefold, the oracle can be at most 1 index behind the statement index.
    - At statement index `i+1`, the oracle can be at `i` (after fold) or `i+1` (after commit)

`@[reducible]` so that the standard `Subtype` coercion applies at raw-`Fin (m + 1)`-keyed
call sites (e.g. `foldingBadEventAtBlock`'s `oracleIdx` slot): behind a non-reducible
`def` the elaborator cannot see the subtype to insert `↑`. -/
@[reducible]
def OracleFrontierIndex {m : ℕ} (stmtIdx : Fin (m + 1)) :=
  { val : Fin (m + 1) // val.val ≤ stmtIdx.val ∧ stmtIdx.val ≤ val.val + 1 }

namespace OracleFrontierIndex

omit r L 𝔽q ℓ 𝓡 ϑ γ_repetitions [NeZero r] [Field L] [Fintype L]
  [DecidableEq L] [CharP L 2] [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  h_Fq_char_prime hF₂ [Algebra 𝔽q L] β hβ_lin_indep h_β₀_eq_1 [NeZero ℓ]
  [NeZero 𝓡] [NeZero ϑ] h_ℓ_add_R_rate 𝓑 hdiv in
/-- Create oracle frontier index equal to statement index (synchronized case) -/
def mkFromStmtIdx {m : ℕ} (stmtIdx : Fin (m + 1)) :
    OracleFrontierIndex stmtIdx :=
  ⟨stmtIdx, by
    constructor
    · exact le_rfl
    · exact Nat.le_succ stmtIdx.val
  ⟩

omit r L 𝔽q ℓ 𝓡 ϑ γ_repetitions [NeZero r] [Field L] [Fintype L]
  [DecidableEq L] [CharP L 2] [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  h_Fq_char_prime hF₂ [Algebra 𝔽q L] β hβ_lin_indep h_β₀_eq_1 [NeZero ℓ]
  [NeZero 𝓡] [NeZero ϑ] h_ℓ_add_R_rate 𝓑 hdiv in
/-- Create oracle frontier index for statement i.succ with oracle at i (lagging case).
    Used after fold step where stmtIdx advances but oracle hasn't committed yet. -/
def mkFromStmtIdxCastSuccOfSucc {m : ℕ} (i : Fin m) :
    OracleFrontierIndex i.succ :=
  ⟨i.castSucc, by
    constructor
    · exact Nat.le_of_lt (by exact Nat.lt_add_one (i.castSucc).val)
    · simp only [Fin.val_succ, Fin.val_castSucc, le_refl]
  ⟩

omit r L 𝔽q ℓ 𝓡 ϑ γ_repetitions [NeZero r] [Field L] [Fintype L]
  [DecidableEq L] [CharP L 2] [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  h_Fq_char_prime hF₂ [Algebra 𝔽q L] β hβ_lin_indep h_β₀_eq_1 [NeZero ℓ]
  [NeZero 𝓡] [NeZero ϑ] h_ℓ_add_R_rate 𝓑 hdiv in
lemma val_mkFromStmtIdx {m : ℕ} (stmtIdx : Fin (m + 1)) :
    (mkFromStmtIdx (m := m) stmtIdx).val = stmtIdx := rfl

omit r L 𝔽q ℓ 𝓡 ϑ γ_repetitions [NeZero r] [Field L] [Fintype L]
  [DecidableEq L] [CharP L 2] [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  h_Fq_char_prime hF₂ [Algebra 𝔽q L] β hβ_lin_indep h_β₀_eq_1 [NeZero ℓ]
  [NeZero 𝓡] [NeZero ϑ] h_ℓ_add_R_rate 𝓑 hdiv in
lemma val_mkFromStmtIdxCastSuccOfSucc {m : ℕ} (i : Fin m) :
    (mkFromStmtIdxCastSuccOfSucc (m := m) i).val = i.castSucc := rfl

omit r L 𝔽q ℓ 𝓡 ϑ γ_repetitions [NeZero r] [Field L] [Fintype L]
  [DecidableEq L] [CharP L 2] [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  h_Fq_char_prime hF₂ [Algebra 𝔽q L] β hβ_lin_indep h_β₀_eq_1 [NeZero ℓ]
  [NeZero 𝓡] [NeZero ϑ] h_ℓ_add_R_rate 𝓑 hdiv in
lemma val_le_i {m : ℕ} (i : Fin (m + 1)) (oracleIdx : OracleFrontierIndex i) :
    oracleIdx.val ≤ i := by
  unfold OracleFrontierIndex at oracleIdx
  let h := oracleIdx.property
  cases h
  · exact h.left

omit r L 𝔽q ℓ 𝓡 ϑ γ_repetitions [NeZero r] [Field L] [Fintype L]
  [DecidableEq L] [CharP L 2] [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  h_Fq_char_prime hF₂ [Algebra 𝔽q L] β hβ_lin_indep h_β₀_eq_1 [NeZero ℓ]
  [NeZero 𝓡] [NeZero ϑ] h_ℓ_add_R_rate 𝓑 hdiv in
lemma val_mkFromStmtIdxCastSuccOfSucc_eq_mkFromStmtIdx {m : ℕ} (i : Fin m) :
    (mkFromStmtIdxCastSuccOfSucc (m := m) i).val =
      (mkFromStmtIdx (m := m) i.castSucc).val := by rfl

attribute [simp] val_mkFromStmtIdx val_mkFromStmtIdxCastSuccOfSucc val_le_i
  val_mkFromStmtIdxCastSuccOfSucc_eq_mkFromStmtIdx

end OracleFrontierIndex

section OracleReductionComponents
-- In this section, we use notation `ϑ` for the folding steps, along with `(hdiv : ϑ ∣ ℓ)`

/-!
## Core Protocol Structures

Basic structures and definitions used throughout the Binary Basefold protocol.
-/

-- `SumcheckBaseContext` and `Statement` now live in `ArkLib.ProofSystem.Sumcheck.Structured`.
-- Re-exported so existing references — qualified or unqualified — continue to resolve.
export Sumcheck.Structured (SumcheckBaseContext Statement)

/-- Statement for the final sumcheck step - includes the final constant c -/
structure FinalSumcheckStatementOut extends
  Statement (L := L) (Context := SumcheckBaseContext L ℓ) (Fin.last ℓ) where
  final_constant : L -- c = f^(ℓ)(0, ..., 0)

def toStatement (stmt : FinalSumcheckStatementOut (L := L) (ℓ := ℓ)) :
  Statement (L := L) (Context := SumcheckBaseContext L ℓ) (Fin.last ℓ) :=
  {
    sumcheck_target := stmt.sumcheck_target,
    challenges := stmt.challenges,
    ctx := stmt.ctx
  }

/-- For the `i`-th round of the protocol, there will be oracle statements corresponding
to all committed codewords. The verifier has oracle access to functions corresponding
to the handles in committed_handles. -/
@[reducible]
def OracleStatement (ϑ : ℕ) [NeZero ϑ] (i : Fin (ℓ + 1)) :
    Fin (toOutCodewordsCount ℓ ϑ (i:=i)) → Type := fun j =>
  by
    let sDomainIdx := j * ϑ
    have h_sDomainIdx_lt_ℓ : sDomainIdx < ℓ := by
      exact toCodewordsCount_mul_ϑ_lt_ℓ ℓ ϑ i j
    exact (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨sDomainIdx, by omega⟩ → L

def mapOStmtOutRelayStep (i : Fin ℓ) (hNCR : ¬ isCommitmentRound ℓ ϑ i)
    (oStmt : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j) :
    ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.succ j := fun j => by
  have h_oracle_size_eq: toOutCodewordsCount ℓ ϑ i.castSucc = toOutCodewordsCount ℓ ϑ i.succ := by
    simp only [toOutCodewordsCount_succ_eq ℓ ϑ i, hNCR, ↓reduceIte]
  -- oracle index mapping
  exact oStmt ⟨j, by rw [h_oracle_size_eq]; omega⟩

/-- The round witness for round `i` of `t ∈ L[≤ 2][X Fin ℓ]` and
`Hᵢ(Xᵢ, ..., Xₗ₋₁) := h(r₀', ..., rᵢ₋₁', Xᵢ, Xᵢ₊₁, ..., Xₗ₋₁) ∈ L[≤ 2][X Fin (ℓ-i)]`.
This ensures efficient computability and constraint on the structure of `H_i`
according to `t`.
-/
structure Witness (i : Fin (ℓ + 1)) where
  t : L⦃≤ 1⦄[X Fin ℓ] -- The original polynomial t
  H : L⦃≤ 2⦄[X Fin (ℓ - i)] -- Hᵢ
  f: (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨i, by omega⟩ → L -- fᵢ

/-- The extractor that recovers the multilinear polynomial t from f^(i) -/
noncomputable def extractMLP (i : Fin ℓ) (f : (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨i, by omega⟩ → L) :
    Option (L⦃≤ 1⦄[X Fin (ℓ - i)]) := by
  set domain_size := Fintype.card (sDomain 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩)
  set d := Code.distFromCode (u := f)
    (C := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
  let e: ℕ := d.toNat
  let k : ℕ := 2^(ℓ - i.val) -- degree bound from BBF_Code definition
  -- Convert domain to Fin format for Berlekamp-Welch
  let domain_to_fin : (sDomain 𝔽q β h_ℓ_add_R_rate)
    ⟨i, by omega⟩ ≃ Fin domain_size := by
    simp only [domain_size]
    rw [sDomain_card 𝔽q β h_ℓ_add_R_rate
      (i := ⟨i, by omega⟩) (h_i:=by apply Nat.lt_add_of_pos_right_of_le; simp only; omega), hF₂.out]
    have h_equiv := sDomainFinEquiv 𝔽q β h_ℓ_add_R_rate (i := ⟨i, by omega⟩)
      (h_i:=by apply Nat.lt_add_of_pos_right_of_le; simp only; omega)
    convert h_equiv
  -- ωs is the mapping from the point index to the actually point in the domain S^{i}
  let ωs : Fin domain_size → L := fun j => (domain_to_fin.symm j).val
  let f_vals : Fin domain_size → L := fun j => f (domain_to_fin.symm j)
  -- Run Berlekamp-Welch decoder to get P(X) in monomial basis
  have domain_neZero : NeZero domain_size := by
    simp only [domain_size];
    rw [sDomain_card 𝔽q β h_ℓ_add_R_rate
      (i := ⟨i, by omega⟩) (h_i:=by apply Nat.lt_add_of_pos_right_of_le; simp only; omega)]
    exact {
      out := by
        rw [hF₂.out]
        simp only [ne_eq, Nat.pow_eq_zero, OfNat.ofNat_ne_zero, false_and, not_false_eq_true]
    }
  -- Run Berlekamp-Welch decoder to get P(X) in monomial basis
  let berlekamp_welch_result: Option L[X] := BerlekampWelch.decoder e k ωs f_vals

  match berlekamp_welch_result with
  | none => exact none -- Decoder failed
  | some P =>
    -- 5. Check if degree < 2^ℓ (unique decoding condition)
    if hp_deg_lt: P.natDegree ≥ 2^(ℓ - i.val) then
      exact none -- Outside unique decoding radius
    else
      -- 6. Convert P(X) from monomial basis to novel polynomial basis
      -- P(X) = Σᵢ aᵢ Xᵢ (monomial) → P(X) = Σⱼ tⱼ X_{j}(X) (novel)
      -- We need the inverse of the change-of-basis matrix
      have h_deg_bound : P ∈ Polynomial.degreeLT L (2^(ℓ - i.val)) := by
        rw [Polynomial.mem_degreeLT]
        by_cases hi: i = ℓ
        · simp only [hi, tsub_self, pow_zero, cast_one]
          by_cases hp_p_eq_0: P = 0
          · simp only [hp_p_eq_0, degree_zero]; omega
          · simp only [hi, tsub_self, pow_zero, ge_iff_le, not_le, lt_one_iff] at hp_deg_lt
            have h_deg_p: P.degree = 0 := by omega
            simp only [h_deg_p]
            omega
        · by_cases hp_p_eq_0: P = 0
          · simp only [hp_p_eq_0];
            have h_i_lt_ℓ : i < ℓ := by omega
            simp only [degree_zero, cast_pow, cast_ofNat, gt_iff_lt]
            -- ⊢ ⊥ < 2 ^ (ℓ - ↑i)
            have h_deg_ne_bot : 2 ^ (ℓ - ↑i) ≠ ⊥ := by
              exact not_isBot_iff_ne_bot.mp fun a ↦ hp_deg_lt (a P.natDegree)
            exact compareOfLessAndEq_eq_lt.mp rfl
          · have h := Polynomial.natDegree_lt_iff_degree_lt (p:=P) (n:=2 ^ (ℓ - ↑i))
              (hp:=by exact hp_p_eq_0)
            rw [←h]; omega
      let P_bounded : L⦃<2^(ℓ - i.val)⦄[X] := ⟨P, h_deg_bound⟩
      -- Get monomial coefficients of P(X)
      let monomial_coeffs : Fin (2^(ℓ - i.val)) → L := fun i => P.coeff i.val
      -- Convert to novel polynomial basis coefficients using change of basis
      -- The changeOfBasisMatrix A has A[j,i] = coeff of X^i in novel basis vector X_j
      -- So we need A⁻¹ to convert monomial coeffs → novel coeffs
      let novel_coeffs : Option (Fin (2^(ℓ - i.val)) → L) :=
        let h_ℓ_le_r : ℓ ≤ r := by
          -- ℓ + 𝓡 < r implies ℓ < r, hence ℓ ≤ r
          have : ℓ < r := by omega
          exact Nat.le_of_lt this
        some (AdditiveNTT.monomialToNovelCoeffs 𝔽q β (ℓ - i.val) (by omega) monomial_coeffs)

      match novel_coeffs with
      | none => exact none
      | some t_coeffs =>
        -- Interpret novel coeffs as Lagrange cosefficients on Boolean hypercube
        -- and reconstruct the multilinear polynomial using MLE
        let hypercube_evals : (Fin (ℓ - i.val) → Fin 2) → L := fun w =>
          -- Map Boolean hypercube point w to its linear index
          let w_index : Fin (2^(ℓ - i.val)) := Nat.binaryFinMapToNat
            (n:=ℓ - i.val) (m:=w) (h_binary:=by intro j; simp only [Nat.cast_id]; omega)
          t_coeffs w_index

        let t_multilinear_mv := MvPolynomial.MLE hypercube_evals
        exact some ⟨t_multilinear_mv, MLE_mem_restrictDegree hypercube_evals⟩

def dummyLastWitness :
    Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) := {
  t := ⟨0, by apply zero_mem⟩,
  H := ⟨0, by apply zero_mem⟩,
  f := fun _ => 0
}

-- `InitialStatement` was orphaned by the `RingSwitching/` extraction (its sole consumer,
-- `RingSwitching.MLPEvalStatement`, now defines the same 2-field shape locally).
-- Removed as part of the post-extraction cleanup.

open Classical in
def snoc_oracle {i : Fin ℓ} {destIdx : Fin r}
    (h_destIdx : destIdx = ⟨i.val + 1, by omega⟩)
    (oStmtIn : ∀ j : Fin (toOutCodewordsCount ℓ ϑ i.castSucc),
      OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j)
    (newOracleFn : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx) :
    ∀ j : Fin (toOutCodewordsCount ℓ ϑ i.succ),
      OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.succ j := fun j =>
  have h_succ_val: i.succ.val = i.val + 1 := rfl
  if hj: j.val < (toOutCodewordsCount ℓ ϑ i.castSucc) then
    oStmtIn ⟨j, by omega⟩
  else -- j.val ≥ toOutCodewordsCount ℓ ϑ i.castSucc
    -- simp only [not_lt] at hj
    if hi: isCommitmentRound ℓ ϑ i then
      -- NEW PROOF --
      -- 1. Prove that the oracle count increases by exactly one.
      have h_count_succ : toOutCodewordsCount ℓ ϑ i.succ =
        toOutCodewordsCount ℓ ϑ i.castSucc + 1 := by
        exact Eq.symm ((fun ℓ ϑ [NeZero ℓ] [NeZero ϑ] i ↦
          (toOutCodewordsCount_succ_eq_add_one_iff ℓ ϑ i).mp) ℓ ϑ i hi)
      -- 2. Prove that j must be the index of the new, last oracle.
      have h_j_eq_last_idx : j.val = toOutCodewordsCount ℓ ϑ i.castSucc := by
        apply Nat.le_antisymm
        · rw [← Nat.lt_succ_iff]
          simp only [Nat.succ_eq_add_one]
          simp only [← h_count_succ, Fin.is_lt];
        · simp only [not_lt] at hj; exact hj
      have h_commit_round : j.val * ϑ = i.succ.val := by
        rw [h_j_eq_last_idx]
        -- This works iff i.succ < ℓ, since i.succ ≠ ℓ, this is TRUE
        have hi_succ_lt_ℓ: i.succ.val < ℓ := by
          have hi_succ_le_ℓ: i.succ.val ≤ ℓ := by omega
          have hi_succ_ne_ℓ: i.succ.val ≠ ℓ := by
            rw [h_succ_val]
            exact hi.2
          exact Nat.lt_of_le_of_ne hi_succ_le_ℓ hi_succ_ne_ℓ
        rw [toOutCodewordsCount_mul_ϑ_eq_i_succ ℓ ϑ i hi]
        rfl
      have h_domain :
          ↥(sDomain 𝔽q β h_ℓ_add_R_rate destIdx) =
            ↥(sDomain 𝔽q β h_ℓ_add_R_rate ⟨i.succ.val, by omega⟩) := by
        have h_fin : destIdx = (⟨i.succ.val, by omega⟩ : Fin r) := by
          apply Fin.eq_of_val_eq
          rw [h_destIdx]
          rfl
        exact congrArg (fun idx => ↥(sDomain 𝔽q β h_ℓ_add_R_rate idx)) h_fin
      cast (by
        simp only [OracleFunction, OracleStatement]
        simp_rw [h_commit_round]
        exact congrArg (fun D : Type => D → L) h_domain) newOracleFn
    else by
      simp only [OracleStatement]
      have h := toOutCodewordsCount_succ_eq ℓ ϑ i
      if hi_succ_eq_ℓ: i.succ.val = ℓ then
        have h_i_succ_eq: i.succ = ⟨ℓ, by omega⟩ := by
          apply Fin.eq_of_val_eq
          simp only [hi_succ_eq_ℓ]
        have h_count_eq: toOutCodewordsCount ℓ ϑ i.castSucc =
          toOutCodewordsCount ℓ ϑ i.succ := by
          simp only [hi, ↓reduceIte] at h
          exact h.symm
        have hj_lt: j.val < toOutCodewordsCount ℓ ϑ i.castSucc := by
          rw [h_count_eq]
          exact j.isLt
        linarith -- hj_lt and hj
      else
        simp only [isCommitmentRound, ne_eq, and_comm, not_and] at hi
        have hi_succ_ne_ℓ: i.succ ≠ ⟨ℓ, by omega⟩ := by
          apply Fin.ne_of_val_ne (by omega)
        have h_ne_v_div_i_succ := hi (by omega)
        have h_count_eq: toOutCodewordsCount ℓ ϑ i.castSucc =
          toOutCodewordsCount ℓ ϑ i.succ := by
          rw [h]; simp only [isCommitmentRound, ne_eq, right_eq_ite_iff, Nat.left_eq_add,
            one_ne_zero, imp_false, not_and, Decidable.not_not];
          intro hv_div_i_succ
          exact False.elim (hi (by omega) (hv_div_i_succ))
        have hj_lt: j.val < toOutCodewordsCount ℓ ϑ i.castSucc := by
          rw [h_count_eq]
          exact j.isLt
        linarith -- hj_lt and hj

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero 𝓡] in
lemma snoc_oracle_new_heq_of_commit {i : Fin ℓ} {destIdx : Fin r}
    (h_destIdx : destIdx = ⟨i.val + 1, by omega⟩)
    (hCR : isCommitmentRound ℓ ϑ i)
    (oStmtIn : ∀ j : Fin (toOutCodewordsCount ℓ ϑ i.castSucc),
      OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j)
    (newOracleFn : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx)
    (j : Fin (toOutCodewordsCount ℓ ϑ i.succ))
    (hj : ¬ j.val < toOutCodewordsCount ℓ ϑ i.castSucc) :
    HEq (snoc_oracle 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      h_destIdx oStmtIn newOracleFn j) newOracleFn := by
  subst h_destIdx
  unfold snoc_oracle
  simp only [hCR, hj, ↓reduceDIte]
  exact cast_heq _ newOracleFn

def take_snoc_oracle (i : Fin ℓ)
    (oStmtIn : (j : Fin (toOutCodewordsCount ℓ ϑ i.castSucc)) →
      OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j)
    {destIdx : Fin r} (h_destIdx : destIdx = ⟨i.val + 1, by omega⟩)
    (newOracleFn : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx) :
    (j : Fin (toOutCodewordsCount ℓ ϑ i.castSucc)) → -- We specify range type so Lean won't be stuck
      OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j
    := fun j => snoc_oracle 𝔽q β h_destIdx oStmtIn newOracleFn ⟨j, by
      have h : (toOutCodewordsCount ℓ ϑ i.castSucc) ≤ toOutCodewordsCount ℓ ϑ i.succ := by
        exact toOutCodewordsCount_i_le_of_succ ℓ ϑ i
      omega
    ⟩

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero 𝓡] in
lemma take_snoc_oracle_eq_oStmtIn (i : Fin ℓ)
    (oStmtIn : (j : Fin (toOutCodewordsCount ℓ ϑ i.castSucc)) →
      OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j)
    {destIdx : Fin r} (h_destIdx : destIdx = ⟨i.val + 1, by omega⟩)
    (newOracleFn : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx) :
    (take_snoc_oracle 𝔽q β i oStmtIn h_destIdx newOracleFn) = oStmtIn := by
  unfold take_snoc_oracle
  unfold snoc_oracle
  simp

/-- Extract the first oracle f^(0) from oracle statements -/
def getFirstOracle {i : Fin (ℓ + 1)}
    (oStmt : (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i j)) :
    sDomain 𝔽q β h_ℓ_add_R_rate 0 → L := by
  let rawf₀ := oStmt ⟨0, by
    letI := instNeZeroNatToOutCodewordsCount ℓ ϑ i
    exact pos_of_neZero (toOutCodewordsCount ℓ ϑ i)
  ⟩
  simp only [OracleStatement, zero_mul, Fin.mk_zero'] at rawf₀
  exact rawf₀

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero 𝓡] in
/-- The first oracle is preserved when appending a new oracle.

Since `getFirstOracle` extracts index 0, and `snoc_oracle` at index 0 always falls into
the old-oracle branch, the first oracle is unchanged. -/
lemma getFirstOracle_snoc_oracle
    (i : Fin ℓ) {destIdx : Fin r} (h_destIdx : destIdx = ⟨i.val + 1, by omega⟩)
    (oStmtIn : ∀ j : Fin (toOutCodewordsCount ℓ ϑ i.castSucc),
      OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j)
    (newOracleFn : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx) :
    getFirstOracle 𝔽q β (snoc_oracle 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      h_destIdx oStmtIn newOracleFn) = getFirstOracle 𝔽q β oStmtIn := by
  unfold getFirstOracle snoc_oracle
  have h_lt : 0 < toOutCodewordsCount ℓ ϑ i.castSucc := by
    have h := (instNeZeroNatToOutCodewordsCount ℓ ϑ i.castSucc).out
    omega
  simp only [Fin.mk_zero', h_lt, ↓reduceDIte]
  rfl

/-- Extract the last (most recently committed) oracle `f^(getLastOracleDomainIndex)` from the
oracle statements at frontier index `oracleFrontierIdx`, reindexed to the requested `destIdx`. -/
def getLastOracle {oracleFrontierIdx : Fin (ℓ + 1)} {destIdx : Fin r}
    (h_destIdx : destIdx.val = getLastOracleDomainIndex ℓ ϑ oracleFrontierIdx)
    (oStmt : (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ
      (i := oracleFrontierIdx) j)) :
    OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx :=
  let res := oStmt ⟨getLastOraclePositionIndex ℓ ϑ oracleFrontierIdx, by omega⟩
  have h_lt : getLastOracleDomainIndex ℓ ϑ oracleFrontierIdx < r := by omega
  have h_eq : destIdx = ⟨getLastOracleDomainIndex ℓ ϑ oracleFrontierIdx, h_lt⟩
    := Fin.eq_of_val_eq (by omega)
  fun y => res (cast (by rw [h_eq]) y)

section SecurityRelations

/-- Helper to get the k-th challenge slice for folding -/
def getFoldingChallenges (i : Fin (ℓ + 1)) (challenges : Fin i → L)
    (k : ℕ) (h : k + ϑ ≤ i) : Fin ϑ → L :=
  fun cId => foldOrderChallenges (ℓ := ℓ) challenges ⟨k + cId, by omega⟩

omit [NeZero r] [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
  [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ] hdiv in
lemma getFoldingChallenges_proof_irrel (i : Fin (ℓ + 1)) (challenges : Fin i → L)
    (k : ℕ) (h h' : k + ϑ ≤ i) :
    getFoldingChallenges (r := r) (𝓡 := 𝓡) (ϑ := ϑ) i challenges k h =
    getFoldingChallenges (r := r) (𝓡 := 𝓡) (ϑ := ϑ) i challenges k h' := by
  funext cId
  unfold getFoldingChallenges
  congr 1

omit [NeZero r] [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
  [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q] h_Fq_char_prime hF₂ [Algebra 𝔽q L]
  β hβ_lin_indep h_β₀_eq_1 [NeZero 𝓡] [NeZero ϑ] h_ℓ_add_R_rate 𝓑 in
/-- Splitting the full final-round fold-order challenge vector at the last oracle block recovers
the prefix challenge slice followed by the final block challenge slice. -/
lemma getFoldingChallenges_append_finalBlock
    (challenges : Fin (Fin.last ℓ) → L) :
    Fin.append
      (getFoldingChallenges (r := r) (𝓡 := 𝓡) (ϑ := ℓ - ϑ)
        (i := Fin.last ℓ) challenges 0 (h := by
          simp only [zero_add, Fin.val_last]
          omega))
      (getFoldingChallenges (r := r) (𝓡 := 𝓡) (ϑ := ϑ)
        (i := Fin.last ℓ) challenges (ℓ - ϑ) (h := by
          simp only [Fin.val_last]
          have h_le : ϑ ≤ ℓ := Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ) hdiv.out
          omega)) =
    fun cIdx : Fin ((ℓ - ϑ) + ϑ) =>
      foldOrderChallenges (ℓ := ℓ) (L := L) (i := Fin.last ℓ) challenges
        ⟨cIdx.val, by
          simp only [Fin.val_last]
          have h_le : ϑ ≤ ℓ := Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ) hdiv.out
          omega⟩ := by
  funext cIdx
  by_cases h : cIdx.val < ℓ - ϑ
  · have hcIdx : cIdx = Fin.castAdd ϑ ⟨cIdx.val, h⟩ := by
      apply Fin.ext
      simp
    rw [hcIdx, Fin.append_left]
    dsimp only [getFoldingChallenges]
    congr 1
    apply Fin.ext
    simp
  · have h_le : ℓ - ϑ ≤ cIdx.val := Nat.le_of_not_gt h
    let j : Fin ϑ := ⟨cIdx.val - (ℓ - ϑ), by
      have hϑ : ϑ ≤ ℓ := Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ) hdiv.out
      omega⟩
    have hcIdx : cIdx = Fin.natAdd (ℓ - ϑ) j := by
      apply Fin.ext
      simp only [j, Fin.val_natAdd]
      omega
    rw [hcIdx, Fin.append_right]
    dsimp only [getFoldingChallenges]
    congr 1

omit [NeZero r] [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
  [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ] hdiv in
lemma getFoldingChallenges_tail_castSucc_eq_of_le (i : Fin ℓ)
    (challenges : Fin i.succ → L) (k : ℕ)
    (h_old : k + ϑ ≤ ↑i.castSucc) (h_new : k + ϑ ≤ ↑i.succ) :
    getFoldingChallenges (r := r) (𝓡 := 𝓡) (ϑ := ϑ) i.castSucc
      (Fin.tail challenges) k (h := h_old) =
    getFoldingChallenges (r := r) (𝓡 := 𝓡) (ϑ := ϑ) i.succ
      challenges k (h := h_new) := by
  unfold getFoldingChallenges
  funext cId
  let idxOld : Fin i.castSucc := ⟨k + cId.val, by
    have hc : cId.val < ϑ := cId.isLt
    have h_old' : k + ϑ ≤ i.val := by
      simpa only [Fin.val_castSucc] using h_old
    omega⟩
  let idxNew : Fin i.succ := ⟨k + cId.val, by
    have hc : cId.val < ϑ := cId.isLt
    have h_new' : k + ϑ ≤ i.val + 1 := by
      simpa only [Fin.val_succ] using h_new
    omega⟩
  change foldOrderChallenges (ℓ := ℓ) (Fin.tail challenges) idxOld =
    foldOrderChallenges (ℓ := ℓ) challenges idxNew
  have hidx : idxNew = idxOld.castSucc := by
    apply Fin.ext
    rfl
  rw [hidx]
  unfold foldOrderChallenges
  have hrev : idxOld.castSucc.rev = idxOld.rev.succ := Fin.rev_castSucc idxOld
  exact (show Fin.tail challenges idxOld.rev = challenges idxOld.rev.succ from rfl).trans
    (congrArg challenges hrev).symm

omit [NeZero r] [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
  [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ] hdiv in
lemma getFoldingChallenges_older_castSucc_eq (i : Fin ℓ)
    (j : Fin (toOutCodewordsCount ℓ ϑ i.castSucc)) (challenges : Fin i.succ → L)
    (h_old : ↑j * ϑ + ϑ ≤ ↑i.castSucc)
    (h_new : ↑j * ϑ + ϑ ≤ ↑i.succ) :
    getFoldingChallenges (r := r) (𝓡 := 𝓡) (ϑ := ϑ) i.castSucc
      (olderStmtChallenges (ℓ := ℓ) (stmtIdx := i.succ) (oracleIdx := i.castSucc)
        (by simp only [Fin.val_succ, Fin.val_castSucc]; omega) challenges) (↑j * ϑ)
      (h := h_old) =
  getFoldingChallenges (r := r) (𝓡 := 𝓡) i.succ challenges (↑j * ϑ)
      (h := h_new) := by
  rw [olderStmtChallenges_succ_castSucc]
  unfold getFoldingChallenges
  funext cId
  have hle : j.val * ϑ + ϑ ≤ i.val := by
    simpa only [Fin.val_castSucc] using h_old
  let idxOld : Fin i.castSucc := ⟨j.val * ϑ + cId.val, by omega⟩
  let idxNew : Fin i.succ := ⟨j.val * ϑ + cId.val, by
    simp only [Fin.val_succ]
    omega⟩
  change foldOrderChallenges (ℓ := ℓ) (Fin.tail challenges) idxOld =
    foldOrderChallenges (ℓ := ℓ) challenges idxNew
  have hidx : idxNew = idxOld.castSucc := by
    apply Fin.ext
    rfl
  rw [hidx]
  unfold foldOrderChallenges
  have hrev : idxOld.castSucc.rev = idxOld.rev.succ := Fin.rev_castSucc idxOld
  exact (show Fin.tail challenges idxOld.rev = challenges idxOld.rev.succ from rfl).trans
    (congrArg challenges hrev).symm

omit [NeZero r] [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
  [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ] hdiv in
lemma getFoldingChallenges_tail_castSucc_eq (i : Fin ℓ)
    (j : Fin (toOutCodewordsCount ℓ ϑ i.castSucc)) (challenges : Fin i.succ → L)
    (h_old : ↑j * ϑ + ϑ ≤ ↑i.castSucc)
    (h_new : ↑j * ϑ + ϑ ≤ ↑i.succ) :
    getFoldingChallenges (r := r) (𝓡 := 𝓡) (ϑ := ϑ) i.castSucc
      (Fin.tail challenges) (↑j * ϑ) (h := h_old) =
    getFoldingChallenges (r := r) (𝓡 := 𝓡) i.succ challenges (↑j * ϑ)
      (h := h_new) := by
  rw [← olderStmtChallenges_succ_castSucc (i := i) (challenges := challenges)]
  exact getFoldingChallenges_older_castSucc_eq (r := r) (𝓡 := 𝓡) (ϑ := ϑ)
    i j challenges h_old h_new

def getNextOracle (i : Fin (ℓ + 1))
    (oStmt : ∀ j, (OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i) j)
    (j : Fin (toOutCodewordsCount ℓ ϑ i)) (hj : j.val + 1 < toOutCodewordsCount ℓ ϑ i)
    {destDomainIdx : Fin r} (h_destDomainIdx : destDomainIdx = j.val * ϑ + ϑ) :
    OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destDomainIdx :=
  let res := oStmt ⟨j.val + 1, hj⟩
  have h : j.val * ϑ + ϑ = (j.val + 1) * ϑ := by
    rw [Nat.add_mul, one_mul]
  have h_lt : (j.val + 1) * ϑ < r := by
    omega
  have h_eq : destDomainIdx = ⟨(j.val + 1) * ϑ, h_lt⟩ :=
    Fin.eq_of_val_eq (by
      simp only
      omega)
  fun y => res (cast (by rw [h_eq]) y)

/-- Folding consistency for round i (where i is the oracleIdx) -/
def oracleFoldingConsistencyProp (i : Fin (ℓ + 1)) (challenges : Fin i → L)
    (oStmt : ∀ j, (OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i) j) : Prop :=
  (∀ (j : Fin (toOutCodewordsCount ℓ ϑ i)) (hj : j.val + 1 < toOutCodewordsCount ℓ ϑ i),
    have h_k_bound := oracle_block_k_bound (ℓ := ℓ) (ϑ := ϑ) (i := i) (j := j)
    have h_k_next_le_i := oracle_block_k_next_le_i (ℓ := ℓ) (ϑ := ϑ) (i := i) (j := j) (hj := hj)
    let destIdx : Fin r := ⟨oraclePositionToDomainIndex (positionIdx := j) + ϑ, by
      have h_le := oracle_index_add_steps_le_ℓ ℓ ϑ (i := i) (j := j)
      dsimp only [oraclePositionToDomainIndex]
      omega
    ⟩
    isCompliant 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := ⟨oraclePositionToDomainIndex (positionIdx := j), by omega⟩) (steps := ϑ)
      (destIdx := destIdx) (by rfl) (by
        dsimp only [destIdx]; simp only [oracle_index_add_steps_le_ℓ])
      (f_i := by
        simpa [OracleStatement, oraclePositionToDomainIndex] using oStmt j)
      (f_i_plus_steps := getNextOracle 𝔽q β i oStmt j hj (destDomainIdx := destIdx)
        (h_destDomainIdx := by rfl))
      (challenges := getFoldingChallenges (r := r) (𝓡 := 𝓡) i challenges (k := j.val * ϑ)
        (h := h_k_next_le_i)))

omit [CharP L 2] in
lemma oracleFoldingConsistencyProp_relay_preserved (i : Fin ℓ)
    (hNCR : ¬ isCommitmentRound ℓ ϑ i) (challenges : Fin i.succ → L)
    (oStmt : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j) :
    oracleFoldingConsistencyProp 𝔽q β i.castSucc
      (olderStmtChallenges (ℓ := ℓ) (stmtIdx := i.succ) (oracleIdx := i.castSucc)
        (by simp only [Fin.val_succ, Fin.val_castSucc]; omega) challenges) oStmt ↔
    oracleFoldingConsistencyProp 𝔽q β i.succ challenges
      (mapOStmtOutRelayStep 𝔽q β i hNCR oStmt) := by
  have h_oracle_size_eq: toOutCodewordsCount ℓ ϑ i.castSucc =
      toOutCodewordsCount ℓ ϑ i.succ := by
    simp only [toOutCodewordsCount_succ_eq ℓ ϑ i, hNCR, ↓reduceIte]
  constructor
  · intro h j hj
    let j' : Fin (toOutCodewordsCount ℓ ϑ i.castSucc) := ⟨j.val, by
      rw [h_oracle_size_eq]
      exact j.isLt⟩
    have hj' : j'.val + 1 < toOutCodewordsCount ℓ ϑ i.castSucc := by
      change j.val + 1 < toOutCodewordsCount ℓ ϑ i.castSucc
      rw [h_oracle_size_eq]
      exact hj
    have h' := h j' hj'
    simp only [olderStmtChallenges_succ_castSucc] at h'
    have h_next_old :=
      oracle_block_k_next_le_i (ℓ := ℓ) (ϑ := ϑ) (i := i.castSucc) (j := j') (hj := hj')
    have h_next_new : ↑j' * ϑ + ϑ ≤ ↑i.succ := by
      exact Nat.le_trans h_next_old (by simp only [Fin.val_castSucc, Fin.val_succ]; omega)
    rw [getFoldingChallenges_tail_castSucc_eq (r := r) (𝓡 := 𝓡) (ϑ := ϑ)
      (i := i) (j := j') (challenges := challenges)
      (h_old := h_next_old) (h_new := h_next_new)] at h'
    simpa [oracleFoldingConsistencyProp, mapOStmtOutRelayStep, getNextOracle, j',
      h_oracle_size_eq, getFoldingChallenges_older_castSucc_eq,
      getFoldingChallenges_tail_castSucc_eq, getFoldingChallenges_proof_irrel] using h'
  · intro h j hj
    let j' : Fin (toOutCodewordsCount ℓ ϑ i.succ) := ⟨j.val, by
      rw [← h_oracle_size_eq]
      exact j.isLt⟩
    have hj' : j'.val + 1 < toOutCodewordsCount ℓ ϑ i.succ := by
      change j.val + 1 < toOutCodewordsCount ℓ ϑ i.succ
      rw [← h_oracle_size_eq]
      exact hj
    have h' := h j' hj'
    have h_next_old :=
      oracle_block_k_next_le_i (ℓ := ℓ) (ϑ := ϑ) (i := i.castSucc) (j := j) (hj := hj)
    have h_next_new : ↑j * ϑ + ϑ ≤ ↑i.succ := by
      exact Nat.le_trans h_next_old (by simp only [Fin.val_castSucc, Fin.val_succ]; omega)
    simp only [j'] at h'
    rw [← getFoldingChallenges_tail_castSucc_eq (r := r) (𝓡 := 𝓡) (ϑ := ϑ)
      (i := i) (j := j) (challenges := challenges)
      (h_old := h_next_old) (h_new := h_next_new)] at h'
    simpa [oracleFoldingConsistencyProp, mapOStmtOutRelayStep, getNextOracle, j',
      h_oracle_size_eq, olderStmtChallenges_succ_castSucc,
      getFoldingChallenges_older_castSucc_eq, getFoldingChallenges_tail_castSucc_eq,
      getFoldingChallenges_proof_irrel] using h'

def BBF_eq_multiplier (r : Fin ℓ → L) : MultilinearPoly L ℓ :=
  ⟨MvPolynomial.eqPolynomial r, by simp only [eqPolynomial_mem_restrictDegree]⟩

def BBF_SumcheckMultiplierParam : SumcheckMultiplierParam L ℓ (SumcheckBaseContext L ℓ) :=
  { multpoly := fun ctx => BBF_eq_multiplier ctx.t_eval_point
    -- Binary Basefold is the plain degree-2 case `H = P · t`: combinator `Q := X`, degree 1.
    combinator := fun _ => Polynomial.X
    degCombinator := 1
    combinator_natDegree_le := by intro _; exact Polynomial.natDegree_X_le }

/-- This condition ensures that the folding witness `f` is properly generated from `t`.

API migration: now uses the new-API `iterated_fold` (`steps : ℕ`, `{destIdx : Fin r}`,
`h_destIdx`/`h_destIdx_le`) — `steps := i.val`, `destIdx := ⟨i, _⟩` — instead of the legacy
`Fin (ℓ + 1)`-stepped `iterated_fold`. The result already lands at `OracleFunction ⟨i, _⟩`.

`Statement.challenges` follow the structured sumcheck convention: each new verifier challenge is
stored with `Fin.cons`, so index `0` is the newest challenge. The fold recursion consumes
challenges chronologically from level `0` upward, so this definition reverses the statement tuple
before passing it to `iterated_fold`. -/
def getMidCodewords {i : Fin (ℓ + 1)} (t : L⦃≤ 1⦄[X Fin ℓ]) -- original polynomial t
    (challenges : Fin i → L) : (sDomain 𝔽q β h_ℓ_add_R_rate (i := ⟨i, by omega⟩) → L) :=
  let P₀ : L⦃< 2^ℓ⦄[X] :=
    polynomialFromNovelCoeffsF₂ 𝔽q β ℓ (by omega)
      (fun ω => t.val.eval (statementOrderBitsOfIndex ω))
  let f₀ : (sDomain 𝔽q β h_ℓ_add_R_rate 0) → L := fun x => P₀.val.eval x.val
  iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := 0)
    (steps := i.val)
    (destIdx := ⟨i, by omega⟩)
    (h_destIdx := by simp only [Fin.val_zero, Nat.zero_add])
    (h_destIdx_le := by simp only [Fin.mk_le_mk]; omega)
    (f := f₀)
    (r_challenges := foldOrderChallenges (ℓ := ℓ) challenges)

/-! `SumcheckContextIncluded_Relations`: Sumcheck context is passed as a
parameters in the following relations --/
section SumcheckContextIncluded_Relations
variable {Context : Type} {mp : SumcheckMultiplierParam L ℓ Context} -- Sumcheck context

/-- This condition ensures that the witness polynomial `H` has the
correct structure `eq(...) * t(...)` -/
def witnessStructuralInvariant {i : Fin (ℓ + 1)} (stmt : Statement (L := L) Context i)
    (wit : Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) : Prop :=
  wit.H = projectToMidSumcheckPoly ℓ wit.t (m:=mp.multpoly stmt.ctx) i stmt.challenges ∧
  wit.f = getMidCodewords 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) wit.t stmt.challenges

/-- Sumcheck consistency: the claimed sumcheck target equals the sum of `H` over the boolean
hypercube of dimension `k` (embedded via `𝓑`). This is the protocol-level `(𝓑)` form consumed
throughout BinaryBasefold (Relations, ReductionLogic, Steps/*). -/
def sumcheckConsistencyProp {k : ℕ} (sumcheckTarget : L) (H : MultiquadraticPoly L k) : Prop :=
  sumcheckTarget = ∑ x ∈ (univ.map 𝓑) ^ᶠ k, H.val.eval x

/-- First oracle witness consistency: the witness polynomial t, when projected to level 0 and
    evaluated on the initial domain S^(0), must be close within unique decoding radius to f^(0) -/
def firstOracleWitnessConsistencyProp (t : MultilinearPoly L ℓ)
    (f₀ : sDomain 𝔽q β h_ℓ_add_R_rate 0 → L) : Prop :=
  let P₀ : L⦃< 2 ^ ℓ⦄[X] :=
    polynomialFromNovelCoeffsF₂ 𝔽q β ℓ (by omega)
      (fun ω => t.val.eval (statementOrderBitsOfIndex ω))
  -- The constraint: P_0 evaluated on S^(0) is close within unique decoding radius to f^(0)
  -- API migration: `BBF_CodeDistance` now lives in `Code.lean` keyed on `𝔽q β (h_ℓ_add_R_rate)`
  -- and a `Fin r` index (no explicit `ℓ 𝓡`).
  2 * hammingDist (fun x => P₀.val.eval x.val) f₀ <
    BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨0, by omega⟩

/-- The bad folding event of `fᵢ` exists RIGHT AFTER the V's challenge of sumcheck round `i+ϑ-1`,
this is the last point that `fᵢ` is the last oracle being sent so far and both
Statement & Witness are advanced to state `i+ϑ`, while oracle is still at state `i+ϑ-1`.
-/
noncomputable def foldingBadEventAtBlock
    (stmtIdx : Fin (ℓ + 1)) (oracleIdx : Fin (ℓ + 1))
    (oStmt : ∀ j, (OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (i := oracleIdx) j))
    (challenges : Fin stmtIdx → L)
    (j : Fin (toOutCodewordsCount ℓ ϑ oracleIdx)) : Prop :=
  have h_ϑ: ϑ > 0 := by exact pos_of_neZero ϑ
  if hj: j.val * ϑ + ϑ ≤ stmtIdx then
    let f_k := oStmt j
    Binius.BinaryBasefold.foldingBadEvent (i := ⟨j.val * ϑ, by omega⟩) (steps := ϑ)
      (destIdx := ⟨j.val * ϑ + ϑ, by omega⟩)
      (h_destIdx := by rfl) (h_destIdx_le := by simp only [Fin.mk_le_mk]; omega)
      (f_i := f_k) (r_challenges :=
        getFoldingChallenges (r := r) (𝓡 := 𝓡) stmtIdx challenges (k := j.val * ϑ) (h := hj))
  else True

attribute [irreducible] foldingBadEventAtBlock

open Classical in
def badEventExistsProp
    (stmtIdx : Fin (ℓ + 1)) (oracleIdx : Fin (ℓ + 1))
    (oStmt : ∀ j, (OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (i := oracleIdx) j))
    (challenges : Fin stmtIdx → L) : Prop :=
  ∃ j, foldingBadEventAtBlock 𝔽q β (stmtIdx := stmtIdx) (oracleIdx := oracleIdx)
    (oStmt := oStmt) (challenges := challenges) j

/-- When `stmtIdx.val < ℓ`, the highest available oracle block `j = stmtIdx/ϑ` has
`j*ϑ + ϑ > stmtIdx`, so its per-block bad-folding guard fails and `foldingBadEventAtBlock`
returns `True`. Hence `badEventExistsProp` (an existential over blocks) holds unconditionally:
the most-recently-sent oracle has not yet been folded past the current statement index, so the
"bad event" disjunct is vacuously available. This is the structural reason a relay/fold round in
the interior of the protocol is always non-doomed via the bad-event branch. -/
lemma badEventExistsProp_of_lt (stmtIdx : Fin (ℓ + 1)) (oracleIdx : Fin (ℓ + 1))
    (oStmt : ∀ j, (OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (i := oracleIdx) j))
    (challenges : Fin stmtIdx → L) (h_lt : stmtIdx.val < ℓ) (h_eq : oracleIdx.val = stmtIdx.val) :
    badEventExistsProp 𝔽q β (stmtIdx := stmtIdx) (oracleIdx := oracleIdx)
      (oStmt := oStmt) (challenges := challenges) := by
  have hϑ : 0 < ϑ := pos_of_neZero ϑ
  refine ⟨⟨stmtIdx.val / ϑ, ?_⟩, ?_⟩
  · -- `stmtIdx/ϑ < toOutCodewordsCount oracleIdx`
    unfold toOutCodewordsCount
    rw [h_eq]
    simp only [h_lt, ↓reduceIte]; omega
  · unfold foldingBadEventAtBlock
    split
    · -- guard holds: `stmtIdx/ϑ * ϑ + ϑ ≤ stmtIdx` is impossible since `stmtIdx/ϑ*ϑ > stmtIdx - ϑ`
      rename_i hj
      exfalso
      have hdm := Nat.div_add_mod stmtIdx.val ϑ
      have hm := Nat.mod_lt stmtIdx.val hϑ
      rw [Nat.mul_comm] at hdm
      simp only [Fin.val_mk] at hj
      omega
    · trivial

-- then simplify the top-level def to use the helper
def nonDoomedFoldingProp (i : Fin (ℓ + 1)) (challenges : Fin i → L)
    (oStmt : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i j)
    : Prop :=
  let oracleFoldingConsistency := oracleFoldingConsistencyProp 𝔽q β i (challenges := challenges)
    (oStmt := oStmt)
  let foldingBadEventExists := badEventExistsProp 𝔽q β i (challenges := challenges)
    (oStmt := oStmt)
  oracleFoldingConsistency ∨ foldingBadEventExists

omit [CharP L 2] [DecidableEq 𝔽q] h_β₀_eq_1 [NeZero 𝓡] in
lemma firstOracleWitnessConsistencyProp_relay_preserved (i : Fin ℓ)
    (hNCR : ¬ isCommitmentRound ℓ ϑ i) (wit : Witness (L := L) 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
    (oStmt : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j) :
    firstOracleWitnessConsistencyProp 𝔽q β wit.t (getFirstOracle 𝔽q β oStmt) =
    firstOracleWitnessConsistencyProp 𝔽q β wit.t
      (getFirstOracle 𝔽q β (mapOStmtOutRelayStep 𝔽q β i hNCR oStmt)) := by congr

-- STATEMENT REPAIR (2026-06-04): added hypothesis `h_not_last : i.val + 1 < ℓ`.
-- Reason: the original `↔` is FALSE at the last relay round (`i.val + 1 = ℓ`). There the LHS
-- (`nonDoomedFoldingProp` at `i.castSucc`, with `i.castSucc.val = i.val < ℓ`) is UNCONDITIONALLY
-- True via the bad-event disjunct (`badEventExistsProp_of_lt`: the top oracle block's folding guard
-- fails, yielding `True`), but the RHS at `i.succ = Fin.last ℓ` has count `ℓ/ϑ` with NO top "+1"
-- block, so every block's guard `j*ϑ+ϑ ≤ ℓ` HOLDS and `badEventExistsProp` becomes a genuine
-- existential over real `foldingBadEvent`s while `oracleFoldingConsistency` is a genuine oracle
-- constraint — neither is unconditionally True, so `True ↔ RHS` does not hold in general. With
-- `i.val + 1 < ℓ` both indices are `< ℓ`, both sides are unconditionally True via the bad-event
-- branch, and the lemma is sound. The lemma has zero live users (only the sibling
-- `oracleWitnessConsistency_relay_preserved`, which does not use the bad-event disjunction, is
-- consumed in `Steps.lean`), so tightening the hypothesis is safe.
lemma nonDoomedFoldingProp_relay_preserved (i : Fin ℓ) (hNCR : ¬ isCommitmentRound ℓ ϑ i)
    (h_not_last : i.val + 1 < ℓ)
    (challenges : Fin i.succ → L)
    (oStmt : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j)
    :
    nonDoomedFoldingProp 𝔽q β i.castSucc
      (olderStmtChallenges (ℓ := ℓ) (stmtIdx := i.succ) (oracleIdx := i.castSucc)
        (by simp only [Fin.val_succ, Fin.val_castSucc]; omega) challenges) oStmt ↔
    nonDoomedFoldingProp 𝔽q β i.succ challenges (mapOStmtOutRelayStep 𝔽q β i hNCR oStmt) := by
  -- Both sides reduce to `True` via their bad-event disjunct, since both statement indices are
  -- `< ℓ`.
  constructor
  · intro _
    refine Or.inr ?_
    exact badEventExistsProp_of_lt 𝔽q β (stmtIdx := i.succ) (oracleIdx := i.succ)
      (oStmt := mapOStmtOutRelayStep 𝔽q β i hNCR oStmt) (challenges := challenges)
      (h_lt := by simp only [Fin.val_succ]; omega) (h_eq := rfl)
  · intro _
    refine Or.inr ?_
    exact badEventExistsProp_of_lt 𝔽q β (stmtIdx := i.castSucc) (oracleIdx := i.castSucc)
      (oStmt := oStmt)
      (challenges := olderStmtChallenges (ℓ := ℓ) (stmtIdx := i.succ)
        (oracleIdx := i.castSucc)
        (by simp only [Fin.val_succ, Fin.val_castSucc]; omega) challenges)
      (h_lt := by simp only [Fin.coe_castSucc]; omega) (h_eq := rfl)

def oracleWitnessConsistency
    (stmtIdx : Fin (ℓ + 1)) (oracleIdx : Fin (ℓ + 1))
    (h_le : oracleIdx.val ≤ stmtIdx.val) (stmt : Statement (L := L) (Context := Context) stmtIdx)
    (wit : Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtIdx)
    (oStmt : ∀ j, (OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
  ϑ (i := oracleIdx) j)) : Prop :=
  let witnessStructuralInvariant: Prop := witnessStructuralInvariant (mp := mp) (i:=stmtIdx) 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmt wit
  let sumCheckConsistency: Prop := sumcheckConsistencyProp (𝓑 := 𝓑)
    stmt.sumcheck_target wit.H
  let firstOracleConsistency: Prop := firstOracleWitnessConsistencyProp 𝔽q β
    wit.t (getFirstOracle 𝔽q β oStmt)
  let oracleFoldingConsistency: Prop := oracleFoldingConsistencyProp 𝔽q β oracleIdx
    (challenges := olderStmtChallenges (ℓ := ℓ) (stmtIdx := stmtIdx) (oracleIdx := oracleIdx)
      h_le stmt.challenges)
    (oStmt := oStmt)
  witnessStructuralInvariant ∧ sumCheckConsistency ∧ firstOracleConsistency ∧
    oracleFoldingConsistency

omit [CharP L 2] in
lemma oracleWitnessConsistency_relay_preserved
    (i : Fin ℓ) (hNCR : ¬ isCommitmentRound ℓ ϑ i)
    (stmt : Statement (L := L) Context i.succ)
    (wit : Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
    (oStmt : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j) :
    oracleWitnessConsistency (mp := mp) (𝓑 := 𝓑) 𝔽q β i.succ i.castSucc
      (le_succ ↑i.castSucc) stmt wit oStmt =
    oracleWitnessConsistency (mp := mp) (𝓑 := 𝓑) 𝔽q β i.succ i.succ (by rfl) stmt wit
      (mapOStmtOutRelayStep 𝔽q β i hNCR oStmt) := by
  unfold oracleWitnessConsistency
  simp only
  -- conjuncts 1,2 (witnessStructuralInvariant, sumCheckConsistency) are identical;
  -- conjunct 3 (firstOracleConsistency) equal by the relay-preservation of the first oracle;
  -- conjunct 4 (oracleFoldingConsistency) equal by oracle/challenge reindexing.
  congr 1
  · -- sumcheckConsistency (identical) ∧ firstOracleConsistency ∧ oracleFoldingConsistency
    rw [firstOracleWitnessConsistencyProp_relay_preserved 𝔽q β i hNCR wit oStmt]
    -- now the two `firstOracle…` conjuncts are syntactically identical; isolate the folding props.
    congr 1  -- peel sumcheckConsistency (rfl)
    congr 1  -- peel firstOracleConsistency (now rfl)
    simpa [olderStmtChallenges_self] using
      propext (oracleFoldingConsistencyProp_relay_preserved 𝔽q β i hNCR
        stmt.challenges oStmt)

-- Per-block relay preservation: `foldingBadEventAtBlock` depends on the oracle index only through
-- `oStmt j` (its `f_i` input). The RHS block index is `Fin.cast h_size j`, so `j.val` is preserved
-- (`Fin.cast` is the identity on values) and `mapOStmtOutRelayStep … oStmt (Fin.cast h_size j)`
-- definitionally reduces to `oStmt j`. Hence the block predicate is literally the same on both
-- sides — no rewriting of the dependent `f_i` is needed. We unseal the irreducible block def. -/
unseal foldingBadEventAtBlock in
lemma foldingBadEventAtBlock_relay_preserved
    (i : Fin ℓ) (hNCR : ¬ isCommitmentRound ℓ ϑ i)
    (h_size : toOutCodewordsCount ℓ ϑ i.castSucc = toOutCodewordsCount ℓ ϑ i.succ)
    (challenges : Fin i.succ → L)
    (oStmt : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j)
    (j : Fin (toOutCodewordsCount ℓ ϑ i.castSucc)) :
    foldingBadEventAtBlock 𝔽q β (stmtIdx := i.succ) (oracleIdx := i.castSucc)
        (oStmt := oStmt) (challenges := challenges) j =
    foldingBadEventAtBlock 𝔽q β (stmtIdx := i.succ) (oracleIdx := i.succ)
        (oStmt := mapOStmtOutRelayStep 𝔽q β i hNCR oStmt) (challenges := challenges)
        (Fin.cast h_size j) :=
  rfl

/-- The relay step's oracle relabeling preserves the bad-event existential, when both sides are
evaluated against the *same* statement index `i.succ`. Both sides quantify the same per-block
folding guard `j*ϑ + ϑ ≤ i.succ` over equal block counts (`hNCR ⇒ count i.castSucc = count i.succ`)
on the identical oracle data (`mapOStmtOutRelayStep` is a pure reindex along that size equality),
so the existentials coincide. This is the bad-event analogue of
`oracleWitnessConsistency_relay_preserved`, and is what makes `foldStepRelOut` (with its repaired
`stmtIdx := i.succ` bad event) equal to its relay image `roundRelation i.succ` at *every* round,
including the last (`i.val + 1 = ℓ`). -/
lemma badEventExistsProp_relay_preserved
    (i : Fin ℓ) (hNCR : ¬ isCommitmentRound ℓ ϑ i)
    (challenges : Fin i.succ → L)
    (oStmt : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j) :
    badEventExistsProp (ϑ := ϑ) 𝔽q β (stmtIdx := i.succ) (oracleIdx := i.castSucc)
        (challenges := challenges) (oStmt := oStmt) =
    badEventExistsProp (ϑ := ϑ) 𝔽q β (stmtIdx := i.succ) (oracleIdx := i.succ)
        (challenges := challenges) (oStmt := mapOStmtOutRelayStep 𝔽q β i hNCR oStmt) := by
  have h_size : toOutCodewordsCount ℓ ϑ i.castSucc = toOutCodewordsCount ℓ ϑ i.succ := by
    simp only [toOutCodewordsCount_succ_eq ℓ ϑ i, hNCR, ↓reduceIte]
  apply propext
  unfold badEventExistsProp
  -- reindex the existential block along the size equality `h_size`; the predicate is literally
  -- preserved by `foldingBadEventAtBlock_relay_preserved`.
  constructor
  · rintro ⟨j, hj⟩
    exact ⟨Fin.cast h_size j,
      (foldingBadEventAtBlock_relay_preserved 𝔽q β i hNCR h_size challenges oStmt j) ▸ hj⟩
  · rintro ⟨j', hj⟩
    refine ⟨Fin.cast h_size.symm j', ?_⟩
    rw [foldingBadEventAtBlock_relay_preserved 𝔽q β i hNCR h_size challenges oStmt
      (Fin.cast h_size.symm j')]
    simpa using hj

/-- Before V's challenge of the `i-th` foldStep, we ignore the bad-folding-event
of the `i-th` oracle if any and enable it after the next V's challenge, i.e. one
round later. This is for the purpose of reasoning its RBR KS properly.
Formally, = (oracleIdx = stmtIdx)`.
-/
def masterKStateProp (stmtIdx : Fin (ℓ + 1))
    (oracleIdx : Fin (ℓ + 1))
    (h_le : oracleIdx.val ≤ stmtIdx.val) (stmt : Statement (L := L) Context stmtIdx)
    (wit : Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtIdx)
    (oStmt : ∀ j, (OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (i := oracleIdx) j))
    (localChecks : Prop := True) : Prop :=
  let oracleWitnessConsistency: Prop := oracleWitnessConsistency (mp := mp) (𝓑 := 𝓑) 𝔽q β
    stmtIdx oracleIdx h_le stmt wit oStmt
  let badEventExists := badEventExistsProp (ϑ := ϑ) 𝔽q β oracleIdx
    (challenges := olderStmtChallenges (ℓ := ℓ) (stmtIdx := stmtIdx) (oracleIdx := oracleIdx)
      h_le stmt.challenges)
    (oStmt := oStmt)
  localChecks ∧ (badEventExists ∨ oracleWitnessConsistency)

def roundRelationProp (i : Fin (ℓ + 1))
    (input : (Statement (L := L) Context i ×
      (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i j)) ×
      Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) : Prop :=
  let stmt := input.1.1
  let oStmt := input.1.2
  let wit := input.2
  masterKStateProp (mp := mp) (𝓑 := 𝓑) 𝔽q β
    (stmtIdx := i) (oracleIdx := i) (h_le := le_refl i) stmt wit oStmt (localChecks := True)

open Classical in
/-- A modified version of roundRelationProp (i+1).

STATEMENT REPAIR (2026-06-04): at *non-commitment* rounds the bad-event disjunct is evaluated at
the statement index `i.succ` (the relay-step / `roundRelation i.succ` form) rather than at the
oracle index `i.castSucc`.

Why a per-round branch. `foldStepRelOut i` is the relOut of the fold step and the relIn of whichever
single step consumes round `i` — the *commit* step when `isCommitmentRound ℓ ϑ i`, the *relay* step
otherwise (the two are mutually exclusive). These two consumers need *different* forms:

* Commit rounds (`ϑ ∣ i+1 ∧ i+1 ≠ ℓ`): `commitKState.toFun_empty` is `rfl` against
  `commitKStateProp 0 = masterKStateProp (stmtIdx := i.succ) (oracleIdx := i.castSucc)`, i.e. the
  bad event at `stmtIdx := oracleIdx := i.castSucc` (the "ignore the latest oracle's bad event one
  step behind" design). The commit step *changes* the oracle count, so the relay relabel does not
  apply; this weak form is the intended one.

* Non-commitment rounds (`¬ isCommitmentRound`, includes the last round `i+1 = ℓ`): the relay step
  is a 0-round protocol, so `relayKnowledgeStateFunction.toFun_empty` demands
  `relIn ↔ toFun 0 = relayKStateProp = roundRelation i.succ` (its relOut). With the weak form this
  `↔` is FALSE at the last round (`i+1 = ℓ`): the relIn bad event at `stmtIdx := i.castSucc`
  (guard `j*ϑ+ϑ ≤ i`) is vacuously `True` via the top block, but `roundRelation i.succ` evaluates
  the bad event at `stmtIdx := oracleIdx := i.succ` (guard `j*ϑ+ϑ ≤ ℓ`, satisfied by that top block)
  — a *genuine* existential. So `True ↔ (genuine bad event ∨ owc)` fails. Evaluating the relIn bad
  event at the *statement* index `i.succ` instead makes it coincide with the relay image of
  `roundRelation i.succ` at *every* non-commitment round, including the boundary — the oracle data
  agrees up to the relay relabel (`hNCR ⇒ count i.castSucc = count i.succ`); see
  `badEventExistsProp_relay_preserved` / `foldStepRelOut_relay_eq_roundRelation`.

The owc disjunct is unchanged (`oracleWitnessConsistency (stmtIdx := i.succ) (oracleIdx :=
i.castSucc)`), matching both consumers via `oracleWitnessConsistency_relay_preserved`. Only
`foldStepRelOut` (confined to `Basic.lean` + `Steps.lean`) is affected; the fold-step theorems that
mention it are by-name and their proofs are research-tier `sorry` stubs, so no proven content
regresses, and the commit path keeps its weak form. -/
def foldStepRelOutProp (i : Fin ℓ)
    (input : (Statement (L := L) Context i.succ ×
      (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j)) ×
      Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ) : Prop :=
  let stmt := input.1.1
  let oStmt := input.1.2
  let wit := input.2
  let oracleWitnessConsistency : Prop :=
    oracleWitnessConsistency (mp := mp) (𝓑 := 𝓑) 𝔽q β
      (stmtIdx := i.succ) (oracleIdx := i.castSucc)
      (h_le := Nat.le_of_lt (Fin.castSucc_lt_succ)) stmt wit oStmt
  let badEventExists : Prop :=
    if isCommitmentRound ℓ ϑ i then
      -- commit-round (weak) form: bad event at `stmtIdx := oracleIdx := i.castSucc`
      badEventExistsProp (ϑ := ϑ) 𝔽q β (stmtIdx := i.castSucc) (oracleIdx := i.castSucc)
        (challenges := olderStmtChallenges (ℓ := ℓ) (stmtIdx := i.succ)
          (oracleIdx := i.castSucc)
          (by simp only [Fin.coe_castSucc, Fin.val_succ]; omega) stmt.challenges)
        (oStmt := oStmt)
    else
      -- non-commitment (relay) form: bad event at the statement index `i.succ`
      badEventExistsProp (ϑ := ϑ) 𝔽q β (stmtIdx := i.succ) (oracleIdx := i.castSucc)
        (challenges := stmt.challenges) (oStmt := oStmt)
  badEventExists ∨ oracleWitnessConsistency

/-- This is a special case of nonDoomedFoldingProp for `i = ℓ`, where we support
the consistency between the last oracle `ℓ - ϑ` and the final constant `c` -/
def finalNonDoomedFoldingProp {h_le : ϑ ≤ ℓ}
    (input : (FinalSumcheckStatementOut (L := L) (ℓ := ℓ) ×
      (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j))) :
    Prop :=
  let stmt := input.1
  let oStmt := input.2
  let f_ℓ: (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨ℓ, by omega⟩ → L := fun x => stmt.final_constant
  let j := mkLastOracleIndex ℓ ϑ (Fin.last ℓ) -- actually `j = ℓ / ϑ - 1`
  let k := j.val * ϑ
  have h_k: k = ℓ - ϑ := by
    dsimp only [mkLastOracleIndex, Fin.val_last, lt_self_iff_false, Lean.Elab.WF.paramLet,
      eq_mpr_eq_cast, cast_eq, k, j]
    simp only [lt_self_iff_false, ↓reduceDIte]
    change (ℓ / ϑ - 1) * ϑ = ℓ - ϑ
    rw [Nat.sub_mul, Nat.one_mul]
    rw [Nat.div_mul_cancel (hdiv.out)]
  let f_k := oStmt j
  let challenges : Fin ϑ → L := fun cId => stmt.challenges ⟨k + cId, by
    simp only [Fin.val_last, k]
    rw [mkLastOracleIndex_last, Nat.sub_mul, Nat.one_mul, Nat.div_mul_cancel (hdiv.out)]
    rw [Nat.sub_add_eq_sub_sub_rev (h1:=by omega) (h2:=by omega)]; omega
  ⟩
  have h_k_add_ϑ: k + ϑ = ℓ := by rw [h_k]; apply Nat.sub_add_cancel; omega
  let finalOracleFoldingConsistency: Prop := by
    -- folding consistency between two adjacent oracles `j` & `j + ϑ`
    exact isCompliant (i := ⟨k, by rw [h_k]; omega⟩) (steps := ϑ)
      (destIdx := ⟨ℓ, by omega⟩)
      (h_destIdx := by simp only [Fin.val_mk]; omega)
      (h_destIdx_le := by simp only [Fin.mk_le_mk]; omega) (f_i := f_k)
      (f_i_plus_steps := by simpa only [h_k_add_ϑ] using f_ℓ) (challenges := challenges)

  -- If oracleFoldingConsistency is true, then we can extract the original
    -- well-formed poly `t` and derive witnesses that satisfy the relations at any state
  let oracleFoldingConsistency: Prop :=
    (oracleFoldingConsistencyProp 𝔽q β (i := Fin.last ℓ)
      (challenges := stmt.challenges) (oStmt := oStmt))
    ∧ finalOracleFoldingConsistency

  let finalFoldingBadEvent : Prop :=
    Binius.BinaryBasefold.foldingBadEvent (i := ⟨k, by rw [h_k]; omega⟩)
      (steps := ϑ) (destIdx := ⟨ℓ, by omega⟩)
      (h_destIdx := by simp only [Fin.val_mk]; omega)
      (h_destIdx_le := by simp only [Fin.mk_le_mk]; omega) (f_i := f_k)
      (r_challenges := challenges)

  -- All bad folding events are fully formed across the sum-check rounds,
    -- no new bad event at the final sumcheck step
  let foldingBadEventExists : Prop := badEventExistsProp 𝔽q β (stmtIdx := Fin.last ℓ)
    (oStmt := oStmt) (challenges := stmt.challenges)

  oracleFoldingConsistency ∨ foldingBadEventExists

/-- Input relation for round i: R_i must hold at the beginning of round i -/
def foldStepRelOut (i : Fin ℓ) :
    Set ((Statement (L := L) Context i.succ ×
      (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j)) ×
      Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ) :=
  { input | foldStepRelOutProp (L := L) (𝔽q := 𝔽q) (β := β) (𝓑 := 𝓑)
      (Context := Context) (mp := mp) i input}

/-- Relation at step `i` of the CoreInteraction. `∀ i < ℓ, R_i` must hold at the
beginning of ITERATION `i`. `R_ℓ` must hold after the last iteration and before sending
the final constant. -/
def roundRelation (i : Fin (ℓ + 1)) :
    Set ((Statement (L := L) Context i ×
      (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i j)) ×
      Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) :=
  { input | roundRelationProp (mp := mp) (𝓑 := 𝓑) 𝔽q β i input}

/-- Relation for final sumcheck step -/
def finalSumcheckRelOutProp
    (input : ((FinalSumcheckStatementOut (L := L) (ℓ := ℓ) ×
      (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j)) ×
      (Unit))) : Prop :=
  -- Final oracle consistency and bad events
  finalNonDoomedFoldingProp 𝔽q β
    (h_le := by apply Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ) (hdiv.out))
    (input := input.1)

/-- Final sumcheck relation -/
def finalSumcheckRelOut :
    Set ((FinalSumcheckStatementOut (L := L) (ℓ := ℓ) ×
      (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j)) ×
      (Unit)) :=
  { input | finalSumcheckRelOutProp 𝔽q β (input := input) }
end SumcheckContextIncluded_Relations
end SecurityRelations
end OracleReductionComponents

end Binius.BinaryBasefold
