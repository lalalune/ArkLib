/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.Incremental

/-!
# Issue #317: the preTensorCombine multilinearity residuals, PROVEN

Discharges two of the named Binius residuals:

* **`PreTensorCombineMultilinearResidual`** — `iterated_fold f r_chal` equals the multilinear
  combination (weights `multilinearWeight r_chal`) of the rows of its preTensorCombine stack.
  Proof: induction on `steps`.  The inductive step peels the **last** fold (`iterated_fold_last`),
  pushes the fold through the tensor sum (`fold` is *linear* in its function argument and
  *affine* in its challenge — both immediate from the `fold_legacy` butterfly formula), and
  reassembles with the MSB-split tensor recursion `multilinearCombine_recursive_form`; the
  even/odd row identification is pure `Nat.getBit` arithmetic on `bitsOfIndex`.

* **`FoldPreTensorCombineAffineSplitResidual`** — one fold step on a preTensorCombine stack is
  the affine line evaluation of the even/odd row split.  Proof: peel the **first** fold
  (`iterated_fold_first`) at the challenge vector `Fin.cons r_new (bitsOfIndex k)`, expand by
  the (now-proven) multilinear identity, factor the first challenge with the LSB-split tensor
  recursion `multilinearCombine_recursive_form_first`, and collapse the binary tail with the
  indicator property `multilinearWeight_bitsOfIndex_eq_indicator`.

No `sorry`; axiom audit at the bottom.
-/

namespace Binius.BinaryBasefold

open Finset

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))] [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ 𝓡 : ℕ} [NeZero ℓ] [NeZero 𝓡]
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r}

noncomputable section

/-! ### Binary-index bit facts: the MSB split of `bitsOfIndex` -/

section Bits

variable {n : ℕ}

/-- The `n`-th bit of an index below `2 ^ n` is `0`. -/
lemma getBit_top_of_lt (k : Fin (2 ^ n)) : Nat.getBit n k.val = 0 := by
  have h := Nat.getBit_of_lt_two_pow (a := k) (k := n)
  simpa using h

/-- Adding the top power `2 ^ n` does not disturb the low bits. -/
lemma getBit_add_two_pow_low (k : Fin (2 ^ n)) {j : ℕ} (hj : j < n) :
    Nat.getBit j (k.val + 2 ^ n) = Nat.getBit j k.val := by
  have hand : k.val &&& 2 ^ n = 0 :=
    Nat.and_two_pow_eq_zero_of_getBit_0 (getBit_top_of_lt k)
  rw [Nat.sum_of_and_eq_zero_is_xor hand, Nat.getBit_of_xor]
  rw [show Nat.getBit j (2 ^ n) = 0 from by
    simp only [Nat.getBit_two_pow, beq_iff_eq]
    rw [if_neg (by omega)]]
  exact Nat.xor_zero _

/-- Adding the top power `2 ^ n` sets the `n`-th bit. -/
lemma getBit_add_two_pow_top (k : Fin (2 ^ n)) :
    Nat.getBit n (k.val + 2 ^ n) = 1 := by
  have hand : k.val &&& 2 ^ n = 0 :=
    Nat.and_two_pow_eq_zero_of_getBit_0 (getBit_top_of_lt k)
  rw [Nat.sum_of_and_eq_zero_is_xor hand, Nat.getBit_of_xor, getBit_top_of_lt k]
  rw [show Nat.getBit n (2 ^ n) = 1 from by
    simp [Nat.getBit_two_pow]]

/-- The first `n` challenge bits of a low row index `k < 2 ^ n` (inside `Fin (2 ^ (n + 1))`)
are the challenge bits of `k`. -/
lemma bitsOfIndex_low_init (k : Fin (2 ^ n)) (h : k.val < 2 ^ (n + 1)) :
    Fin.init (bitsOfIndex (L := L) (⟨k.val, h⟩ : Fin (2 ^ (n + 1))))
      = bitsOfIndex (L := L) k := rfl

/-- The last challenge bit of a low row index `k < 2 ^ n` is `0`. -/
lemma bitsOfIndex_low_last (k : Fin (2 ^ n)) (h : k.val < 2 ^ (n + 1)) :
    bitsOfIndex (L := L) (⟨k.val, h⟩ : Fin (2 ^ (n + 1))) (Fin.last n) = 0 := by
  apply bitsOfIndex_apply_of_getBit_ne_one
  show Nat.getBit n k.val ≠ 1
  rw [getBit_top_of_lt k]
  omega

/-- The first `n` challenge bits of a high row index `k + 2 ^ n` are the challenge bits of
`k`. -/
lemma bitsOfIndex_high_init (k : Fin (2 ^ n)) (h : k.val + 2 ^ n < 2 ^ (n + 1)) :
    Fin.init (bitsOfIndex (L := L) (⟨k.val + 2 ^ n, h⟩ : Fin (2 ^ (n + 1))))
      = bitsOfIndex (L := L) k := by
  funext j
  show (if Nat.getBit j.val (k.val + 2 ^ n) = 1 then (1 : L) else 0) = _
  rw [getBit_add_two_pow_low k j.isLt]
  rfl

/-- The last challenge bit of a high row index `k + 2 ^ n` is `1`. -/
lemma bitsOfIndex_high_last (k : Fin (2 ^ n)) (h : k.val + 2 ^ n < 2 ^ (n + 1)) :
    bitsOfIndex (L := L) (⟨k.val + 2 ^ n, h⟩ : Fin (2 ^ (n + 1))) (Fin.last n) = 1 := by
  apply bitsOfIndex_apply_of_getBit_eq_one
  show Nat.getBit n (k.val + 2 ^ n) = 1
  exact getBit_add_two_pow_top k

end Bits

/-! ### The fold butterfly is linear in `f` and affine in the challenge -/

section FoldAlgebra

set_option maxHeartbeats 1000000 in
seal sDomain qMap_total_fiber normalizedW intermediateEvaluationPoly in
/-- `fold_legacy` is affine in its challenge: `fold(f, c) = (1-c)·fold(f, 0) + c·fold(f, 1)`.
Immediate from the butterfly formula. -/
lemma fold_legacy_affine (i : Fin r) (h_i : i.val + 1 < ℓ + 𝓡)
    (f : sDomain 𝔽q β h_ℓ_add_R_rate i → L) (c : L)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate ⟨i.val + 1, by omega⟩) :
    fold_legacy 𝔽q β i h_i f c y
      = (1 - c) * fold_legacy 𝔽q β i h_i f 0 y + c * fold_legacy 𝔽q β i h_i f 1 y := by
  unfold fold_legacy
  dsimp only
  ring

set_option maxHeartbeats 1000000 in
seal sDomain qMap_total_fiber normalizedW intermediateEvaluationPoly in
/-- `fold_legacy` is linear in its function argument over a weighted finite sum. -/
lemma fold_legacy_sum {m : ℕ} (i : Fin r) (h_i : i.val + 1 < ℓ + 𝓡)
    (V : Fin m → sDomain 𝔽q β h_ℓ_add_R_rate i → L) (w : Fin m → L) (c : L)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate ⟨i.val + 1, by omega⟩) :
    fold_legacy 𝔽q β i h_i (fun x => ∑ k : Fin m, w k • V k x) c y
      = ∑ k : Fin m, w k • fold_legacy 𝔽q β i h_i (V k) c y := by
  unfold fold_legacy
  dsimp only
  simp only [smul_eq_mul, Finset.sum_mul]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

set_option maxHeartbeats 1000000 in
/-- New-API `fold` is affine in its challenge. -/
lemma fold_affine (i : Fin r) {destIdx : Fin r} (h_destIdx : destIdx.val = i.val + 1)
    (h_destIdx_le : destIdx ≤ ℓ)
    (f : sDomain 𝔽q β h_ℓ_add_R_rate i → L) (c : L)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate destIdx) :
    fold 𝔽q β (i := i) (destIdx := destIdx) h_destIdx h_destIdx_le f c y
      = (1 - c) * fold 𝔽q β (i := i) (destIdx := destIdx) h_destIdx h_destIdx_le f 0 y
        + c * fold 𝔽q β (i := i) (destIdx := destIdx) h_destIdx h_destIdx_le f 1 y := by
  have hb : i.val + 1 < r := by rw [← h_destIdx]; exact destIdx.isLt
  have h_eq : destIdx = ⟨i.val + 1, hb⟩ := Fin.ext h_destIdx
  subst h_eq
  unfold fold
  simp only [cast_eq]
  exact fold_legacy_affine 𝔽q β i _ f c y

set_option maxHeartbeats 1000000 in
/-- New-API `fold` of a multilinear combination is the multilinear combination of the
folded rows. -/
lemma fold_multilinearCombine {m : ℕ} (i : Fin r) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + 1) (h_destIdx_le : destIdx ≤ ℓ)
    (V : Fin (2 ^ m) → sDomain 𝔽q β h_ℓ_add_R_rate i → L) (ri : Fin m → L) (c : L)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate destIdx) :
    fold 𝔽q β (i := i) (destIdx := destIdx) h_destIdx h_destIdx_le
        (multilinearCombine (F := L) V ri) c y
      = ∑ k : Fin (2 ^ m), multilinearWeight ri k •
          fold 𝔽q β (i := i) (destIdx := destIdx) h_destIdx h_destIdx_le (V k) c y := by
  have hb : i.val + 1 < r := by rw [← h_destIdx]; exact destIdx.isLt
  have h_eq : destIdx = ⟨i.val + 1, hb⟩ := Fin.ext h_destIdx
  subst h_eq
  unfold fold multilinearCombine
  simp only [cast_eq]
  exact fold_legacy_sum 𝔽q β i _ V (multilinearWeight ri) c y

end FoldAlgebra

/-! ### The even/odd rows of the `(n+1)`-stack are folds of the `n`-stack rows -/

section StackRows

set_option maxHeartbeats 4000000 in
/-- **Low rows**: row `k < 2 ^ n` of the `(n+1)`-step preTensorCombine stack is the `0`-fold of
row `k` of the `n`-step stack. -/
lemma preTensorCombine_succ_row_low (i : Fin ℓ) (n : ℕ) {midIdx destIdx : Fin r}
    (h_midIdx : midIdx.val = i.val + n)
    (h_destIdx : destIdx.val = i.val + (n + 1)) (h_destIdx_le : destIdx ≤ ℓ)
    (h_midIdx_le : midIdx ≤ ℓ)
    (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ⟨i.val, lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (le_of_lt i.isLt)⟩)
    (k : Fin (2 ^ n)) (hk : k.val < 2 ^ (n + 1)) :
    preTensorCombine_WordStack 𝔽q β i (n + 1) h_destIdx h_destIdx_le f ⟨k.val, hk⟩
      = fold 𝔽q β (i := midIdx) (destIdx := destIdx)
          (h_destIdx := by omega) (h_destIdx_le := h_destIdx_le)
          (preTensorCombine_WordStack 𝔽q β i n (destIdx := midIdx)
            (h_destIdx := by omega) (h_destIdx_le := h_midIdx_le) f k) 0 := by
  simp only [preTensorCombine_WordStack]
  rw [iterated_fold_last 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := ⟨i.val, lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (le_of_lt i.isLt)⟩)
    (steps := n) (midIdx := midIdx) (destIdx := destIdx)
    (h_midIdx := by omega) (h_destIdx := by omega) (h_destIdx_le := h_destIdx_le)
    f (bitsOfIndex (L := L) ⟨k.val, hk⟩)]
  rw [bitsOfIndex_low_init (L := L) k hk, bitsOfIndex_low_last (L := L) k hk]

set_option maxHeartbeats 4000000 in
/-- **High rows**: row `k + 2 ^ n` of the `(n+1)`-step preTensorCombine stack is the `1`-fold of
row `k` of the `n`-step stack. -/
lemma preTensorCombine_succ_row_high (i : Fin ℓ) (n : ℕ) {midIdx destIdx : Fin r}
    (h_midIdx : midIdx.val = i.val + n)
    (h_destIdx : destIdx.val = i.val + (n + 1)) (h_destIdx_le : destIdx ≤ ℓ)
    (h_midIdx_le : midIdx ≤ ℓ)
    (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ⟨i.val, lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (le_of_lt i.isLt)⟩)
    (k : Fin (2 ^ n)) (hk : k.val + 2 ^ n < 2 ^ (n + 1)) :
    preTensorCombine_WordStack 𝔽q β i (n + 1) h_destIdx h_destIdx_le f ⟨k.val + 2 ^ n, hk⟩
      = fold 𝔽q β (i := midIdx) (destIdx := destIdx)
          (h_destIdx := by omega) (h_destIdx_le := h_destIdx_le)
          (preTensorCombine_WordStack 𝔽q β i n (destIdx := midIdx)
            (h_destIdx := by omega) (h_destIdx_le := h_midIdx_le) f k) 1 := by
  simp only [preTensorCombine_WordStack]
  rw [iterated_fold_last 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := ⟨i.val, lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (le_of_lt i.isLt)⟩)
    (steps := n) (midIdx := midIdx) (destIdx := destIdx)
    (h_midIdx := by omega) (h_destIdx := by omega) (h_destIdx_le := h_destIdx_le)
    f (bitsOfIndex (L := L) ⟨k.val + 2 ^ n, hk⟩)]
  rw [bitsOfIndex_high_init (L := L) k hk, bitsOfIndex_high_last (L := L) k hk]

end StackRows

/-! ### The main multilinearity theorem (PreTensorCombineMultilinearResidual) -/

section MainTheorem

set_option maxHeartbeats 4000000 in
/-- **`iterated_fold` is the multilinear combination of its preTensorCombine stack** —
the content of `PreTensorCombineMultilinearResidual`, proven. -/
theorem iterated_fold_eq_multilinearCombine_preTensorCombine_proven
    (i : Fin ℓ) (steps : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f_i : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ⟨i.val, lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (le_of_lt i.isLt)⟩)
    (r_chal : Fin steps → L) :
    iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := ⟨i.val, lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (le_of_lt i.isLt)⟩)
      steps (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := f_i)
      (r_challenges := r_chal) =
    multilinearCombine (F := L)
      (preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le f_i) r_chal := by
  induction steps generalizing destIdx with
  | zero =>
    funext y
    rw [iterated_fold_zero_steps 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (h_destIdx := by omega) (h_destIdx_le := h_destIdx_le)]
    simp only [multilinearCombine]
    rw [Finset.sum_eq_single (⟨0, by norm_num⟩ : Fin (2 ^ 0))]
    · rw [show multilinearWeight r_chal (⟨0, by norm_num⟩ : Fin (2 ^ 0)) = 1 from
        Fin.prod_univ_zero _]
      rw [one_smul]
      simp only [preTensorCombine_WordStack]
      rw [iterated_fold_zero_steps 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (h_destIdx := by omega) (h_destIdx_le := h_destIdx_le)]
    · intro b _ hb
      refine absurd (Fin.ext ?_) hb
      have h1 : (2 : ℕ) ^ 0 = 1 := pow_zero 2
      have := b.isLt
      omega
    · intro h
      exact absurd (Finset.mem_univ _) h
  | succ n ih =>
    have h_mid_bound : i.val + n < r := by have := destIdx.isLt; omega
    have h_mid_le : (⟨i.val + n, h_mid_bound⟩ : Fin r) ≤ ℓ := by
      show i.val + n ≤ ℓ
      have h1 : destIdx.val ≤ ℓ := h_destIdx_le
      omega
    -- Peel the last fold step.
    rw [iterated_fold_last 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := ⟨i.val, lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (le_of_lt i.isLt)⟩)
      (steps := n) (midIdx := ⟨i.val + n, h_mid_bound⟩) (destIdx := destIdx)
      (h_midIdx := rfl) (h_destIdx := by omega) (h_destIdx_le := h_destIdx_le)
      f_i r_chal]
    -- Inductive hypothesis on the inner fold.
    rw [ih (destIdx := ⟨i.val + n, h_mid_bound⟩) rfl h_mid_le (Fin.init r_chal)]
    -- MSB-split recursion on the RHS tensor combination.
    have hrec := multilinearCombine_recursive_form
      (u := preTensorCombine_WordStack 𝔽q β i (n + 1) h_destIdx h_destIdx_le f_i)
      (r := r_chal)
    dsimp only at hrec
    rw [hrec]
    -- Pointwise: push the fold through the tensor sum and match rows.
    funext y
    rw [fold_multilinearCombine 𝔽q β (i := ⟨i.val + n, h_mid_bound⟩) (destIdx := destIdx)
      (h_destIdx := by omega) (h_destIdx_le := h_destIdx_le)]
    simp only [multilinearCombine]
    apply Finset.sum_congr rfl
    intro k _
    congr 1
    -- fold (stack_n k) c y = (affineLineEvaluation U₀ U₁ c) k y
    rw [fold_affine 𝔽q β (i := ⟨i.val + n, h_mid_bound⟩) (destIdx := destIdx)
      (h_destIdx := by omega) (h_destIdx_le := h_destIdx_le)]
    simp only [affineLineEvaluation, splitHalfRowWiseInterleavedWords,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [preTensorCombine_succ_row_low 𝔽q β i n (midIdx := ⟨i.val + n, h_mid_bound⟩)
      (h_midIdx := rfl) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
      (h_midIdx_le := h_mid_le) f_i k (by omega)]
    rw [preTensorCombine_succ_row_high 𝔽q β i n (midIdx := ⟨i.val + n, h_mid_bound⟩)
      (h_midIdx := rfl) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
      (h_midIdx_le := h_mid_le) f_i k (by omega)]

/-- **Issue #317: `PreTensorCombineMultilinearResidual` DISCHARGED.** -/
instance instPreTensorCombineMultilinearResidualProven :
    PreTensorCombineMultilinearResidual 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) where
  holds i steps h_destIdx h_destIdx_le f_i r_chal :=
    iterated_fold_eq_multilinearCombine_preTensorCombine_proven 𝔽q β
      i steps h_destIdx h_destIdx_le f_i r_chal

end MainTheorem

/-! ### The affine even/odd split (FoldPreTensorCombineAffineSplitResidual) -/

section AffineSplit

/-- Tensor combination at a binary challenge vector reads off the indexed row. -/
lemma multilinearCombine_bitsOfIndex {m : ℕ} {ι : Type*}
    (W : Fin (2 ^ m) → ι → L) (k : Fin (2 ^ m)) :
    multilinearCombine (F := L) W (bitsOfIndex (L := L) k) = W k := by
  funext y
  simp only [multilinearCombine]
  rw [Finset.sum_eq_single k]
  · rw [multilinearWeight_bitsOfIndex_eq_indicator (L := L) k k, if_pos rfl, one_smul]
  · intro b _ hb
    rw [multilinearWeight_bitsOfIndex_eq_indicator (L := L) b k, if_neg hb, zero_smul]
  · intro h
    exact absurd (Finset.mem_univ _) h

set_option maxHeartbeats 4000000 in
/-- **One fold step on preTensorCombine = affine line evaluation on the even/odd split** —
the content of `FoldPreTensorCombineAffineSplitResidual`, proven row-by-row from the
multilinearity theorem, the first-step peel, and the LSB-split tensor recursion. -/
theorem fold_preTensorCombine_affineSplit_proven
    (i : Fin ℓ) (steps : ℕ) {midIdx destIdx : Fin r}
    (h_midIdx : midIdx.val = i.val + 1)
    (h_destIdx : destIdx.val = i.val + (steps + 1))
    (h_destIdx_le : destIdx ≤ ℓ)
    (f_i : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ⟨i.val, lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (le_of_lt i.isLt)⟩)
    (r_new : L)
    (h_midIdx_lt_ℓ : midIdx.val < ℓ) :
    interleaveWordStack
      (preTensorCombine_WordStack 𝔽q β (⟨midIdx.val, h_midIdx_lt_ℓ⟩ : Fin ℓ) steps
        (destIdx := destIdx)
        (h_destIdx := by omega)
        (h_destIdx_le := h_destIdx_le)
        (fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := ⟨i.val, lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (le_of_lt i.isLt)⟩)
          (destIdx := midIdx) (h_destIdx := h_midIdx)
          (h_destIdx_le := by omega) f_i r_new)) =
      affineLineEvaluation (F := L)
        (interleaveWordStack ((splitEvenOddRowWiseInterleavedWords (r := r) (ℓ := ℓ) (𝓡 := 𝓡)
          (ϑ := steps)
          (preTensorCombine_WordStack 𝔽q β i (steps + 1) (destIdx := destIdx)
            (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) f_i)).1))
        (interleaveWordStack ((splitEvenOddRowWiseInterleavedWords (r := r) (ℓ := ℓ) (𝓡 := 𝓡)
          (ϑ := steps)
          (preTensorCombine_WordStack 𝔽q β i (steps + 1) (destIdx := destIdx)
            (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) f_i)).2))
        r_new := by
  -- Row-wise: V k = (1 - r_new) • U_even k + r_new • U_odd k.
  have hrow : ∀ k : Fin (2 ^ steps),
      preTensorCombine_WordStack 𝔽q β (⟨midIdx.val, h_midIdx_lt_ℓ⟩ : Fin ℓ) steps
        (destIdx := destIdx) (h_destIdx := by omega) (h_destIdx_le := h_destIdx_le)
        (fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := ⟨i.val, lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (le_of_lt i.isLt)⟩)
          (destIdx := midIdx) (h_destIdx := h_midIdx)
          (h_destIdx_le := by omega) f_i r_new) k
      = (1 - r_new) • (splitEvenOddRowWiseInterleavedWords (r := r) (ℓ := ℓ) (𝓡 := 𝓡)
            (ϑ := steps)
            (preTensorCombine_WordStack 𝔽q β i (steps + 1) (destIdx := destIdx)
              (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) f_i)).1 k
        + r_new • (splitEvenOddRowWiseInterleavedWords (r := r) (ℓ := ℓ) (𝓡 := 𝓡)
            (ϑ := steps)
            (preTensorCombine_WordStack 𝔽q β i (steps + 1) (destIdx := destIdx)
              (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) f_i)).2 k := by
    intro k
    -- The first-step peel at the challenge vector `cons r_new (bitsOfIndex k)`.
    have hfirst := iterated_fold_first 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := ⟨i.val, lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (le_of_lt i.isLt)⟩)
      (midIdx := midIdx) (destIdx := destIdx) (steps := steps)
      (h_midIdx := h_midIdx) (h_destIdx := by omega) (h_destIdx_le := h_destIdx_le)
      f_i (Fin.cons r_new (bitsOfIndex (L := L) k))
    simp only [Fin.cons_zero, Fin.cons_succ] at hfirst
    -- The V row is the RHS of the peel.
    have hV : preTensorCombine_WordStack 𝔽q β (⟨midIdx.val, h_midIdx_lt_ℓ⟩ : Fin ℓ) steps
        (destIdx := destIdx) (h_destIdx := by omega) (h_destIdx_le := h_destIdx_le)
        (fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := ⟨i.val, lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (le_of_lt i.isLt)⟩)
          (destIdx := midIdx) (h_destIdx := h_midIdx)
          (h_destIdx_le := by omega) f_i r_new) k
        = iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            (i := ⟨i.val, lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              (le_of_lt i.isLt)⟩)
            (steps := steps + 1) (destIdx := destIdx)
            (h_destIdx := by omega) (h_destIdx_le := h_destIdx_le) (f := f_i)
            (r_challenges := Fin.cons r_new (bitsOfIndex (L := L) k)) := by
      rw [hfirst]
      -- Both sides are `iterated_fold` of the same single-step fold at start indices with
      -- equal `.val` (structure eta) and the same challenges: definitionally equal.
      rfl
    rw [hV]
    -- Multilinearity at `steps + 1`, then factor the first challenge.
    rw [iterated_fold_eq_multilinearCombine_preTensorCombine_proven 𝔽q β i (steps + 1)
      (h_destIdx := by omega) (h_destIdx_le := h_destIdx_le) f_i
      (Fin.cons r_new (bitsOfIndex (L := L) k))]
    have hfirstrec := multilinearCombine_recursive_form_first
      (r := r) (ℓ := ℓ) (𝓡 := 𝓡)
      (u := preTensorCombine_WordStack 𝔽q β i (steps + 1) (destIdx := destIdx)
        (h_destIdx := by omega) (h_destIdx_le := h_destIdx_le) f_i)
      (r_challenges := Fin.cons r_new (bitsOfIndex (L := L) k))
    dsimp only at hfirstrec
    simp only [Fin.cons_zero, Fin.cons_succ] at hfirstrec
    rw [hfirstrec]
    -- Collapse the binary tail with the indicator property.
    rw [multilinearCombine_bitsOfIndex]
    simp only [affineLineEvaluation, Pi.add_apply, Pi.smul_apply]
  -- Lift the row identity through the interleave (transpose).
  funext y
  funext k
  have h := congrFun (hrow k) y
  simp only [Pi.add_apply, Pi.smul_apply] at h
  simp only [interleaveWordStack, Matrix.transpose_apply, affineLineEvaluation,
    Pi.add_apply, Pi.smul_apply]
  exact h

/-- **Issue #317: `FoldPreTensorCombineAffineSplitResidual` DISCHARGED.** -/
instance instFoldPreTensorCombineAffineSplitResidualProven :
    FoldPreTensorCombineAffineSplitResidual (r := r) (L := L) (𝔽q := 𝔽q) (β := β)
      (ℓ := ℓ) (𝓡 := 𝓡) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) where
  holds := by
    intro i steps _ midIdx destIdx h_midIdx h_destIdx h_destIdx_le f_i r_new
    intro h_midIdx_lt_ℓ U U_even U_odd fold_1_f midIdx_fin_ℓ V
    exact fold_preTensorCombine_affineSplit_proven 𝔽q β i steps
      (h_midIdx := h_midIdx) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
      f_i r_new h_midIdx_lt_ℓ

end AffineSplit

end

end Binius.BinaryBasefold

/-! ### Axiom audit (issue #317 preTensorCombine residual discharges) -/

#print axioms Binius.BinaryBasefold.iterated_fold_eq_multilinearCombine_preTensorCombine_proven
#print axioms Binius.BinaryBasefold.instPreTensorCombineMultilinearResidualProven
#print axioms Binius.BinaryBasefold.fold_preTensorCombine_affineSplit_proven
#print axioms Binius.BinaryBasefold.instFoldPreTensorCombineAffineSplitResidualProven
