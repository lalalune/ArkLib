/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Binius.BinaryBasefold.Code

/-!
# Iterated fold advances the intermediate evaluation polynomial (BCIKS Lemma 4.13, iterated)

This file proves `iterated_fold_advances_evaluation_poly`: iterating the single-step fold
`steps` times (from level `i` to `destIdx = i + steps`) on the oracle function of the
intermediate evaluation polynomial `intermediateEvaluationPoly i coeffs` yields the oracle
function of `intermediateEvaluationPoly destIdx new_coeffs`, where `new_coeffs` is the iterated
coefficient refinement `fun j => ∑ x, multilinearWeight r_challenges x * coeffs ⟨j*2^steps + x⟩`.

It is the iterated form of the single-step `fold_advances_evaluation_poly_legacy`, proven by
induction on `steps`.
-/

namespace Binius.BinaryBasefold

open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial
  Binius.BinaryBasefold
open scoped NNReal
open ReedSolomon Code BerlekampWelch Function
open Finset AdditiveNTT Polynomial MvPolynomial Nat Matrix

noncomputable section

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))] [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ 𝓡 : ℕ} [NeZero ℓ] [NeZero 𝓡]
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r}

/-- The iterated coefficient refinement: after `steps` folds with challenges `r_challenges`,
coefficient `j` of the resulting polynomial is the multilinear-weight combination of the
original coefficients in the block `[j*2^steps, (j+1)*2^steps)`. -/
def iteratedRefineCoeffs {i destIdx : Fin r} (steps : ℕ)
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (coeffs : Fin (2 ^ (ℓ - i.val)) → L) (r_challenges : Fin steps → L) :
    Fin (2 ^ (ℓ - destIdx.val)) → L :=
  fun j => ∑ x : Fin (2 ^ steps), multilinearWeight r_challenges x *
    coeffs ⟨j.val * 2 ^ steps + x.val, by
      have hle : i.val + steps ≤ ℓ := by rw [← h_destIdx]; exact h_destIdx_le
      have hpow : 2 ^ (ℓ - i.val) = 2 ^ (ℓ - destIdx.val) * 2 ^ steps := by
        rw [← pow_add]; congr 1; omega
      rw [hpow]
      have hj := j.isLt
      have hx := x.isLt
      calc j.val * 2 ^ steps + x.val
          < j.val * 2 ^ steps + 2 ^ steps := by omega
        _ = (j.val + 1) * 2 ^ steps := by ring
        _ ≤ 2 ^ (ℓ - destIdx.val) * 2 ^ steps := by
            apply Nat.mul_le_mul_right; omega⟩

omit [CharP L 2] [DecidableEq 𝔽q] [NeZero ℓ] in
/-- Single-step new-API version of `fold_advances_evaluation_poly_legacy`: folding the raw-eval
oracle function of `intermediateEvaluationPoly i coeffs` (via the `{destIdx}`-keyed `fold`)
yields the raw-eval oracle function of `intermediateEvaluationPoly destIdx new_coeffs`, where
`new_coeffs j = (1 - r_chal) * coeffs⟨2j⟩ + r_chal * coeffs⟨2j+1⟩`. -/
theorem fold_advances_evaluation_poly_step
    (i : Fin r) {destIdx : Fin r} (h_i_lt : i.val < ℓ)
    (h_destIdx : destIdx.val = i.val + 1) (h_destIdx_le : destIdx ≤ ℓ)
    (coeffs : Fin (2 ^ (ℓ - i.val)) → L) (r_chal : L)
    (new_coeffs : Fin (2 ^ (ℓ - destIdx.val)) → L)
    (h_new_coeffs : ∀ j : Fin (2 ^ (ℓ - destIdx.val)),
      new_coeffs j =
        (1 - r_chal) * coeffs ⟨j.val * 2, by
          have hpow : 2 ^ (ℓ - i.val) = 2 ^ (ℓ - destIdx.val) * 2 := by
            rw [← pow_succ]; congr 1; omega
          have := j.isLt; rw [hpow]; omega⟩ +
        r_chal * coeffs ⟨j.val * 2 + 1, by
          have hpow : 2 ^ (ℓ - i.val) = 2 ^ (ℓ - destIdx.val) * 2 := by
            rw [← pow_succ]; congr 1; omega
          have := j.isLt; rw [hpow]; omega⟩) :
    fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (destIdx := destIdx)
        (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
        (f := fun x => (intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate
          ⟨i.val, by omega⟩ coeffs).eval x.val) (r_chal := r_chal) =
      fun y => (intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate
        ⟨destIdx.val, by omega⟩ new_coeffs).eval y.val := by
  classical
  -- Reduce `destIdx` to its canonical `⟨i+1, _⟩` form. The index bound is derived from
  -- `h_i_lt`/`h_ℓ_add_R_rate` alone (independent of `h_destIdx`), so `subst` is unobstructed.
  have ha_lt0 : i.val + 1 < r := by
    have hR : 0 < 𝓡 := Nat.pos_of_neZero 𝓡
    omega
  have hdest : destIdx = (⟨i.val + 1, ha_lt0⟩ : Fin r) := Fin.eq_of_val_eq h_destIdx
  subst hdest
  -- Invoke the legacy single-step advance lemma at `i' : Fin ℓ`.
  have h_i_succ_lt : i.val + 1 < ℓ + 𝓡 := by
    have hR : 0 < 𝓡 := Nat.pos_of_neZero 𝓡
    omega
  have h_legacy := fold_advances_evaluation_poly_legacy 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨i.val, h_i_lt⟩)
    (h_i_succ_lt := by simpa using h_i_succ_lt) (coeffs := coeffs) (r_chal := r_chal)
  simp only at h_legacy
  funext y
  -- Unfold `fold`: at the canonical destination index `⟨i+1, _⟩` the cast collapses.
  unfold fold
  simp only [cast_eq]
  -- Apply the legacy advance at the point `y` (now at the canonical index).
  rw [h_legacy ⟨y.val, y.property⟩]
  -- Reconcile the legacy `new_coeffs` with our `new_coeffs` pointwise.
  congr 1
  unfold intermediateEvaluationPoly
  apply Finset.sum_congr rfl
  rintro ⟨j, hj⟩ _
  simp only
  rw [h_new_coeffs ⟨j, hj⟩]

omit [Fintype L] [DecidableEq L] [CharP L 2] [NeZero ℓ] [NeZero 𝓡] in
/-- **Low half of the multilinear weight tensor.** For `x : Fin (2^n)` (so the top bit `n` of
`x` is `0`), the `(n+1)`-challenge weight at index `x` factors as the `n`-challenge weight at
`x` (over `Fin.init r`) times `(1 - r (last n))`. -/
theorem multilinearWeight_castSucc_low {n : ℕ} (r : Fin (n + 1) → L) (x : Fin (2 ^ n)) :
    multilinearWeight r ⟨x.val, by
      have := x.isLt; calc x.val < 2 ^ n := this
        _ ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by omega) (by omega)⟩ =
      multilinearWeight (Fin.init r) x * (1 - r (Fin.last n)) := by
  have h_getLastBit : Nat.getBit (Fin.last n) x.val = 0 := by
    have h := Nat.getBit_of_lt_two_pow (a := x) (k := Fin.last n)
    simp only [Fin.val_last, lt_self_iff_false, ↓reduceIte] at h
    exact h
  dsimp only [multilinearWeight]
  rw [Fin.prod_univ_castSucc]
  simp_rw [Nat.testBit_true_eq_getBit_eq_1]
  simp_rw [h_getLastBit]
  simp only [Fin.val_castSucc, Fin.init]
  congr 1

omit [Fintype L] [DecidableEq L] [CharP L 2] [NeZero ℓ] [NeZero 𝓡] in
/-- **High half of the multilinear weight tensor.** For `x : Fin (2^n)`, the `(n+1)`-challenge
weight at index `2^n + x` (top bit `n` set) factors as the `n`-challenge weight at `x`
(over `Fin.init r`) times `r (last n)`. -/
theorem multilinearWeight_castSucc_high {n : ℕ} (r : Fin (n + 1) → L) (x : Fin (2 ^ n)) :
    multilinearWeight r ⟨2 ^ n + x.val, by
      have := x.isLt; rw [pow_succ]; omega⟩ =
      multilinearWeight (Fin.init r) x * (r (Fin.last n)) := by
  have h_getLastBit : Nat.getBit (Fin.last n) x.val = 0 := by
    have h := Nat.getBit_of_lt_two_pow (a := x) (k := Fin.last n)
    simp only [Fin.val_last, lt_self_iff_false, ↓reduceIte] at h
    exact h
  have h_x_and_two_pow : x.val &&& (2 ^ n) = 0 := by
    apply Nat.and_two_pow_eq_zero_of_getBit_0 (n := x.val) (i := n)
    exact h_getLastBit
  have h_x_add_two_pow := Nat.sum_of_and_eq_zero_is_xor
    (n := x.val) (m := 2 ^ n) (h_n_AND_m := h_x_and_two_pow)
  have h_x_add_two_pow_comm : 2 ^ n + x.val = x.val ^^^ 2 ^ n := by
    rw [Nat.add_comm]
    exact h_x_add_two_pow
  have h_getLastBit_add_pow : Nat.getBit (Fin.last n) (2 ^ n + x.val) = 1 := by
    rw [h_x_add_two_pow_comm]
    rw [Nat.getBit_of_xor]
    rw [h_getLastBit]
    rw [Nat.getBit_two_pow]
    simp only [Fin.val_last, BEq.rfl, ↓reduceIte, Nat.zero_xor]
  dsimp only [multilinearWeight]
  rw [Fin.prod_univ_castSucc]
  simp_rw [Nat.testBit_true_eq_getBit_eq_1]
  simp_rw [h_getLastBit_add_pow]
  simp only [Fin.val_last, Fin.val_castSucc, Fin.init, ↓reduceIte]
  congr 1
  apply Finset.prod_congr rfl
  intro k _
  rw [h_x_add_two_pow_comm]
  simp_rw [Nat.getBit_of_xor, Nat.getBit_two_pow]
  simp only [beq_iff_eq]
  have h_k_ne_n : n ≠ k.val := by omega
  simp only [h_k_ne_n, ↓reduceIte, Nat.xor_zero]
  rfl

end

end Binius.BinaryBasefold

-- Axiom audit.
#print axioms Binius.BinaryBasefold.fold_advances_evaluation_poly_step
