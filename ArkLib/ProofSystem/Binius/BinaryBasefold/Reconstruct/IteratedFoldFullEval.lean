/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Binius.BinaryBasefold.Reconstruct.IteratedFoldToLevel

/-!
# Full-depth fold of a consistency codeword is a constant evaluation

The honest replacement for the phantom `iterated_fold_to_level_ℓ_eval` cited by the
quarantined extractor draft (`Steps/FinalSumcheckExtractorDraft.wip`): folding the level-`0`
novel-coefficient encoding of a multilinear polynomial `t` through ALL `ℓ` levels with
challenge vector `rc` is the constant function with value `t` evaluated at `rc ∘ Fin.rev`.

The `Fin.rev` is the challenge-order reconciliation seam the draft's header warns about, now
explicit in the statement instead of buried: the fold consumes challenges in fold order while
the multilinear evaluation point is in statement order, and
`multilinear_eval_eq_sum_statementOrderBitsOfIndex` exchanges the two through the reversal.
A consumer whose fold challenges are already fold-order slices (e.g. via
`foldOrderChallenges`) recovers the un-reversed evaluation — see
`getLastOracle_finalFold_eq_eval` (Reconstruct/FinalConstantWeld) for that instantiation.

Proof recipe (the weld's, without the prefix/final split):
`intermediate_poly_P_base` (CompPoly) → `iterated_fold_advances_evaluation_poly_nat` →
`intermediateEvaluationPoly_last_iteratedRefineCoeffs_eval` →
`multilinear_eval_eq_sum_statementOrderBitsOfIndex`.
-/

namespace Binius.BinaryBasefold

open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial
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

/-- **Full-depth fold of the consistency codeword, sum form.** Folding the level-`0`
novel-coefficient encoding of `coeffs` through all `ℓ` levels with challenges `rc` is the
constant function whose value is the `multilinearWeight rc`-weighted sum of `coeffs`. -/
lemma iterated_fold_full_eq_weight_sum
    (destIdx : Fin r) (h_destIdx : destIdx.val = ℓ)
    (coeffs : Fin (2 ^ ℓ) → L) (rc : Fin ℓ → L) :
    iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := (0 : Fin r)) (steps := ℓ) (destIdx := destIdx)
      (h_destIdx := by rw [h_destIdx]; exact (Nat.zero_add ℓ).symm)
      (h_destIdx_le := by
        show destIdx.val ≤ ℓ
        omega)
      (f := fun x => (polynomialFromNovelCoeffsF₂ 𝔽q β ℓ (by omega : ℓ ≤ r) coeffs).val.eval
        x.val)
      (r_challenges := rc) =
      fun _ => ∑ x : Fin (2 ^ ℓ), multilinearWeight rc x * coeffs x := by
  have h𝓡 : 0 < 𝓡 := Nat.pos_of_neZero 𝓡
  have hℓ_lt_r : ℓ < r := by omega
  let finalIdx : Fin r := ⟨(Fin.last ℓ).val, by
    simpa only [Fin.val_last] using hℓ_lt_r⟩
  -- normalize the destination index to the canonical `⟨(Fin.last ℓ).val, _⟩`
  obtain rfl : destIdx = finalIdx :=
    Fin.eq_of_val_eq (by simpa using h_destIdx)
  -- Step 1: the codeword is the raw-eval of the level-0 intermediate evaluation polynomial.
  have h_base := intermediate_poly_P_base 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (h_ℓ := by omega) (coeffs := coeffs)
  have h_f₀ :
      (fun (x : sDomain 𝔽q β h_ℓ_add_R_rate 0) =>
        (polynomialFromNovelCoeffsF₂ 𝔽q β ℓ (by omega : ℓ ≤ r) coeffs).val.eval x.val) =
      (fun (x : sDomain 𝔽q β h_ℓ_add_R_rate 0) =>
        (intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate
          ⟨(0 : Fin r).val, by
            have h0 : (0 : Fin r).val = 0 := rfl
            omega⟩ coeffs).eval x.val) := by
    funext x
    exact (congrArg (fun p => Polynomial.eval x.val p) h_base).symm
  rw [h_f₀]
  -- Step 2: advance the fold from level 0 to level ℓ in one pass.
  change
    iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := (0 : Fin r)) (steps := ℓ) (destIdx := finalIdx)
      (h_destIdx := by simp [finalIdx]) (h_destIdx_le := by simp [finalIdx])
      (f := fun x => (intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate
        ⟨(0 : Fin r).val, by
          have h0 : (0 : Fin r).val = 0 := rfl
          omega⟩ coeffs).eval x.val)
      (r_challenges := rc) =
    fun _ => ∑ x : Fin (2 ^ ℓ), multilinearWeight rc x * coeffs x
  rw [iterated_fold_advances_evaluation_poly_nat 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := (0 : Fin r)) (steps := ℓ)
    (destIdx := finalIdx)
    (h_destIdx := by simp [finalIdx]) (h_destIdx_le := by simp [finalIdx])
    (coeffs := coeffs) (r_challenges := rc)]
  -- Step 3: the endpoint evaluation is the multilinear-weight sum (constant in `y`).
  funext y
  exact intermediateEvaluationPoly_last_iteratedRefineCoeffs_eval 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (coeffs := coeffs) (r_challenges := rc) (y := y)

/-- **Full-depth fold of a multilinear consistency codeword, evaluation form** (the honest
`iterated_fold_to_level_ℓ_eval`). The constant value is `t` evaluated at `rc ∘ Fin.rev`:
fold-order challenges against the statement-order coefficient encoding. -/
lemma iterated_fold_to_level_ℓ_eval
    (destIdx : Fin r) (h_destIdx : destIdx.val = ℓ)
    (t : MultilinearPoly L ℓ) (rc : Fin ℓ → L) :
    iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := (0 : Fin r)) (steps := ℓ) (destIdx := destIdx)
      (h_destIdx := by rw [h_destIdx]; exact (Nat.zero_add ℓ).symm)
      (h_destIdx_le := by
        show destIdx.val ≤ ℓ
        omega)
      (f := fun x => (polynomialFromNovelCoeffsF₂ 𝔽q β ℓ (by omega : ℓ ≤ r)
        (fun ω => t.val.eval (statementOrderBitsOfIndex (L := L) ω))).val.eval x.val)
      (r_challenges := rc) =
      fun _ => t.val.eval (fun j => rc (Fin.rev j)) := by
  rw [iterated_fold_full_eq_weight_sum 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    destIdx h_destIdx
    (coeffs := fun ω => t.val.eval (statementOrderBitsOfIndex (L := L) ω)) (rc := rc)]
  funext y
  have h_sum := multilinear_eval_eq_sum_statementOrderBitsOfIndex
    (t := t) (r := fun j => rc (Fin.rev j))
  have h_weights :
      (fun j : Fin ℓ => (fun j' : Fin ℓ => rc (Fin.rev j')) (Fin.rev j)) = rc := by
    funext j
    simp
  rw [h_weights] at h_sum
  exact h_sum.symm

end

end Binius.BinaryBasefold

#print axioms Binius.BinaryBasefold.iterated_fold_full_eq_weight_sum
#print axioms Binius.BinaryBasefold.iterated_fold_to_level_ℓ_eval
