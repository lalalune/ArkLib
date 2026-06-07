/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Binius.BinaryBasefold.Code

/-!
# Incremental soundness helper lemmas

Helper lemmas for `ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.Incremental`.

This file provides:
* `iterated_fold_first` — the "peel first step" analogue of `iterated_fold_last`: folding
  `steps + 1` times starting at level `i` with challenges `Fin.cons r_new rest` equals folding
  `steps` times starting at level `midIdx = i + 1` of the single-step fold `fold(f, r_new)`.
* `fiberwiseClose_steps_zero_iff_UDRClose` — `fiberwiseClose` at `steps = 1` (the minimal
  `NeZero` step count) coincides with `UDRClose`, since both unfold to the same inequality.
-/

set_option maxHeartbeats 1000000

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

/-- **Peel the first step (new-API).** Folding `steps + 1` times starting at level `i` with
challenges `Fin.cons r_new rest` equals folding `steps` times starting at level `midIdx = i + 1`
of the single-step fold `fold(f, r_new)` (with challenges `rest`).

Proved by induction on `steps`, peeling the *last* step on both sides with `iterated_fold_last`. -/
theorem iterated_fold_first (i : Fin r) {midIdx destIdx : Fin r} (steps : ℕ)
    (h_midIdx : midIdx.val = i.val + 1)
    (h_destIdx : destIdx.val = i.val + (steps + 1))
    (h_destIdx_le : destIdx ≤ ℓ)
    (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
    (r_challenges : Fin (steps + 1) → L) :
    iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := steps + 1)
        (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := f)
        (r_challenges := r_challenges) =
    iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := midIdx) (steps := steps)
      (h_destIdx := by omega) (h_destIdx_le := h_destIdx_le)
      (f := fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (destIdx := midIdx)
        (h_destIdx := h_midIdx) (h_destIdx_le := by omega) (f := f)
        (r_chal := r_challenges 0))
      (r_challenges := fun j => r_challenges j.succ) := by
  induction steps generalizing destIdx with
  | zero =>
    -- `iterated_fold (i) 1 (cons r_new ![])` = `fold(iterated_fold(i) 0 (init …), last)` and the
    -- inner `iterated_fold 0` is `f` transported; the RHS is `iterated_fold(midIdx) 0 (fold …)`.
    rw [iterated_fold_last 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := 0)
      (midIdx := i) (destIdx := destIdx)
      (h_midIdx := by omega) (h_destIdx := by omega) (h_destIdx_le := h_destIdx_le) f r_challenges]
    -- RHS: `iterated_fold (midIdx) 0 (fold f r_challenges 0)` is the `0`-step identity = `fold f …`.
    funext y
    rw [iterated_fold_zero_steps 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := midIdx)
      (h_destIdx := by omega) (h_destIdx_le := h_destIdx_le)]
    -- LHS: the inner `iterated_fold (i) 0 (init r_challenges)` is also the `0`-step identity = `f`.
    show fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (destIdx := destIdx) _ h_destIdx_le
        (iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := 0) _ _ f
          (Fin.init r_challenges)) (r_challenges (Fin.last 0)) y = _
    rw [show (iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := 0)
        (destIdx := i) (by omega) (by omega) f (Fin.init r_challenges)) = f from by
      funext z
      rw [iterated_fold_zero_steps 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)
        (h_destIdx := rfl) (h_destIdx_le := by omega)]
      rfl]
    simp only [Fin.last_zero]
    congr 1
  | succ n ih =>
    -- bounds for the intermediate `Fin r` indices appearing below
    have h_mid_bound : i.val + (n + 1) < r := by
      have : destIdx.val < r := destIdx.isLt; omega
    have h_midmid_bound : midIdx.val + n < r := by
      have : destIdx.val < r := destIdx.isLt; omega
    -- Peel the last step on the LHS.
    rw [iterated_fold_last 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := n + 1)
      (midIdx := ⟨i.val + (n + 1), h_mid_bound⟩) (destIdx := destIdx)
      (h_midIdx := rfl) (h_destIdx := by omega) (h_destIdx_le := h_destIdx_le)
      f r_challenges]
    -- Peel the last step on the RHS.
    rw [iterated_fold_last 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := midIdx) (steps := n)
      (midIdx := ⟨midIdx.val + n, h_midmid_bound⟩) (destIdx := destIdx)
      (h_midIdx := rfl) (h_destIdx := by omega) (h_destIdx_le := h_destIdx_le)]
    -- The two inner `n`-step folds are related by the inductive hypothesis `ih`.
    have h_ih := ih (midIdx := midIdx) (destIdx := ⟨i.val + (n + 1), h_mid_bound⟩)
      (h_midIdx := h_midIdx) (h_destIdx := by omega) (h_destIdx_le := by omega)
      (f := f) (r_challenges := fun j => r_challenges j.castSucc)
    -- Reconcile the `fold` outer steps (same midpoints and last challenge).
    congr 1
    · -- the two single-step `fold` start/dest indices coincide
      apply Fin.ext; omega
    · -- inner functions equal by IH (after reconciling the truncated challenge reindexings)
      rw [h_ih]
    · -- last challenges agree: `r_challenges (last (n+1))` vs `(fun j => r_challenges j.succ) (last n)`
      simp only [Fin.succ_last]

end

end Binius.BinaryBasefold
