/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Binius.BinaryBasefold.Code

/-!
# Iterated fold advances the intermediate evaluation polynomial (BCIKS-Binius Lemma 4.13)

This file proves the general-level-`i` form of BCIKS-Binius Lemma 4.13: iterating the
Binary-Basefold fold `steps` times advances the intermediate evaluation polynomial.

The main result `iterated_fold_advances_evaluation_poly` shows that the `steps`-fold of the
codeword `polyToOracleFunc i (intermediateEvaluationPoly ⟨i⟩ coeffs)` is the codeword
`polyToOracleFunc destIdx (intermediateEvaluationPoly ⟨i+steps⟩ (foldedNovelCoeffs …))`, where
the folded novel coefficients `foldedNovelCoeffs` are the `multilinearWeight`-tensor combination
of the originals:
`foldedNovelCoeffs i steps coeffs r j = ∑ x, multilinearWeight r x * coeffs ⟨j * 2^steps + x⟩`.

## Proof outline

* `foldedNovelCoeffs_succ` — the one-fold recurrence for the folded coefficients, matching the
  proven legacy single-step `(1 - r)·c(2j) + r·c(2j+1)` form. Proved from a binary MSB-split of
  `multilinearWeight` (`mlw_split`) and an MSB sum-split (`sum_split_two`).
* `degree_intermediateEvaluationPoly_lt` — the general-`i` degree bound packaging
  `intermediateEvaluationPoly` as a Reed-Solomon-domain codeword via `polyToOracleFunc`. Proved
  bottom-up from `degree (qMap) ≤ 2` through `intermediateNormVpoly`/`intermediateNovelBasisX`.
* `iterated_fold_advances_aux` — the induction (on `steps`), peeling the last fold via
  `iterated_fold_last`, bridging new-API `fold` to `fold_legacy` (`fold_eq_fold_legacy`), then
  applying the proven single-step `fold_advances_evaluation_poly_legacy` and `foldedNovelCoeffs_succ`.
* `iterated_fold_advances_evaluation_poly` — the public `polyToOracleFunc`-wrapped restatement
  consumed by `ReductionLogic`.
-/

namespace Binius.BinaryBasefold
open AdditiveNTT Polynomial Finset Nat
noncomputable section

section Combinatorics
variable {L : Type} [Field L] [Fintype L] [DecidableEq L]
variable {ℓ : ℕ}
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

private lemma idx_bound {i steps : ℕ} (h : i + steps ≤ ℓ)
    (j : Fin (2 ^ (ℓ - (i + steps)))) (x : Fin (2 ^ steps)) :
    (j : ℕ) * 2 ^ steps + (x : ℕ) < 2 ^ (ℓ - i) := by
  have h1 : ℓ - i = (ℓ - (i + steps)) + steps := by omega
  rw [h1, pow_add]; have hj := j.isLt; have hx := x.isLt
  calc (j : ℕ) * 2 ^ steps + (x : ℕ) < (j : ℕ) * 2 ^ steps + 2 ^ steps := by omega
    _ = ((j : ℕ) + 1) * 2 ^ steps := by ring
    _ ≤ 2 ^ (ℓ - (i + steps)) * 2 ^ steps := by apply Nat.mul_le_mul_right; omega

/-- The folded novel coefficients after `steps` folds with challenges `rc`. -/
def foldedNovelCoeffs (i steps : ℕ) (h : i + steps ≤ ℓ)
    (coeffs : Fin (2 ^ (ℓ - i)) → L) (rc : Fin steps → L) :
    Fin (2 ^ (ℓ - (i + steps))) → L :=
  fun j => ∑ x : Fin (2 ^ steps),
    multilinearWeight rc x * coeffs ⟨(j : ℕ) * 2 ^ steps + (x : ℕ), idx_bound h j x⟩

private lemma mlw_split {steps : ℕ} (rr : Fin (steps + 1) → L) (x' : Fin (2 ^ (steps + 1))) :
    multilinearWeight rr x' =
      multilinearWeight (Fin.init rr) ⟨x'.val % 2 ^ steps, Nat.mod_lt _ (Nat.two_pow_pos steps)⟩ *
        (if x'.val / 2 ^ steps = 1 then rr (Fin.last steps) else 1 - rr (Fin.last steps)) := by
  unfold multilinearWeight
  rw [Fin.prod_univ_castSucc]
  congr 1
  · apply Finset.prod_congr rfl
    intro j _
    have hbit : x'.val.testBit j.castSucc.val = (x'.val % 2 ^ steps).testBit j.val := by
      rw [Fin.val_castSucc, Nat.testBit_mod_two_pow]
      simp only [j.isLt, decide_true, Bool.true_and]
    rw [hbit]; rfl
  · have hb : x'.val.testBit (Fin.last steps).val = decide (x'.val / 2 ^ steps = 1) := by
      rw [Fin.val_last, Nat.testBit_eq_decide_div_mod_eq]
      have hpe : (2:Nat) ^ (steps + 1) = 2 ^ steps * 2 := by rw [pow_succ]
      have hlt : x'.val < 2 ^ steps * 2 := hpe ▸ x'.isLt
      have hdiv : x'.val / 2 ^ steps < 2 := Nat.div_lt_of_lt_mul hlt
      interval_cases h : (x'.val / 2 ^ steps) <;> simp
    rw [hb]
    by_cases h : x'.val / 2 ^ steps = 1 <;> simp [h]

private lemma sum_split_two {A : Type} [AddCommMonoid A] (s : Nat) (g : Fin (2 ^ (s+1)) → A) :
    ∑ x' : Fin (2 ^ (s+1)), g x' =
      ∑ b : Fin 2, ∑ x : Fin (2 ^ s), g ⟨b.val * 2 ^ s + x.val, by
        have := x.isLt; have := b.isLt
        calc b.val * 2 ^ s + x.val < b.val * 2^s + 2^s := by omega
          _ = (b.val + 1) * 2^s := by ring
          _ ≤ 2 * 2^s := by apply Nat.mul_le_mul_right; omega
          _ = 2 ^ (s+1) := by rw [pow_succ]; ring⟩ := by
  rw [← Fintype.sum_prod_type']
  symm
  apply Fintype.sum_bijective (fun (p : Fin 2 × Fin (2^s)) =>
    (⟨p.1.val * 2^s + p.2.val, by
      have := p.2.isLt; have := p.1.isLt
      calc p.1.val * 2 ^ s + p.2.val < p.1.val * 2^s + 2^s := by omega
        _ = (p.1.val + 1) * 2^s := by ring
        _ ≤ 2 * 2^s := by apply Nat.mul_le_mul_right; omega
        _ = 2 ^ (s+1) := by rw [pow_succ]; ring⟩ : Fin (2^(s+1))))
  · constructor
    · rintro ⟨b1, x1⟩ ⟨b2, x2⟩ h
      simp only [Fin.mk.injEq] at h
      have hx1 := x1.isLt; have hx2 := x2.isLt
      have hb1 := b1.isLt; have hb2 := b2.isLt
      have hxmod : x1.val = x2.val := by
        have e1 : (b1.val * 2^s + x1.val) % 2^s = x1.val := by
          rw [Nat.add_mod, Nat.mul_mod_left]; simp [Nat.mod_eq_of_lt hx1]
        have e2 : (b2.val * 2^s + x2.val) % 2^s = x2.val := by
          rw [Nat.add_mod, Nat.mul_mod_left]; simp [Nat.mod_eq_of_lt hx2]
        rw [← e1, ← e2, h]
      have hbmul : b1.val * 2^s = b2.val * 2^s := by omega
      have hb : b1.val = b2.val :=
        Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos s) hbmul
      ext <;> simp <;> omega
    · intro y
      refine ⟨(⟨y.val / 2^s, ?_⟩, ⟨y.val % 2^s, Nat.mod_lt _ (Nat.two_pow_pos s)⟩), ?_⟩
      · have hpe : (2:Nat) ^ (s + 1) = 2 ^ s * 2 := by rw [pow_succ]
        have hlt : y.val < 2 ^ s * 2 := hpe ▸ y.isLt
        exact Nat.div_lt_of_lt_mul hlt
      · apply Fin.ext; simp only; rw [Nat.div_add_mod']
  · intro p; rfl

/-- **Zero-step folded coefficients are the original coefficients.** -/
private lemma foldedNovelCoeffs_zero (i : ℕ) (h : i + 0 ≤ ℓ)
    (coeffs : Fin (2 ^ (ℓ - i)) → L) (rc : Fin 0 → L)
    (j : Fin (2 ^ (ℓ - (i + 0)))) :
    foldedNovelCoeffs i 0 h coeffs rc j
      = coeffs ⟨(j : ℕ), lt_of_lt_of_le j.isLt (by gcongr <;> omega)⟩ := by
  unfold foldedNovelCoeffs
  haveI huniq : Unique (Fin (2 ^ (0:ℕ))) := by rw [pow_zero]; exact Fin.instUnique
  rw [Fintype.sum_unique]
  have hmlw : ∀ d : Fin (2 ^ 0), multilinearWeight rc d = 1 := by
    intro d; unfold multilinearWeight; rw [Finset.prod_eq_one]; intro x _; exact x.elim0
  have hdef0 : ∀ d : Fin (2 ^ 0), d.val = 0 := by
    intro d; have := d.isLt; simp only [pow_zero] at this; omega
  rw [hmlw, one_mul]
  congr 1
  apply Fin.ext; simp only [pow_zero, mul_one, hdef0, add_zero]

/-- **One-fold recurrence for `foldedNovelCoeffs`** (matches the legacy single-step
`(1 - r)·c(2j) + r·c(2j+1)` form). -/
private lemma foldedNovelCoeffs_succ (i steps : ℕ) (hstep1 : i + (steps + 1) ≤ ℓ)
    (coeffs : Fin (2 ^ (ℓ - i)) → L) (rc : Fin (steps + 1) → L)
    (j : Fin (2 ^ (ℓ - (i + (steps + 1))))) :
    foldedNovelCoeffs i (steps + 1) hstep1 coeffs rc j =
      (1 - rc (Fin.last steps)) * foldedNovelCoeffs i steps (by omega) coeffs (Fin.init rc)
        ⟨2 * (j : ℕ), by
          have hj := j.isLt
          have he : ℓ - (i + steps) = (ℓ - (i + (steps + 1))) + 1 := by omega
          rw [he, pow_succ]; omega⟩
      + rc (Fin.last steps) * foldedNovelCoeffs i steps (by omega) coeffs (Fin.init rc)
        ⟨2 * (j : ℕ) + 1, by
          have hj := j.isLt
          have he : ℓ - (i + steps) = (ℓ - (i + (steps + 1))) + 1 := by omega
          rw [he, pow_succ]; omega⟩ := by
  conv_lhs => rw [foldedNovelCoeffs]
  rw [sum_split_two (A := L) steps, Fin.sum_univ_two]
  rw [foldedNovelCoeffs, foldedNovelCoeffs, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl; intro x _
    rw [mlw_split rc ⟨(0:Fin 2).val * 2 ^ steps + x.val, _⟩]
    have hmod : (⟨((0:Fin 2).val * 2 ^ steps + x.val) % 2 ^ steps,
        Nat.mod_lt _ (Nat.two_pow_pos steps)⟩ : Fin (2 ^ steps)) = x := by
      apply Fin.ext; simp only [Fin.val_zero, zero_mul, zero_add]; exact Nat.mod_eq_of_lt x.isLt
    have hdiv : ((0:Fin 2).val * 2 ^ steps + x.val) / 2 ^ steps = 0 := by
      simp only [Fin.val_zero, zero_mul, zero_add]; exact Nat.div_eq_of_lt x.isLt
    rw [hdiv, hmod, if_neg (by norm_num : ¬ (0:Nat) = 1)]
    have hc : (coeffs ⟨(j : ℕ) * 2 ^ (steps + 1) + (⟨(0:Fin 2).val * 2 ^ steps + x.val, by
          have := x.isLt; have := (0:Fin 2).isLt
          calc (0:Fin 2).val * 2 ^ steps + x.val < (0:Fin 2).val * 2^steps + 2^steps := by omega
            _ = ((0:Fin 2).val + 1) * 2^steps := by ring
            _ ≤ 2 * 2^steps := by apply Nat.mul_le_mul_right; omega
            _ = 2 ^ (steps+1) := by rw [pow_succ]; ring⟩ : Fin (2^(steps+1))).val,
          idx_bound hstep1 j _⟩)
        = coeffs ⟨(⟨2 * (j : ℕ), by
            have hj := j.isLt
            have he : ℓ - (i + steps) = (ℓ - (i + (steps + 1))) + 1 := by omega
            rw [he, pow_succ]; omega⟩ : Fin (2 ^ (ℓ - (i + steps)))).val * 2 ^ steps + x.val,
            idx_bound (by omega) _ x⟩ := by
      congr 1; apply Fin.ext
      simp only [Fin.val_zero, zero_mul, zero_add]
      have hpe : (2:Nat) ^ (steps + 1) = 2 ^ steps * 2 := by rw [pow_succ]
      rw [hpe]; ring
    rw [hc]; ring
  · apply Finset.sum_congr rfl; intro x _
    rw [mlw_split rc ⟨(1:Fin 2).val * 2 ^ steps + x.val, _⟩]
    have hmod : (⟨((1:Fin 2).val * 2 ^ steps + x.val) % 2 ^ steps,
        Nat.mod_lt _ (Nat.two_pow_pos steps)⟩ : Fin (2 ^ steps)) = x := by
      apply Fin.ext; simp only [Fin.val_one, one_mul]
      rw [Nat.add_mod_left, Nat.mod_eq_of_lt x.isLt]
    have hdiv : ((1:Fin 2).val * 2 ^ steps + x.val) / 2 ^ steps = 1 := by
      simp only [Fin.val_one, one_mul]
      rw [Nat.add_div_left _ (Nat.two_pow_pos steps), Nat.div_eq_of_lt x.isLt]
    rw [hdiv, hmod, if_pos rfl]
    have hc : (coeffs ⟨(j : ℕ) * 2 ^ (steps + 1) + (⟨(1:Fin 2).val * 2 ^ steps + x.val, by
          have := x.isLt; have := (1:Fin 2).isLt
          calc (1:Fin 2).val * 2 ^ steps + x.val < (1:Fin 2).val * 2^steps + 2^steps := by omega
            _ = ((1:Fin 2).val + 1) * 2^steps := by ring
            _ ≤ 2 * 2^steps := by apply Nat.mul_le_mul_right; omega
            _ = 2 ^ (steps+1) := by rw [pow_succ]; ring⟩ : Fin (2^(steps+1))).val,
          idx_bound hstep1 j _⟩)
        = coeffs ⟨(⟨2 * (j : ℕ) + 1, by
            have hj := j.isLt
            have he : ℓ - (i + steps) = (ℓ - (i + (steps + 1))) + 1 := by omega
            rw [he, pow_succ]; omega⟩ : Fin (2 ^ (ℓ - (i + steps)))).val * 2 ^ steps + x.val,
            idx_bound (by omega) _ x⟩ := by
      congr 1; apply Fin.ext
      simp only [Fin.val_one, one_mul]
      have hpe : (2:Nat) ^ (steps + 1) = 2 ^ steps * 2 := by rw [pow_succ]
      rw [hpe]; ring
    rw [hc]; ring

end Combinatorics

section DegreeAndMain
variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))] [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ 𝓡 : ℕ} [NeZero ℓ] [NeZero 𝓡]
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r}
set_option linter.unusedSectionVars false

private lemma natDegree_qMap_le (i : Fin r) : (qMap 𝔽q β i).natDegree ≤ 2 := by
  rw [qMap]
  refine le_trans (Polynomial.natDegree_mul_le) ?_
  have h1 : (C (((W 𝔽q β i).eval (β i))^(Fintype.card 𝔽q)
    / ((W 𝔽q β (i + 1)).eval (β (i + 1))))).natDegree = 0 := Polynomial.natDegree_C _
  rw [h1, zero_add]
  refine le_trans (Polynomial.natDegree_prod_le _ _) ?_
  have hone : ∀ c : 𝔽q, (X - C (algebraMap 𝔽q L c)).natDegree ≤ 1 := fun c => by
    refine le_trans (Polynomial.natDegree_sub_le _ _) ?_
    simp [Polynomial.natDegree_X]
  refine le_trans (Finset.sum_le_sum (g := fun _ : 𝔽q => 1) (fun c _ => hone c)) ?_
  rw [Finset.sum_const, Finset.card_univ, hF₂.out]; simp

private lemma natDegree_intermediateNormVpoly_le (i : Fin (ℓ + 1)) (k : Fin (ℓ - i + 1)) :
    (intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate i k).natDegree ≤ 2 ^ (k : ℕ) := by
  unfold intermediateNormVpoly
  induction k using Fin.induction with
  | zero => simp [Fin.foldl_zero, Polynomial.natDegree_X]
  | succ k' ih =>
    simp only [Fin.val_succ, Fin.val_castSucc] at ih ⊢
    rw [Fin.foldl_succ_last]
    refine le_trans (Polynomial.natDegree_comp_le) ?_
    calc (qMap 𝔽q β ⟨i + (Fin.last k').val, by omega⟩).natDegree
          * (Fin.foldl (k' : ℕ) (fun acc j => (qMap 𝔽q β ⟨i + j, by omega⟩).comp acc) X).natDegree
        ≤ 2 * 2 ^ (k' : ℕ) := Nat.mul_le_mul (natDegree_qMap_le 𝔽q β _) ih
      _ = 2 ^ (k' + 1 : ℕ) := by rw [pow_succ]; ring

private lemma natDegree_intermediateNovelBasisX_le (i : Fin (ℓ + 1)) (j : Fin (2 ^ (ℓ - i))) :
    (intermediateNovelBasisX 𝔽q β h_ℓ_add_R_rate i j).natDegree ≤ (j : ℕ) := by
  unfold intermediateNovelBasisX
  refine le_trans (Polynomial.natDegree_prod_le _ _) ?_
  have hterm : ∀ k : Fin (ℓ - i), ((intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate i
      ⟨k, by omega⟩) ^ Nat.getBit k.val j.val).natDegree
      ≤ Nat.getBit k.val j.val * 2 ^ (k : ℕ) := by
    intro k
    refine le_trans (Polynomial.natDegree_pow_le) ?_
    exact Nat.mul_le_mul_left _ (natDegree_intermediateNormVpoly_le 𝔽q β i ⟨k, by omega⟩)
  refine le_trans (Finset.sum_le_sum (fun k _ => hterm k)) ?_
  rw [← getBit_repr_univ j.val j.isLt]

/-- **Degree bound for the intermediate evaluation polynomial** (BCIKS reconstruction; the
general-`i` degree lemma needed to package `intermediateEvaluationPoly` as a Reed-Solomon-domain
codeword via `polyToOracleFunc`). -/
lemma degree_intermediateEvaluationPoly_lt (i : Fin (ℓ + 1))
    (coeffs : Fin (2 ^ (ℓ - i)) → L) :
    (intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate i coeffs).degree < 2 ^ (ℓ - (i:ℕ)) := by
  unfold intermediateEvaluationPoly
  apply (Polynomial.degree_sum_le _ _).trans_lt
  apply (Finset.sup_lt_iff ?_).mpr ?_
  · exact compareOfLessAndEq_eq_lt.mp rfl
  · rintro ⟨j, hj⟩ _
    calc (C (coeffs ⟨j, by omega⟩) * intermediateNovelBasisX 𝔽q β h_ℓ_add_R_rate i ⟨j, by omega⟩).degree
        ≤ (C (coeffs ⟨j, by omega⟩)).degree
            + (intermediateNovelBasisX 𝔽q β h_ℓ_add_R_rate i ⟨j, by omega⟩).degree := degree_mul_le _ _
      _ ≤ 0 + (intermediateNovelBasisX 𝔽q β h_ℓ_add_R_rate i ⟨j, by omega⟩).degree := by
          gcongr; exact degree_C_le
      _ ≤ ((⟨j, hj⟩ : Fin (2 ^ (ℓ - i))) : ℕ) := by
          rw [zero_add]
          refine le_trans (Polynomial.degree_le_natDegree) ?_
          exact_mod_cast natDegree_intermediateNovelBasisX_le 𝔽q β i ⟨j, hj⟩
      _ < ↑(2 ^ (ℓ - (i:ℕ))) := WithBot.coe_lt_coe.mpr hj

/-- New-API single-step `fold` equals the legacy `fold_legacy` at the canonical destination
index `⟨i+1, _⟩` (the `cast` collapses to `rfl`). -/
lemma fold_eq_fold_legacy (i : Fin r) (h_i : i.val + 1 < ℓ + 𝓡)
    (h_destIdx_le : (⟨i.val + 1, Nat.lt_trans h_i h_ℓ_add_R_rate⟩ : Fin r) ≤ ℓ)
    (f : (sDomain 𝔽q β h_ℓ_add_R_rate) i → L) (r_chal : L)
    (y : (sDomain 𝔽q β h_ℓ_add_R_rate) (⟨i.val + 1, Nat.lt_trans h_i h_ℓ_add_R_rate⟩)) :
    fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)
      (destIdx := ⟨i.val + 1, Nat.lt_trans h_i h_ℓ_add_R_rate⟩)
      (by simp) h_destIdx_le f r_chal y =
    fold_legacy 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (h_i := h_i) f r_chal y := by
  unfold fold
  simp only [cast_eq]

/-- **BCIKS Lemma 4.13 (general level), evaluation-function form.** -/
lemma iterated_fold_advances_aux (i steps : ℕ) (h : i + steps ≤ ℓ)
    (coeffs : Fin (2 ^ (ℓ - i)) → L) (rc : Fin steps → L)
    (y : (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨i + steps, by omega⟩) :
    iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨i, by omega⟩)
      (steps := steps) (destIdx := ⟨i + steps, by omega⟩)
      (h_destIdx := by simp) (h_destIdx_le := by simp; omega)
      (f := fun x => (intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩ coeffs).eval x.val)
      (r_challenges := rc) y
    = (intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate ⟨i + steps, by omega⟩
        (foldedNovelCoeffs i steps h coeffs rc)).eval y.val := by
  induction steps generalizing i coeffs with
  | zero =>
    rw [iterated_fold_zero_steps 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)]
    have hpoly : intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate ⟨i + 0, by omega⟩
          (foldedNovelCoeffs i 0 h coeffs rc)
        = intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩ coeffs := by
      congr 1
      funext j
      rw [foldedNovelCoeffs_zero]
      rfl
    rw [hpoly]
    congr 1
  | succ n ih =>
    have hℓr : ℓ < r := ℓ_lt_r (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    rw [iterated_fold_last 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := ⟨i, by omega⟩) (midIdx := ⟨i + n, by omega⟩) (destIdx := ⟨i + (n+1), by omega⟩)
      (steps := n) (h_midIdx := by simp) (h_destIdx := by simp; omega)
      (h_destIdx_le := by simp; omega)]
    -- Rewrite the inner n-fold via the induction hypothesis (as a function).
    have hinner : (iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨i, by omega⟩)
        (steps := n) (destIdx := ⟨i + n, by omega⟩) (h_destIdx := by simp)
        (h_destIdx_le := by simp; omega)
        (f := fun x => (intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩ coeffs).eval x.val)
        (r_challenges := Fin.init rc))
        = (fun y' => (intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate ⟨i + n, by omega⟩
            (foldedNovelCoeffs i n (by omega) coeffs (Fin.init rc))).eval y'.val) := by
      funext y'
      exact ih i (by omega) coeffs (Fin.init rc) y'
    rw [hinner]
    have h𝓡pos : 0 < 𝓡 := Nat.pos_of_neZero 𝓡
    have hin : i + n < ℓ := by omega
    -- Bridge new-API `fold` to legacy `fold_legacy` at level i+n.
    rw [fold_eq_fold_legacy 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨i + n, by omega⟩)
      (h_i := by simp only; omega)]
    -- Apply the proven single-step Lemma 4.13 (legacy form).
    rw [fold_advances_evaluation_poly_legacy 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := ⟨i + n, hin⟩) (h_i_succ_lt := by simp only; omega)
      (coeffs := foldedNovelCoeffs i n (by omega) coeffs (Fin.init rc))
      (r_chal := rc (Fin.last n))]
    have hf : (fun j : Fin (2 ^ (ℓ - (i + (n+1)))) =>
          (1 - rc (Fin.last n)) * foldedNovelCoeffs i n (by omega) coeffs (Fin.init rc)
            ⟨(j:ℕ) * 2, by
              have hj := j.isLt
              have he : ℓ - (i + n) = (ℓ - (i + (n + 1))) + 1 := by omega
              rw [he, pow_succ]; omega⟩ +
          rc (Fin.last n) * foldedNovelCoeffs i n (by omega) coeffs (Fin.init rc)
            ⟨(j:ℕ) * 2 + 1, by
              have hj := j.isLt
              have he : ℓ - (i + n) = (ℓ - (i + (n + 1))) + 1 := by omega
              rw [he, pow_succ]; omega⟩)
        = foldedNovelCoeffs i (n+1) h coeffs rc := by
      funext j
      rw [foldedNovelCoeffs_succ i n h coeffs rc j]
      have e1 : (⟨2 * (j:ℕ), by
            have hj := j.isLt
            have he : ℓ - (i + n) = (ℓ - (i + (n + 1))) + 1 := by omega
            rw [he, pow_succ]; omega⟩ : Fin (2 ^ (ℓ - (i + n))))
          = ⟨(j:ℕ) * 2, by
            have hj := j.isLt
            have he : ℓ - (i + n) = (ℓ - (i + (n + 1))) + 1 := by omega
            rw [he, pow_succ]; omega⟩ := by apply Fin.ext; simp only; ring
      have e2 : (⟨2 * (j:ℕ) + 1, by
            have hj := j.isLt
            have he : ℓ - (i + n) = (ℓ - (i + (n + 1))) + 1 := by omega
            rw [he, pow_succ]; omega⟩ : Fin (2 ^ (ℓ - (i + n))))
          = ⟨(j:ℕ) * 2 + 1, by
            have hj := j.isLt
            have he : ℓ - (i + n) = (ℓ - (i + (n + 1))) + 1 := by omega
            rw [he, pow_succ]; omega⟩ := by apply Fin.ext; simp only; ring
      rw [e1, e2]
    show eval (↑y) (intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate ⟨i + (n + 1), by omega⟩
        (fun j : Fin (2 ^ (ℓ - (i + (n+1)))) =>
          (1 - rc (Fin.last n)) * foldedNovelCoeffs i n (by omega) coeffs (Fin.init rc)
            ⟨(j:ℕ) * 2, by
              have hj := j.isLt
              have he : ℓ - (i + n) = (ℓ - (i + (n + 1))) + 1 := by omega
              rw [he, pow_succ]; omega⟩ +
          rc (Fin.last n) * foldedNovelCoeffs i n (by omega) coeffs (Fin.init rc)
            ⟨(j:ℕ) * 2 + 1, by
              have hj := j.isLt
              have he : ℓ - (i + n) = (ℓ - (i + (n + 1))) + 1 := by omega
              rw [he, pow_succ]; omega⟩)) = _
    rw [hf]


private lemma sDomain_cast_val {A B : Fin r} (h : (sDomain 𝔽q β h_ℓ_add_R_rate A : Type)
    = sDomain 𝔽q β h_ℓ_add_R_rate B) (hAB : A = B) (y : sDomain 𝔽q β h_ℓ_add_R_rate B) :
    ((cast h.symm y : sDomain 𝔽q β h_ℓ_add_R_rate A) : L) = (y : L) := by
  subst hAB; simp [cast_eq]

set_option maxHeartbeats 1000000 in
/-- **BCIKS-Binius Lemma 4.13 (general level `i`).** Iterating the fold `steps` times advances
the intermediate evaluation polynomial: the `steps`-fold of the codeword
`polyToOracleFunc i (intermediateEvaluationPoly ⟨i⟩ coeffs)` is the codeword
`polyToOracleFunc destIdx (intermediateEvaluationPoly ⟨destIdx⟩ (foldedNovelCoeffs …))`,
where the folded coefficients are the `multilinearWeight`-tensor combination of the originals. -/
lemma iterated_fold_advances_evaluation_poly (i : Fin r) (steps : Fin (ℓ + 1)) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps.val) (h_destIdx_le : destIdx ≤ ℓ)
    (coeffs : Fin (2 ^ (ℓ - i.val)) → L) (r_challenges : Fin steps.val → L) :
    iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := steps.val)
      (destIdx := destIdx) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
      (polyToOracleFunc 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (domainIdx := i)
        ⟨intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate ⟨i.val, by omega⟩ coeffs, by
          simpa [Polynomial.mem_degreeLT] using
            degree_intermediateEvaluationPoly_lt 𝔽q β ⟨i.val, by omega⟩ coeffs⟩)
      r_challenges
    = polyToOracleFunc 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (domainIdx := destIdx)
        ⟨intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate ⟨i.val + steps.val, by omega⟩
          (foldedNovelCoeffs i.val steps.val (by omega) coeffs r_challenges), by
          simpa [Polynomial.mem_degreeLT, ← h_destIdx] using
            degree_intermediateEvaluationPoly_lt 𝔽q β ⟨i.val + steps.val, by omega⟩
              (foldedNovelCoeffs i.val steps.val (by omega) coeffs r_challenges)⟩ := by
  funext y
  unfold polyToOracleFunc
  simp only
  have hi : (⟨i.val, by
      have hℓr : ℓ < r := ℓ_lt_r (h_ℓ_add_R_rate := h_ℓ_add_R_rate); omega⟩ : Fin r) = i :=
    Fin.ext rfl
  have key := iterated_fold_advances_aux 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := i.val) (steps := steps.val) (h := by omega) (coeffs := coeffs)
    (rc := r_challenges)
    (y := cast (by rw [show (⟨i.val + steps.val, by
        have hℓr : ℓ < r := ℓ_lt_r (h_ℓ_add_R_rate := h_ℓ_add_R_rate); omega⟩ : Fin r) = destIdx from
        Fin.ext h_destIdx.symm]) y)
  -- Transport `key` along `destIdx = ⟨i.val + steps.val, _⟩` and `i = ⟨i.val, _⟩`.
  have hdest : (⟨i.val + steps.val, by
      have hℓr : ℓ < r := ℓ_lt_r (h_ℓ_add_R_rate := h_ℓ_add_R_rate); omega⟩ : Fin r) = destIdx :=
    Fin.ext h_destIdx.symm
  rw [iterated_fold_congr_dest_index 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := ⟨i.val, by have hℓr : ℓ < r := ℓ_lt_r (h_ℓ_add_R_rate := h_ℓ_add_R_rate); omega⟩)
    (steps := steps.val) (destIdx := destIdx)
    (destIdx' := ⟨i.val + steps.val, by
      have hℓr : ℓ < r := ℓ_lt_r (h_ℓ_add_R_rate := h_ℓ_add_R_rate); omega⟩)
    (h_destIdx := by simp [h_destIdx]) (h_destIdx_le := h_destIdx_le)
    (h_destIdx_eq_destIdx' := hdest.symm)
    (f := fun x => eval (↑x) (intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate
      ⟨i.val, by have hℓr : ℓ < r := ℓ_lt_r (h_ℓ_add_R_rate := h_ℓ_add_R_rate); omega⟩ coeffs))
    (r_challenges := r_challenges) (y := y)]
  rw [key]
  congr 1
  -- `↑(cast h y) = ↑y`: the cast is between equal `sDomain` types, hence value-preserving.
  exact sDomain_cast_val 𝔽q β (h := by rw [show (⟨i.val + steps.val, by
      have hℓr : ℓ < r := ℓ_lt_r (h_ℓ_add_R_rate := h_ℓ_add_R_rate); omega⟩ : Fin r) = destIdx from
      Fin.ext h_destIdx.symm]) (hAB := Fin.ext h_destIdx.symm) (y := y)

end DegreeAndMain
end
end Binius.BinaryBasefold
