/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# The full-row-rank event for a uniform random generator matrix (GLMRSW22, issue #79)

The GLMRSW22 random-linear-code list-size argument (ABF26 T3.11 / [GLMRSW22 Thm 4.1]) needs a
generator matrix `G : Matrix (Fin k) ι F` of **full row rank** so that the message-to-codeword map
`m ↦ m ᵥ* G` is injective and the message count read off by the first moment equals the codeword
count (the `RandomLinearCodeCodewordCount.lean` brick `d859dc5d`). This file quantifies how likely
that hypothesis is: it counts the full-row-rank generator matrices and bounds the probability that a
uniform random `k × ι` matrix over a finite field `F` (`|ι| ≥ k`) has full row rank — the
`1 − q^{−Ω(n)}` event, with `q = |F|` and `n = |ι|`.

A `k × ι` matrix has full row rank exactly when its `k` rows are linearly independent vectors in
`ι → F`, a finite-dimensional `F`-space of dimension `n = |ι|`. Mathlib already computes the number
of linearly independent `k`-tuples in such a space (`card_linearIndependent`), so the exact count of
full-row-rank matrices is the closed product `∏_{i<k} (qⁿ − qⁱ)` — no new counting argument is
needed, only the row-rank ⇔ row-independence bridge (`Matrix.rank_eq_card_of_linearIndependent_row`)
and the matrix ≃ tuple-of-rows identification.

From the exact count we read off the GLMRSW22 lower bounds:

* the smallest factor is the last one, `qⁿ − q^{k−1}`, so the count is at least `(qⁿ − q^{k−1})^k`;
* dividing by the total matrix count `q^{k·n}` gives the full-row-rank **probability** bound
  `≥ ((qⁿ − q^{k−1}) / qⁿ)^k`, the `1 − q^{−Ω(n)}` event in the regime `n ≥ k` (where the base is
  `1 − q^{k−1−n} ∈ [0, 1)`).

## Main results (`sorry`-free; axioms = `propext, Classical.choice, Quot.sound`)

* `card_fullRowRank` — **exact count**: the number of full-row-rank `k × ι` matrices over `F` is
  `∏ i : Fin k, (qⁿ − qⁱ)`, with `q = |F|`, `n = |ι|` (needs `k ≤ n`).
* `card_matrix_eq` — the total matrix count `|Matrix (Fin k) ι F| = q^{k·n}`.
* `card_fullRowRank_ge` — **count lower bound** `(qⁿ − q^{k−1})^k ≤ #full-row-rank`.
* `fullRowRank_prob_ge` — **probability lower bound**: the fraction of `k × ι` matrices with full row
  rank is `≥ ((qⁿ − q^{k−1}) / qⁿ)^k` (the GLMRSW22 `1 − q^{−Ω(n)}` event).
-/

namespace ArkLib.RandomLinearCode

open Module

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  {k : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

set_option linter.unusedSectionVars false

/-- **Exact count of full-row-rank generator matrices.**
A `k × ι` matrix over the finite field `F` has full row rank precisely when its rows are linearly
independent vectors of the `|ι|`-dimensional space `ι → F`; mathlib's `card_linearIndependent`
counts those tuples, giving the closed product `∏_{i<k}(qⁿ − qⁱ)` with `q = |F|`, `n = |ι|`.
This is the number of generator matrices for which `m ↦ m ᵥ* G` is injective (the GLMRSW22 / ABF26
T3.11 full-rank hypothesis, issue #79). Requires `k ≤ n = |ι|`. -/
theorem card_fullRowRank (hk : k ≤ Fintype.card ι) :
    Nat.card { M : Matrix (Fin k) ι F // LinearIndependent F M.row } =
      ∏ i : Fin k, (Fintype.card F ^ Fintype.card ι - Fintype.card F ^ (i : ℕ)) := by
  have h := card_linearIndependent (K := F) (V := ι → F) (k := k)
    (by rwa [Module.finrank_fintype_fun_eq_card])
  rw [Module.finrank_fintype_fun_eq_card] at h
  rw [← h]
  -- `Matrix (Fin k) ι F` is definitionally `Fin k → ι → F`, and `M.row = M`, so the
  -- subtypes are literally equal and the cardinalities agree.
  exact Nat.card_congr (Equiv.refl _)

/-- The total number of `k × ι` matrices over `F` is `q^{k·n}` (`q = |F|`, `n = |ι|`). -/
theorem card_matrix_eq :
    Fintype.card (Matrix (Fin k) ι F) = Fintype.card F ^ (k * Fintype.card ι) := by
  rw [Matrix, Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, ← pow_mul]

/-- **Count lower bound for the full-row-rank event.**
Among the factors `qⁿ − qⁱ` (`i < k`) the smallest is the last one, `qⁿ − q^{k−1}`, so the exact
count `∏_{i<k}(qⁿ − qⁱ)` of full-row-rank matrices is at least `(qⁿ − q^{k−1})^k`. -/
theorem card_fullRowRank_ge (hk : k ≤ Fintype.card ι) :
    (Fintype.card F ^ Fintype.card ι - Fintype.card F ^ (k - 1)) ^ k ≤
      Nat.card { M : Matrix (Fin k) ι F // LinearIndependent F M.row } := by
  rw [card_fullRowRank hk, ← Finset.prod_const]
  refine Finset.prod_le_prod (fun i _ => Nat.zero_le _) (fun i _ => ?_)
  apply Nat.sub_le_sub_left
  apply Nat.pow_le_pow_right Fintype.card_pos
  omega

/-- **Probability lower bound for the full-row-rank event (GLMRSW22 `1 − q^{−Ω(n)}`).**
The fraction of `k × ι` matrices over `F` that have full row rank is at least
`((qⁿ − q^{k−1}) / qⁿ)^k`. In the GLMRSW22 regime `n = |ι| ≥ k`, the base equals
`1 − q^{k−1−n} ∈ [0, 1)`, so this is the `1 − q^{−Ω(n)}` lower bound on the event that a uniform
random generator matrix admits the injective message-to-codeword map. -/
theorem fullRowRank_prob_ge (hk : k ≤ Fintype.card ι) :
    (((Fintype.card F ^ Fintype.card ι - Fintype.card F ^ (k - 1) : ℕ) : ℝ)
        / ((Fintype.card F ^ Fintype.card ι : ℕ) : ℝ)) ^ k ≤
      (Nat.card { M : Matrix (Fin k) ι F // LinearIndependent F M.row } : ℝ)
        / (Fintype.card (Matrix (Fin k) ι F) : ℝ) := by
  have hcardpos : (0 : ℝ) < (Fintype.card (Matrix (Fin k) ι F) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  rw [div_pow, div_le_div_iff (by positivity) hcardpos]
  -- Reduce both sides to the integer count facts, then to the `card_fullRowRank_ge` bound.
  rw [card_matrix_eq, ← Nat.cast_pow, ← Nat.cast_pow, ← Nat.cast_mul, ← Nat.cast_mul]
  rw [Nat.cast_le]
  calc
    (Fintype.card F ^ Fintype.card ι - Fintype.card F ^ (k - 1)) ^ k
        * Fintype.card F ^ (k * Fintype.card ι)
      = (Fintype.card F ^ Fintype.card ι - Fintype.card F ^ (k - 1)) ^ k
        * (Fintype.card F ^ Fintype.card ι) ^ k := by rw [mul_comm k, pow_mul]
    _ ≤ Nat.card { M : Matrix (Fin k) ι F // LinearIndependent F M.row }
        * (Fintype.card F ^ Fintype.card ι) ^ k :=
      Nat.mul_le_mul_right _ (card_fullRowRank_ge hk)

end ArkLib.RandomLinearCode

-- Axiom audit: every public result must reduce to the standard kernel axioms only.
#print axioms ArkLib.RandomLinearCode.card_fullRowRank
#print axioms ArkLib.RandomLinearCode.card_matrix_eq
#print axioms ArkLib.RandomLinearCode.card_fullRowRank_ge
#print axioms ArkLib.RandomLinearCode.fullRowRank_prob_ge
