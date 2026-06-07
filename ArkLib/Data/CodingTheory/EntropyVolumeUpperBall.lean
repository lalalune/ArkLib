/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.EntropyVolumeUpper
import ArkLib.Data.CodingTheory.QEntropyMonotone
import ArkLib.Data.CodingTheory.HammingBallVolume

/-!
# q-ary Hamming-ball volume UPPER bound (sub-capacity)

The matching upper bound to `hammingBallVolume_ge_qEntropy` (`EntropyVolumeBound.lean`): in the
sub-capacity regime `⌊δn⌋/n ≤ 1 − 1/q`,

  `Vol_q(δ, n) ≤ (n + 1) · q^{n·H_q(⌊δn⌋/n)}`.

Together with the `/(n+1)` lower bound this brackets `Vol_q(δ,n)` within a `(n+1)²` factor of
`q^{n·H_q(⌊δn⌋/n)}` — the standard entropy-volume estimate (elementary `/(n+1)` form, no Stirling).

Proof: each summand `C(n,i)·(q-1)^i` of the volume is `≤ q^{n·H_q(i/n)}` (the per-term upper bound
`choose_pow_le_qEntropy`) and `H_q(i/n) ≤ H_q(⌊δn⌋/n)` since `i/n ≤ ⌊δn⌋/n ≤ 1 − 1/q` lies below the
entropy's capacity peak (`qEntropy_le_qEntropy_of_le`); there are `⌊δn⌋+1 ≤ n+1` summands.
`sorry`/`axiom`-free, axiom-clean.
-/

namespace CodingTheory

open Real Finset

variable {q : ℕ}

/-- **q-ary Hamming-ball volume UPPER bound (sub-capacity).**  For `2 ≤ q` and `δ` whose mode index
`r := ⌊δn⌋` satisfies `r < n` and `r/n ≤ 1 − 1/q`:

  `Vol_q(δ, n) ≤ (n + 1) · q^{n·H_q(r/n)}`. -/
theorem hammingBallVolume_le_qEntropy (hq : 2 ≤ q) (δ : ℝ) {n : ℕ}
    (hr : ⌊δ * (n : ℝ)⌋₊ < n)
    (hcap : (⌊δ * (n : ℝ)⌋₊ : ℝ) / (n : ℝ) ≤ 1 - 1 / (q : ℝ)) :
    (hammingBallVolume q δ n : ℝ)
      ≤ ((n : ℝ) + 1)
        * (q : ℝ) ^ ((n : ℝ) * qEntropy q ((⌊δ * (n : ℝ)⌋₊ : ℝ) / (n : ℝ))) := by
  set r := ⌊δ * (n : ℝ)⌋₊ with hrdef
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le r) hr
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (show 1 ≤ q by omega)
  have hqcast : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ q)]; norm_num
  have hrn_nn : (0 : ℝ) ≤ (r : ℝ) / (n : ℝ) := by positivity
  have hrn_le1 : (r : ℝ) / (n : ℝ) ≤ 1 := by
    have hpos : (0 : ℝ) < 1 / (q : ℝ) := by positivity
    linarith [hcap]
  have hH_nn : 0 ≤ qEntropy q ((r : ℝ) / (n : ℝ)) :=
    (qEntropy_nonneg_and_basic hq hrn_nn hrn_le1).1
  set B := (q : ℝ) ^ ((n : ℝ) * qEntropy q ((r : ℝ) / (n : ℝ))) with hBdef
  have hB_ge_one : (1 : ℝ) ≤ B := by
    rw [hBdef]
    calc (1 : ℝ) = (q : ℝ) ^ (0 : ℝ) := (Real.rpow_zero _).symm
      _ ≤ (q : ℝ) ^ ((n : ℝ) * qEntropy q ((r : ℝ) / (n : ℝ))) :=
          Real.rpow_le_rpow_of_exponent_le hq1 (by positivity)
  -- Each volume summand is `≤ B`.
  have hterm : ∀ i ∈ Finset.range (r + 1),
      ((Nat.choose n i * (q - 1) ^ i : ℕ) : ℝ) ≤ B := by
    intro i hi
    rw [Finset.mem_range, Nat.lt_succ_iff] at hi
    have hin : i < n := lt_of_le_of_lt hi hr
    rcases Nat.eq_zero_or_pos i with hi0 | hipos
    · subst hi0
      simpa using hB_ge_one
    · have hcast_i : ((Nat.choose n i * (q - 1) ^ i : ℕ) : ℝ)
          = (Nat.choose n i : ℝ) * ((q : ℝ) - 1) ^ i := by push_cast [hqcast]; ring
      rw [hcast_i]
      refine le_trans (choose_pow_le_qEntropy hq n i hipos hin) ?_
      rw [hBdef]
      refine Real.rpow_le_rpow_of_exponent_le hq1 ?_
      refine mul_le_mul_of_nonneg_left ?_ hnR.le
      refine qEntropy_le_qEntropy_of_le hq (by positivity) ?_ hcap
      exact (div_le_div_iff_of_pos_right hnR).mpr (by exact_mod_cast hi)
  -- Sum the per-term bounds.
  have hvol_eq : (hammingBallVolume q δ n : ℝ)
      = ∑ i ∈ Finset.range (r + 1), ((Nat.choose n i * (q - 1) ^ i : ℕ) : ℝ) := by
    unfold hammingBallVolume
    rw [← hrdef, Nat.cast_sum]
  rw [hvol_eq]
  calc ∑ i ∈ Finset.range (r + 1), ((Nat.choose n i * (q - 1) ^ i : ℕ) : ℝ)
      ≤ ∑ _i ∈ Finset.range (r + 1), B := Finset.sum_le_sum hterm
    _ = ((r : ℝ) + 1) * B := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
    _ ≤ ((n : ℝ) + 1) * B := by
        have hrn : (r : ℝ) ≤ (n : ℝ) := by exact_mod_cast (le_of_lt hr)
        have hB0 : (0 : ℝ) ≤ B := le_trans zero_le_one hB_ge_one
        nlinarith [hrn, hB0]

end CodingTheory

-- Axiom audit: depends on exactly `[propext, Classical.choice, Quot.sound]`.
#print axioms CodingTheory.hammingBallVolume_le_qEntropy
