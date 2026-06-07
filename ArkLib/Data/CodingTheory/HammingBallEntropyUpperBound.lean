/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.EntropyVolumeUpperBound
import ArkLib.Data.CodingTheory.QEntropyMonotone

/-!
# Hamming-ball volume entropy UPPER bound

Completes the two-sided `q`-ary entropy estimate on the Hamming-ball volume. The landed lower
bound `CodingTheory.hammingBallVolume_ge_qEntropy` gives `q^{n·H_q(δ)} ≤ (n+1)·Vol`; this file
adds the matching upper bound

  `Vol_q(δ,n) ≤ (n+1) · q^{n · H_q(⌊δn⌋/n)}`   (for `⌊δn⌋/n ≤ 1 − 1/q`),

so together `q^{n·H}/(n+1) ≤ Vol ≤ (n+1)·q^{n·H}`. Each binomial summand is bounded by
`q^{n·H(i/n)} ≤ q^{n·H(⌊δn⌋/n)}` (per-term upper bound `choose_pow_le_qEntropy` + entropy
monotonicity), then summed over the `≤ n+1` radii.

## Main result (`sorry`-free; axioms = `propext, Classical.choice, Quot.sound`)

* `hammingBallVolume_le_qEntropy`.
-/

namespace CodingTheory

open Real

variable {q : ℕ}

/-- **Hamming-ball volume entropy upper bound.** For `2 ≤ q`, `⌊δn⌋ < n`, and
`⌊δn⌋/n ≤ 1 − 1/q`, `Vol_q(δ,n) ≤ (n+1) · q^{n·H_q(⌊δn⌋/n)}`. -/
theorem hammingBallVolume_le_qEntropy (hq : 2 ≤ q) (δ : ℝ) (n : ℕ)
    (hkn : ⌊δ * (n : ℝ)⌋₊ < n)
    (hrange : (⌊δ * (n : ℝ)⌋₊ : ℝ) / (n : ℝ) ≤ 1 - 1 / (q : ℝ)) :
    (hammingBallVolume q δ n : ℝ)
      ≤ ((n : ℝ) + 1) * (q : ℝ) ^ ((n : ℝ) * qEntropy q ((⌊δ * (n : ℝ)⌋₊ : ℝ) / (n : ℝ))) := by
  classical
  set K : ℕ := ⌊δ * (n : ℝ)⌋₊ with hK
  set B : ℝ := (q : ℝ) ^ ((n : ℝ) * qEntropy q ((K : ℝ) / (n : ℝ))) with hB
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (show 1 ≤ q by omega)
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hn0 : 0 < n := lt_of_le_of_lt (Nat.zero_le K) hkn
  have hHnn : 0 ≤ qEntropy q ((K : ℝ) / (n : ℝ)) := by
    have := qEntropy_le_qEntropy_of_le hq (le_refl (0 : ℝ)) (by positivity) hrange
    rwa [qEntropy_zero] at this
  have hexpnn : 0 ≤ (n : ℝ) * qEntropy q ((K : ℝ) / (n : ℝ)) := by positivity
  have hBpos : 0 < B := by rw [hB]; exact Real.rpow_pos_of_pos hqpos _
  have hterm : ∀ i ∈ Finset.range (K + 1),
      ((Nat.choose n i * (q - 1) ^ i : ℕ) : ℝ) ≤ B := by
    intro i hi
    have hiK : i ≤ K := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hin : i < n := lt_of_le_of_lt hiK hkn
    have hcast : ((Nat.choose n i * (q - 1) ^ i : ℕ) : ℝ)
        = (Nat.choose n i : ℝ) * ((q : ℝ) - 1) ^ i := by
      push_cast [Nat.cast_sub (show 1 ≤ q by omega)]; ring
    rw [hcast]
    rcases Nat.eq_zero_or_pos i with hi0 | hipos
    · subst hi0
      simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, mul_one]
      rw [hB]; exact one_le_rpow hq1 hexpnn
    · have h1 := choose_pow_le_qEntropy hq n i hipos hin
      have hmono : qEntropy q ((i : ℝ) / (n : ℝ)) ≤ qEntropy q ((K : ℝ) / (n : ℝ)) := by
        refine qEntropy_le_qEntropy_of_le hq (by positivity) ?_ hrange
        gcongr
      have h2 : (q : ℝ) ^ ((n : ℝ) * qEntropy q ((i : ℝ) / (n : ℝ))) ≤ B := by
        rw [hB]
        exact rpow_le_rpow_of_exponent_le hq1 (by nlinarith [hmono, (by positivity : (0:ℝ) ≤ (n:ℝ))])
      exact le_trans h1 h2
  calc (hammingBallVolume q δ n : ℝ)
      = ∑ i ∈ Finset.range (K + 1), ((Nat.choose n i * (q - 1) ^ i : ℕ) : ℝ) := by
        rw [hammingBallVolume]; push_cast; rfl
    _ ≤ ∑ _i ∈ Finset.range (K + 1), B := Finset.sum_le_sum hterm
    _ = ((K : ℝ) + 1) * B := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
    _ ≤ ((n : ℝ) + 1) * B := by
        apply mul_le_mul_of_nonneg_right _ (le_of_lt hBpos)
        have : K + 1 ≤ n + 1 := by omega
        exact_mod_cast this

end CodingTheory

-- Axiom audit.
#print axioms CodingTheory.hammingBallVolume_le_qEntropy
