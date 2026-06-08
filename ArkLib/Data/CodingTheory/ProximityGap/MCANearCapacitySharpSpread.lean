/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCANearCapacityQuadratic

/-!
# The sharp maximal near-capacity MCA spread on the arithmetic domain (Proximity Prize, #232)

`MCANearCapacityQuadratic.lean` realized a quadratic `Θ(k(n-k))` witness spread, but only a *sub*-range
of the `(k+1)`-subset sums (its single-tail staircase has gaps near the top, and it needs `n ≥ 2k+1`).
This file proves the **exact maximal** arithmetic-domain spread promised in
`MCANearCapacityGeneralRate.lean`'s docstring:

`ε_mca(C, 1-(k+1)/n) ≥ ((k+1)(n-k-1) + 1) / |F|`  for every `1 ≤ k < n`,

the largest spread any `(k+1)`-window family on the arithmetic node set `{0,…,n-1}` can give, because
the set of `(k+1)`-subset sums of `{0,…,n-1}` is *exactly* the contiguous integer interval `[T, T']`
with `T = 0+1+⋯+k` and `T' = (n-k-1)+⋯+(n-1)`, of size `T'-T+1 = (k+1)(n-k-1)+1`.

## The construction (water-filling / complement gaps)

A `(k+1)`-subset `{a₀<⋯<a_k} ⊆ {0,…,n-1}` is encoded by its **gaps** `c_j = a_j - j ∈ {0,…,m}`
(`m = n-1-k`), a weakly-increasing sequence, with `∑aⱼ = T + ∑cⱼ`. Conversely, every offset
`s ∈ [0, (k+1)m]` is realized by the *water-filled* gap profile

`c_j = min m (max 0 (s - (k-j)·m))`  (pour `s` units into `k+1` columns of height `m`, top-first),

whose total is exactly `s` (`gapProfile_sum`, via the water-filling identity `waterfill_sum`). Setting
`a_j = c_j + j` gives a strictly increasing window (`aProfile_strictMono`) of `k+1` nodes `< n`, with
node-sum `T + s`. The `(k+1)m + 1` windows for `s = 0,…,(k+1)m` have distinct sums, hence (feeding
`MCANearCapacityGK.epsMCA_ge_of_window_family`) distinct bad scalars, giving the sharp bound.

## What this does and does not do (candidate analysis for #232)

* It is the **tight** arithmetic-domain realization — no `(k+1)`-window family on `{0,…,n-1}` beats
  `(k+1)(n-k-1)+1`, since that is the full subset-sum interval length. Removes the `n ≥ 2k+1`
  restriction of the staircase: holds for every `1 ≤ k < n`.
* It is still `O(n²)/|F| < ε* = 2⁻¹²⁸` for the prize's large fields, so it does **not** pin `δ*`
  (which needs an *exponential* spread). It is the ceiling of the *single-line, single-domain* method;
  the open prize lives beyond it (multiplicity / Guruswami–Sudan).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
  Tracking issue #232 / #141.
-/

open Polynomial BigOperators
open scoped NNReal ENNReal

namespace ProximityGap.MCANearCapacitySharpSpread

open ProximityGap Code ProximityGap.MCANearCapacityGK ProximityGap.MCANearCapacityQuadratic

/-! ## The water-filling identity -/

/-- **Water-filling.** Pouring `s` units of water into `K` columns of height `m` (top-first, each
column `i` receiving `min m (max 0 (s - i·m))`) holds `min s (K·m)` units in total. -/
theorem waterfill_sum (m s : ℕ) :
    ∀ K, (∑ i ∈ Finset.range K, min m (max 0 (s - i * m))) = min s (K * m) := by
  intro K
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, ih]
    rcases Nat.le_or_lt s (K * m) with hsKm | hsKm
    · have h1 : min s (K * m) = s := by omega
      have h2 : s - K * m = 0 := by omega
      have h3 : min s ((K + 1) * m) = s := by
        have : K * m ≤ (K + 1) * m := Nat.mul_le_mul_right _ (by omega)
        omega
      rw [h1, h2, h3]; simp
    · have h1 : min s (K * m) = K * m := by omega
      rcases Nat.le_or_lt ((K + 1) * m) s with hs1 | hs1
      · have hge : m ≤ s - K * m := by
          have : (K + 1) * m = K * m + m := by ring
          omega
        have h2 : min m (max 0 (s - K * m)) = m := by omega
        have h3 : min s ((K + 1) * m) = (K + 1) * m := by omega
        rw [h1, h2, h3]; ring
      · have hlt : s - K * m < m := by
          have : (K + 1) * m = K * m + m := by ring
          omega
        have h2 : min m (max 0 (s - K * m)) = s - K * m := by omega
        have h3 : min s ((K + 1) * m) = s := by omega
        rw [h1, h2, h3]; omega

/-! ## The gap profile and window for a given offset -/

variable {p : ℕ} [Fact p.Prime] {n k : ℕ} [NeZero n]

/-- The water-filled gap of node `j` (`0 ≤ j ≤ k`) for total offset `s`, into columns of height
`m = n-1-k`. -/
def gap (m k s j : ℕ) : ℕ := min m (max 0 (s - (k - j) * m))

/-- The window node `aⱼ = cⱼ + j`. -/
def aNode (m k s j : ℕ) : ℕ := gap m k s j + j

/-- The gap profile sums to the offset `s`, provided `s ≤ (k+1)·m`. -/
theorem gapProfile_sum (m k s : ℕ) (hs : s ≤ (k + 1) * m) :
    (∑ j ∈ Finset.range (k + 1), gap m k s j) = s := by
  have hreflect :
      (∑ j ∈ Finset.range (k + 1), min m (max 0 (s - (k - j) * m)))
        = ∑ i ∈ Finset.range (k + 1), min m (max 0 (s - i * m)) := by
    rw [← Finset.sum_range_reflect (fun i => min m (max 0 (s - i * m))) (k + 1)]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    congr 2
    omega
  rw [gap]
  simp only
  rw [hreflect, waterfill_sum m s (k + 1)]
  omega

/-- The gap profile is weakly increasing in `j`. -/
theorem gap_mono (m k s : ℕ) {j j' : ℕ} (hj : j ≤ j') (hj'k : j' ≤ k) :
    gap m k s j ≤ gap m k s j' := by
  rw [gap, gap]
  have hsub : (k - j') * m ≤ (k - j) * m := Nat.mul_le_mul_right _ (by omega)
  omega

/-- The window nodes are strictly increasing, hence injective. -/
theorem aNode_strictMono (m k s : ℕ) {j j' : ℕ} (hj : j < j') (hj'k : j' ≤ k) :
    aNode m k s j < aNode m k s j' := by
  have hmono : gap m k s j ≤ gap m k s j' := gap_mono m k s (by omega) hj'k
  rw [aNode, aNode]; omega

end ProximityGap.MCANearCapacitySharpSpread
