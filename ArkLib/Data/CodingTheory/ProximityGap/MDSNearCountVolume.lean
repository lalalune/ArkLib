/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.HammingBallVolume

/-!
# MDS near-codeword count as a Hamming-ball volume (toward T4.17 far half, #82)

The RS near-codeword bound (`rs_near_codeword_count_le`) and the covered-fraction entropy bound
(`rs_covered_fraction_entropy`) carry the counting sum `∑_{d≤R} C(n,d)·q^d`. The genuine analytic
obstruction for the far/coverage half of the CS25 breakdown band inequality is bounding this sum by
a qEntropy exponential. This file supplies the bridge: the sum is *exactly* a Hamming-ball volume
over the alphabet `q+1`,

  `∑_{d≤R} C(n,d)·q^d = hammingBallVolume(q+1, R/n, n)`,

since `hammingBallVolume Q δ n = ∑_{i≤⌊δn⌋} C(n,i)·(Q−1)^i` with `Q = q+1`, `(Q−1) = q`, and
`⌊(R/n)·n⌋ = R`. Composing with `hammingBallVolume_le_qEntropy_real_radius` then bounds the near
count by `(n+1)·(q+1)^{n·H_{q+1}(R/n)}` — the missing input that turns the coverage *lower* bound
into the far *upper* bound `#{far}` small on the breakdown sub-band.
-/

namespace CodingTheory

/-- **MDS near-count sum = `(q+1)`-ary Hamming-ball volume.**
`∑_{d≤R} C(n,d)·q^d = hammingBallVolume(q+1, R/n, n)`. -/
theorem sum_choose_mul_pow_eq_hammingBallVolume (q n R : ℕ) (hn : 0 < n) :
    ∑ d ∈ Finset.range (R + 1), n.choose d * q ^ d
      = hammingBallVolume (q + 1) ((R : ℝ) / (n : ℝ)) n := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  unfold hammingBallVolume
  have heq : (R : ℝ) / (n : ℝ) * (n : ℝ) = (R : ℝ) := by field_simp
  have hfloor : ⌊(R : ℝ) / (n : ℝ) * (n : ℝ)⌋₊ = R := by rw [heq, Nat.floor_natCast]
  rw [hfloor]
  simp [Nat.add_sub_cancel]

end CodingTheory
