/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CS25BallIntersectionBound

/-!
# CS25 #82, deliverable 2 (b): the off-support weight budget for ball intersections

The triangle cutoff `jointCoverCount_eq_zero_of_lt` records only that `B(0,δ) ∩ B(e,δ)` is *empty*
once `wt(e) > 2r` (`r = ⌊δ·n⌋`).  This file proves the quantitative refinement that drives the
ball-intersection **decay** in `wt(e)`: every `w` in the intersection has its weight *off* the
support of `e` budgeted by

  `2 · offWt(w) + wt(e) ≤ 2r`,    `offWt(w) := #{i : e i = 0 ∧ w i ≠ 0}`.

As `wt(e)` grows toward `2r`, the off-support budget `(2r − wt(e))/2` shrinks to `0`, forcing `w` to
live almost entirely on `supp(e)`.  This is the structural mechanism behind the CS25 second-moment
off-diagonal estimate (cf. `CS25BallIntersectionWeightInvariant` for the weight-enumerator collapse).

## Main results

* `two_mul_offSupport_add_hammingNorm_le` — the pointwise budget `2·offWt(w) + wt(e) ≤ wt(w)+Δ₀(w,e)`.
* `offSupport_budget_of_mem_jointCover` — its specialization to joint-cover members: `≤ 2r`.
* `jointCoverCount_le_offSupport_card` — the resulting `jointCoverCount` upper bound by the
  off-support–budgeted set, the entry point to the explicit `q^{wt e}·V_{n−wt e}` decay bound.
-/

open scoped BigOperators ENNReal NNReal

namespace ArkLib.CS25

open Code Finset

set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type*} [Fintype F] [DecidableEq F] [AddCommGroup F]

/-- **Off-support weight budget (pointwise).** For any `w, e`, twice the weight of `w` *off* the
support of `e` plus the weight of `e` is at most `wt(w) + Δ₀(w,e)`.  Coordinatewise: off `supp(e)`,
both `wt(w)` and `Δ₀(w,e)` see the same coordinate (so it is counted twice on the left exactly when
`w` is nonzero there); on `supp(e)`, at least one of `wt(w)`, `Δ₀(w,e)` fires (`e i ≠ 0` forbids
`w i = 0 = e i` simultaneously), covering the single `wt(e)` count. -/
theorem two_mul_offSupport_add_hammingNorm_le (w e : ι → F) :
    2 * (univ.filter (fun i => e i = 0 ∧ w i ≠ 0)).card + hammingNorm e
      ≤ hammingNorm w + hammingDist w e := by
  classical
  have hwN : hammingNorm w = ∑ i, (if w i ≠ 0 then (1 : ℕ) else 0) := by
    rw [hammingNorm, Finset.card_filter]
  have hd : hammingDist w e = ∑ i, (if w i ≠ e i then (1 : ℕ) else 0) := by
    rw [hammingDist, Finset.card_filter]
  have heN : hammingNorm e = ∑ i, (if e i ≠ 0 then (1 : ℕ) else 0) := by
    rw [hammingNorm, Finset.card_filter]
  have ha : (univ.filter (fun i => e i = 0 ∧ w i ≠ 0)).card
      = ∑ i, (if (e i = 0 ∧ w i ≠ 0) then (1 : ℕ) else 0) := by
    rw [Finset.card_filter]
  rw [hwN, hd, heN, ha, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum (fun i _ => ?_)
  by_cases he : e i = 0 <;> by_cases hw : w i = 0 <;> by_cases hwe : w i = e i <;> simp_all

/-- **Quantitative budget for joint-cover members.** Any `w` in `B(0,δ) ∩ B(e,δ)` (Hamming radius
`r = ⌊δ·n⌋`) has its weight *off* `supp(e)` budgeted: `2·offWt(w) + wt(e) ≤ 2r`.  In particular
`offWt(w) ≤ (2r − wt(e))/2`, a quantitative strengthening of the triangle cutoff
`jointCoverCount_eq_zero_of_lt`. -/
theorem offSupport_budget_of_mem_jointCover (δ : ℝ≥0) (e w : ι → F)
    (hw0 : (relHammingDist w 0 : ENNReal) ≤ (δ : ENNReal))
    (hwe : (relHammingDist w e : ENNReal) ≤ (δ : ENNReal)) :
    2 * (univ.filter (fun i => e i = 0 ∧ w i ≠ 0)).card + hammingNorm e
      ≤ 2 * ⌊(δ : ℝ) * (Fintype.card ι : ℝ)⌋₊ := by
  have h1 : hammingDist w 0 ≤ ⌊(δ : ℝ) * (Fintype.card ι : ℝ)⌋₊ :=
    (rHD_le_iff_hammingDist_le w 0 δ).mp hw0
  have h2 : hammingDist w e ≤ ⌊(δ : ℝ) * (Fintype.card ι : ℝ)⌋₊ :=
    (rHD_le_iff_hammingDist_le w e δ).mp hwe
  have hbudget := two_mul_offSupport_add_hammingNorm_le w e
  rw [hammingDist_zero_right] at h1
  omega

/-- **Joint cover bounded by the off-support–budgeted set.** The `δ`-ball intersection
`I(e) = jointCoverCount δ 0 e` is at most the number of words whose weight off `supp(e)` is at most
`(2r − wt(e))/2`.  This isolates the decay: the bounding set's size is `q^{wt(e)} · V_{n−wt(e)}(B')`
(`B' = (2r − wt(e))/2`), so it shrinks as `wt(e) → 2r`. -/
theorem jointCoverCount_le_offSupport_card (δ : ℝ≥0) (e : ι → F) :
    jointCoverCount δ 0 e
      ≤ (univ.filter (fun w : ι → F =>
          (univ.filter (fun i => e i = 0 ∧ w i ≠ 0)).card
            ≤ (2 * ⌊(δ : ℝ) * (Fintype.card ι : ℝ)⌋₊ - hammingNorm e) / 2)).card := by
  classical
  unfold jointCoverCount
  apply Finset.card_le_card
  intro w hw
  rw [Finset.mem_filter] at hw ⊢
  obtain ⟨_, hw0, hwe⟩ := hw
  refine ⟨Finset.mem_univ _, ?_⟩
  have := offSupport_budget_of_mem_jointCover δ e w hw0 hwe
  omega

end ArkLib.CS25
