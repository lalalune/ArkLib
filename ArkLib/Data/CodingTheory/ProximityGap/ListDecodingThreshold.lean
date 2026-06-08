/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.ListSizeMoments

/-!
# The unique-decoding endpoint of `δ*` (direction A for #232)

`ListSizeMoments.exists_two_of_second_gt_first` gives the *upper* (ambiguity) side of the list
threshold: when the second moment exceeds the first, some received word has `|Λ| ≥ 2`. This file pins
the *lower* (unique) side **exactly** via the triangle inequality:

* `pairBall_eq_zero` — the pair-ball count `N(v,r) = 0` whenever `wt(v) > 2r` (two balls of radius `r`
  centred `wt(v)` apart cannot meet). So in `second_moment_linear = |C|·Σ_{v∈C} N(v,r)`, every nonzero
  codeword beyond weight `2r` contributes nothing.
* `list_le_one_of_min_weight` — if the minimum distance exceeds `2r` (i.e. `r < d/2`), then **every**
  decoding list has size `≤ 1`: unique decoding holds below half the minimum distance.

Together with the ambiguity criterion, this brackets `δ*`: list size is `≤ 1` for `2r < d` and becomes
`≥ 2` once the second moment crosses the first — the unique→list transition sits at half the minimum
distance, recovered here purely from the metric (no FTA/Johnson root bound).
-/

namespace ArkLib.CodingTheory.ListMoments

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Fintype F] [DecidableEq F] [AddCommGroup F]

/-- **The pair-ball vanishes beyond weight `2r`.** No vector `g` is within Hamming distance `r` of
both `0` and `v` when `wt(v) > 2r`: by the triangle inequality `wt(v) = d(0,v) ≤ d(0,g) + d(v,g) ≤ 2r`,
a contradiction. Hence `N(v,r) = 0`. -/
theorem pairBall_eq_zero (v : ι → F) (r : ℕ) (hv : 2 * r < hammingNorm v) :
    (Finset.univ.filter
        (fun g => hammingDist (0 : ι → F) g ≤ r ∧ hammingDist v g ≤ r)).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro g - ⟨h1, h2⟩
  have htri : hammingDist (0 : ι → F) v ≤ hammingDist (0 : ι → F) g + hammingDist g v :=
    hammingDist_triangle _ _ _
  have hd0v : hammingDist (0 : ι → F) v = hammingNorm v := by rw [hammingDist_zero_left]
  rw [hd0v, hammingDist_comm g v] at htri
  omega

/-- **Unique decoding below half the minimum distance.** If every nonzero codeword has weight `> 2r`
(equivalently the minimum distance `d > 2r`, i.e. `r < d/2`), then every decoding list `Λ(C,r,f)` has
size at most `1`. Proof: two distinct codewords `c, c'` within `r` of the same `f` would satisfy
`wt(c-c') = d(c,c') ≤ d(c,f) + d(c',f) ≤ 2r`, contradicting the minimum-weight bound (`c-c'` is a
nonzero codeword by linearity). -/
theorem list_le_one_of_min_weight {C : Finset (ι → F)}
    (hsub : ∀ a ∈ C, ∀ b ∈ C, a - b ∈ C) (r : ℕ)
    (hmin : ∀ v ∈ C, v ≠ 0 → 2 * r < hammingNorm v) (f : ι → F) :
    (lam C r f).card ≤ 1 := by
  by_contra hgt
  rw [not_le] at hgt
  obtain ⟨c, hc, c', hc', hne⟩ := Finset.one_lt_card.mp hgt
  rw [lam, Finset.mem_filter] at hc hc'
  have hv : c' - c ∈ C := hsub c' hc'.1 c hc.1
  have hvne : c' - c ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have hwt : 2 * r < hammingNorm (-c + c') := by
    have hdiff : (-c + c') = c' - c := by
      ext i
      simp [sub_eq_add_neg, add_comm]
    simpa [hdiff] using hmin _ hv hvne
  have hd : hammingDist c c' = hammingNorm (c - c') := by
    have h := hammingDist_add_right (c - c') (0 : ι → F) c'
    rw [sub_add_cancel, zero_add, hammingDist_zero_right] at h
    exact h
  have htri : hammingDist c c' ≤ hammingDist c f + hammingDist f c' :=
    hammingDist_triangle _ _ _
  rw [hd, hammingDist_comm f c'] at htri
  omega

#print axioms pairBall_eq_zero
#print axioms list_le_one_of_min_weight

end ArkLib.CodingTheory.ListMoments
