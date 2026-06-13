/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubJohnsonListSupply
import ArkLib.Data.CodingTheory.ProximityGap.JohnsonListBound
import ArkLib.Data.CodingTheory.ProximityGap.UniqueDecodingListBound

/-!
# `SubJohnsonListBound` is a THEOREM above the Johnson radius (#389)

The named residual `SubJohnsonListBound dom k m L A` (the open core of #389) is here
**proven unconditionally whenever the band threshold `k+m+1` sits at or above the
Johnson radius** `√(n·(k−1))` — i.e. when `n·(k−1) < (k+m+1)²`.  The proof is the
classical second-moment (Johnson) list bound, already in-tree
(`ArkLib.JohnsonList.johnson_list_bound_div`), fed the Reed–Solomon pairwise
agreement cap `k−1` (`agreement_card_le`):

  `#{codewords agreeing ≥ k+m+1 with w} ≤ n² / ((k+m+1)² − n(k−1))`.

This makes the residual's *name* a theorem: the open part of #389 is **strictly
sub-Johnson** (`(k+m+1)² ≤ n(k−1)`).  Composing with
`explainableCoreSupply_of_listBound`, the deep-band supply is fully proven in the
above-Johnson band, with `B = (n²/((k+m+1)²−n(k−1))) · C(n, k+m+1)`.

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`.
-/

open Finset Polynomial

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- Reed–Solomon pairwise agreement: two distinct codewords of `rsCode dom k`
(degree `< k`) agree on at most `k − 1` coordinates. -/
theorem rsCode_pairwise_agree_le (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k)
    {c c' : Fin n → F}
    (hc : c ∈ (rsCode dom k : Submodule F (Fin n → F)))
    (hc' : c' ∈ (rsCode dom k : Submodule F (Fin n → F)))
    (hne : c ≠ c') :
    (Finset.univ.filter (fun x => c x = c' x)).card ≤ k - 1 := by
  obtain ⟨P, hP, rfl⟩ := hc
  obtain ⟨Q, hQ, rfl⟩ := hc'
  have hPk : P.natDegree < k := by
    rcases eq_or_ne P 0 with rfl | hP0
    · simpa using hk
    · exact (Polynomial.natDegree_lt_iff_degree_lt hP0).mpr hP
  have hQk : Q.natDegree < k := by
    rcases eq_or_ne Q 0 with rfl | hQ0
    · simpa using hk
    · exact (Polynomial.natDegree_lt_iff_degree_lt hQ0).mpr hQ
  have hPQ : P ≠ Q := by
    intro h; exact hne (by rw [h])
  exact ArkLib.CodingTheory.UniqueDecoding.agreement_card_le (D := dom) hPk hQk hPQ

open Classical in
/-- **The residual is a theorem above the Johnson radius.**  When the band
threshold `k+m+1` lies at/above `√(n(k−1))` (`n·(k−1) < (k+m+1)²`), the sub-Johnson
list bound holds unconditionally with `L = n²/((k+m+1)²−n(k−1))` and the trivial cap
`A = n`.  Hence the open core of #389 is *strictly sub-Johnson*. -/
theorem subJohnsonListBound_aboveJohnson (dom : Fin n ↪ F) {k m : ℕ} (hk : 1 ≤ k)
    (hJohnson : n * (k - 1) < (k + m + 1) ^ 2) :
    SubJohnsonListBound dom k m
      (n ^ 2 / ((k + m + 1) ^ 2 - n * (k - 1))) n := by
  intro w
  refine ⟨?_, ?_⟩
  · -- the second-moment Johnson cap, instantiated
    have hcard : (bigAgreeCodewords dom k m w).card
        ≤ (Fintype.card (Fin n)) ^ 2
            / ((k + m + 1) ^ 2 - Fintype.card (Fin n) * (k - 1)) := by
      refine ArkLib.JohnsonList.johnson_list_bound_div w (bigAgreeCodewords dom k m w)
        (k + m + 1) (k - 1) ?_ ?_ ?_
      · intro c hc
        rw [bigAgreeCodewords, Finset.mem_filter] at hc
        simpa [listAgreeSet] using hc.2.2
      · intro c hc c' hc' hne
        rw [bigAgreeCodewords, Finset.mem_filter] at hc hc'
        exact rsCode_pairwise_agree_le dom hk hc.2.1 hc'.2.1 hne
      · simpa [Fintype.card_fin] using hJohnson
    simpa [Fintype.card_fin] using hcard
  · -- trivial agreement cap A = n
    intro c _
    rw [listAgreeSet]
    refine le_trans (Finset.card_filter_le _ _) ?_
    simp [Finset.card_univ]

open Classical in
/-- **The deep-band supply is fully proven above the Johnson radius.**  Composing the
discharged list bound with `explainableCoreSupply_of_listBound`: when
`n·(k−1) < (k+m+1)²`, the top-level `ExplainableCoreSupply` holds with
`B = (n²/((k+m+1)²−n(k−1))) · C(n, k+m+1)`, no open hypothesis. -/
theorem explainableCoreSupply_aboveJohnson (dom : Fin n ↪ F) {k m : ℕ} (hk : 1 ≤ k)
    (hJohnson : n * (k - 1) < (k + m + 1) ^ 2) :
    ExplainableCoreSupply dom k m
      ((n ^ 2 / ((k + m + 1) ^ 2 - n * (k - 1))) * (n.choose (k + m + 1))) :=
  explainableCoreSupply_of_listBound dom (subJohnsonListBound_aboveJohnson dom hk hJohnson)

/-- **Non-vacuity, concrete parameters.**  At `k = 2, m = 2, n = 16` the band
threshold `k+m+1 = 5` sits above the Johnson radius (`16·1 = 16 < 25 = 5²`), so the
deep-band supply is fully proven for *any* domain with the concrete bound
`B = (16²/(5²−16))·C(16,5) = 28·4368 = 122304`. -/
theorem explainableCoreSupply_concrete_k2m2n16 (dom : Fin 16 ↪ F) :
    ExplainableCoreSupply dom 2 2 122304 := by
  have h := explainableCoreSupply_aboveJohnson (k := 2) (m := 2) dom
    (by norm_num) (by norm_num)
  norm_num at h
  exact h

end ProximityGap.Ownership

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Ownership.rsCode_pairwise_agree_le
#print axioms ProximityGap.Ownership.subJohnsonListBound_aboveJohnson
#print axioms ProximityGap.Ownership.explainableCoreSupply_aboveJohnson
#print axioms ProximityGap.Ownership.explainableCoreSupply_concrete_k2m2n16
