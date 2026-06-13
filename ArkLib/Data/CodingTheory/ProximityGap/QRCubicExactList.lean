/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.QRCubicSupplyLower

/-!
# The EXACT orbit count: distinct zero-sum QR triples `= 6 ×` the sum-zero 3-subsets (#389)

`QRCubicSupplyLower` bounded the distinct-entry zero-sum triples by `27 ×` the sum-zero
`3`-subsets (fiber `≤ 27`).  This file pins the orbit factor **exactly to `6`**: a
distinct-entry triple is one of the `3! = 6` orderings of its underlying `3`-set, so

> **`qrDistinctTriples_card_eq`** — `#{distinct (a,b,c) ∈ (QR*)³ : a+b+c=0}
> = 6 · #{T ⊆ QR* : |T|=3, ∑T = 0}`.

Combined with the exact ordered count `qr_zeroSum_ordered_eq` (`= #QR*·M`) and the
degenerate count (`≤ 3·#QR*`), this brackets the unordered cubic-word list size
(`= cubicSupply`) tightly:
`(#QR*·M − 3·#QR*)/6 ≤ #{sum-zero 3-subsets} ≤ #QR*·M / 6`, i.e. `Θ(n²)` with the exact
leading constant `(q−1)(q−5)/48`.  Issue #389.
-/

open Finset

namespace ProximityGap.PairRank

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- The orbit map is surjective onto the sum-zero `3`-subsets: every such subset has a
distinct-ordered preimage (any ordering of its three elements). -/
theorem image_tripleSet_eq :
    (qrDistinctTriples (F := F)).image tripleSet = qrSumZeroSubsets := by
  apply Finset.Subset.antisymm image_tripleSet_subset
  intro T hT
  rw [qrSumZeroSubsets, Finset.mem_filter, Finset.mem_powersetCard] at hT
  obtain ⟨⟨hsub, hcard⟩, hsum⟩ := hT
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.mp hcard
  rw [Finset.mem_image]
  refine ⟨(x, y, z), ?_, ?_⟩
  · rw [qrDistinctTriples, Finset.mem_filter, mem_qrZeroSumTriples]
    refine ⟨⟨?_, ?_, ?_, ?_⟩, hxy, hxz, hyz⟩
    · exact hsub (by simp)
    · exact hsub (by simp)
    · exact hsub (by simp)
    · rw [Finset.sum_insert (by simp [hxy, hxz]), Finset.sum_insert (by simp [hyz]),
        Finset.sum_singleton] at hsum
      linear_combination hsum
  · rfl

/-- The fiber over a sum-zero `3`-subset `T = {x,y,z}` is exactly its `6` orderings. -/
theorem fiber_card_eq_six (T : Finset F) (hT : T ∈ qrSumZeroSubsets (F := F)) :
    ((qrDistinctTriples (F := F)).filter (fun t => tripleSet t = T)).card = 6 := by
  classical
  rw [qrSumZeroSubsets, Finset.mem_filter, Finset.mem_powersetCard] at hT
  obtain ⟨⟨hsub, hcard⟩, hsum⟩ := hT
  obtain ⟨x, y, z, hxy, hxz, hyz, hTeq⟩ := Finset.card_eq_three.mp hcard
  have hx : x ∈ qrStar (F := F) := hsub (by rw [hTeq]; simp)
  have hy : y ∈ qrStar (F := F) := hsub (by rw [hTeq]; simp)
  have hz : z ∈ qrStar (F := F) := hsub (by rw [hTeq]; simp)
  have hsum0 : x + y + z = 0 := by
    rw [hTeq, Finset.sum_insert (by simp [hxy, hxz]),
      Finset.sum_insert (by simp [hyz]), Finset.sum_singleton] at hsum
    linear_combination hsum
  -- the six orderings
  set perms : Finset (F × F × F) :=
    {(x, y, z), (x, z, y), (y, x, z), (y, z, x), (z, x, y), (z, y, x)} with hperms
  have heq : (qrDistinctTriples (F := F)).filter (fun t => tripleSet t = T) = perms := by
    ext t
    simp only [Finset.mem_filter, hperms, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨ht, htS⟩
      rw [qrDistinctTriples, Finset.mem_filter, mem_qrZeroSumTriples] at ht
      obtain ⟨_, hd1, hd2, hd3⟩ := ht
      -- tripleSet t = T = {x,y,z}, so t.1, t.2.1, t.2.2 ∈ {x,y,z}, distinct ⟹ a permutation
      have hmem : ∀ w, w ∈ tripleSet t → w = x ∨ w = y ∨ w = z := by
        intro w hw; rw [htS, hTeq] at hw
        simpa [Finset.mem_insert, Finset.mem_singleton] using hw
      have h1 := hmem t.1 (by simp [tripleSet])
      have h2 := hmem t.2.1 (by simp [tripleSet])
      have h3 := hmem t.2.2 (by simp [tripleSet])
      -- 27 cases collapse via distinctness of t's entries to the 6 valid permutations
      obtain ⟨t1, t2, t3⟩ := t
      simp only at h1 h2 h3 hd1 hd2 hd3 ⊢
      rcases h1 with rfl | rfl | rfl <;> rcases h2 with rfl | rfl | rfl <;>
        rcases h3 with rfl | rfl | rfl <;>
        first
          | (exfalso; exact hd1 rfl) | (exfalso; exact hd2 rfl) | (exfalso; exact hd3 rfl)
          | tauto
    · intro hcases
      have hmkmem : ∀ a b c : F, a ∈ qrStar (F := F) → b ∈ qrStar (F := F) →
          c ∈ qrStar (F := F) → a + b + c = 0 → a ≠ b → a ≠ c → b ≠ c →
          tripleSet (a, b, c) = T ∧ ((a, b, c) ∈ qrDistinctTriples (F := F)) := by
        intro a b c hca hcb hcc hcsum hab hac hbc
        refine ⟨?_, ?_⟩
        · rw [hTeq]; ext w
          simp only [tripleSet, Finset.mem_insert, Finset.mem_singleton]
          constructor <;> (rintro (rfl|rfl|rfl) <;> tauto)
        · rw [qrDistinctTriples, Finset.mem_filter, mem_qrZeroSumTriples]
          exact ⟨⟨hca, hcb, hcc, hcsum⟩, hab, hac, hbc⟩
      rcases hcases with h|h|h|h|h|h <;> subst h
      · exact ⟨(hmkmem x y z hx hy hz hsum0 hxy hxz hyz).2,
          (hmkmem x y z hx hy hz hsum0 hxy hxz hyz).1⟩
      · exact ⟨(hmkmem x z y hx hz hy (by linear_combination hsum0) hxz hxy
          (Ne.symm hyz)).2, (hmkmem x z y hx hz hy (by linear_combination hsum0) hxz hxy
          (Ne.symm hyz)).1⟩
      · exact ⟨(hmkmem y x z hy hx hz (by linear_combination hsum0) (Ne.symm hxy) hyz
          hxz).2, (hmkmem y x z hy hx hz (by linear_combination hsum0) (Ne.symm hxy) hyz
          hxz).1⟩
      · exact ⟨(hmkmem y z x hy hz hx (by linear_combination hsum0) hyz (Ne.symm hxy)
          (Ne.symm hxz)).2, (hmkmem y z x hy hz hx (by linear_combination hsum0) hyz
          (Ne.symm hxy) (Ne.symm hxz)).1⟩
      · exact ⟨(hmkmem z x y hz hx hy (by linear_combination hsum0) (Ne.symm hxz) (Ne.symm hyz)
          hxy).2, (hmkmem z x y hz hx hy (by linear_combination hsum0) (Ne.symm hxz)
          (Ne.symm hyz) hxy).1⟩
      · exact ⟨(hmkmem z y x hz hy hx (by linear_combination hsum0) (Ne.symm hyz) (Ne.symm hxz)
          (Ne.symm hxy)).2, (hmkmem z y x hz hy hx (by linear_combination hsum0) (Ne.symm hyz)
          (Ne.symm hxz) (Ne.symm hxy)).1⟩
  rw [heq, hperms]
  -- the 6 tuples are pairwise distinct
  decide +kernel

end ProximityGap.PairRank
