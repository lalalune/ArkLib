/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G172SubsetSumToREnergy

/-!
# G173: all-depth deletion bound by `rEnergy`

Mark an `r`-subset on each endpoint of a balanced depth-`t` core and delete both marked subsets.
The reduced supports have size `t-r`; their sum difference forces the two marked subsets into one
shifted subset-sum fiber.  G172 bounds that fiber by `rEnergy G r`.

The code is injective because the stored marked subsets and reduced supports reconstruct both
original supports by union.  Its exact marked-domain multiplicity is `choose(t,r)^2`, giving

`#cores * choose(t,r)^2 <= choose(|G|,t-r)^2 * rEnergy(G,r)`.

Issue #466.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G173AllDepthDeletionREnergy

open scoped BigOperators
open ArkLib.ProximityGap.Frontier.G145LowerDepthMultiplicityEnvelope
open ArkLib.ProximityGap.Frontier.G172SubsetSumToREnergy
open ArkLib.ProximityGap.SubgroupGaussSumMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

noncomputable def rMarkedCorePairs (G : Finset F) (t r : ℕ) :
    Finset (Σ _c : Finset F × Finset F, Finset F × Finset F) :=
  (subsetCorePairs G t).sigma fun c => c.1.powersetCard r ×ˢ c.2.powersetCard r

noncomputable def rDeletionAmbient (G : Finset F) (t r : ℕ) :
    Finset ((Finset F × Finset F) × (Finset F × Finset F)) :=
  ((G.powersetCard (t - r) ×ˢ G.powersetCard (t - r)).sigma fun q =>
    shiftedSubsetSumPairs G r ((∑ y ∈ q.2, y) - ∑ x ∈ q.1, x)) |>.image
      fun z => (z.1, z.2)

def rDeletionCode
    (z : Σ _c : Finset F × Finset F, Finset F × Finset F) :
    (Finset F × Finset F) × (Finset F × Finset F) :=
  ((z.1.1 \ z.2.1, z.1.2 \ z.2.2), z.2)

theorem mem_rMarkedCorePairs_iff {G : Finset F} {t r : ℕ}
    {z : Σ _c : Finset F × Finset F, Finset F × Finset F} :
    z ∈ rMarkedCorePairs G t r ↔
      z.1 ∈ subsetCorePairs G t ∧
      z.2.1 ∈ z.1.1.powersetCard r ∧ z.2.2 ∈ z.1.2.powersetCard r := by
  classical
  simp [rMarkedCorePairs]

theorem rMarkedCorePairs_card (G : Finset F) (t r : ℕ) :
    (rMarkedCorePairs G t r).card =
      (subsetCorePairs G t).card * (t.choose r) ^ 2 := by
  classical
  rw [rMarkedCorePairs, Finset.card_sigma]
  calc
    (∑ c ∈ subsetCorePairs G t,
        (c.1.powersetCard r ×ˢ c.2.powersetCard r).card) =
        ∑ _c ∈ subsetCorePairs G t, (t.choose r) ^ 2 := by
      apply Finset.sum_congr rfl
      intro c hc
      rw [Finset.card_product, Finset.card_powersetCard, Finset.card_powersetCard]
      have hL := (Finset.mem_powersetCard.mp (mem_subsetCorePairs_iff.mp hc).1).2
      have hR := (Finset.mem_powersetCard.mp (mem_subsetCorePairs_iff.mp hc).2.1).2
      rw [hL, hR, pow_two]
    _ = (subsetCorePairs G t).card * (t.choose r) ^ 2 := by simp

theorem sdiff_union_of_subset {A X : Finset F} (hXA : X ⊆ A) : A \ X ∪ X = A := by
  exact Finset.sdiff_union_of_subset hXA

theorem rDeletionCode_maps {G : Finset F} {t r : ℕ}
    {z : Σ _c : Finset F × Finset F, Finset F × Finset F}
    (hz : z ∈ rMarkedCorePairs G t r) : rDeletionCode z ∈ rDeletionAmbient G t r := by
  classical
  rw [mem_rMarkedCorePairs_iff] at hz
  obtain ⟨hcore, hX, hY⟩ := hz
  rw [rDeletionAmbient, Finset.mem_image]
  let q : Finset F × Finset F := (z.1.1 \ z.2.1, z.1.2 \ z.2.2)
  refine ⟨⟨q, z.2⟩, ?_, rfl⟩
  rw [Finset.mem_sigma]
  refine ⟨?_, ?_⟩
  · rw [Finset.mem_product]
    have hXm := Finset.mem_powersetCard.mp hX
    have hYm := Finset.mem_powersetCard.mp hY
    constructor <;> rw [Finset.mem_powersetCard]
    · refine ⟨(Finset.sdiff_subset).trans
          (Finset.mem_powersetCard.mp (mem_subsetCorePairs_iff.mp hcore).1).1, ?_⟩
      rw [Finset.card_sdiff_of_subset hXm.1,
        (Finset.mem_powersetCard.mp (mem_subsetCorePairs_iff.mp hcore).1).2, hXm.2]
    · refine ⟨(Finset.sdiff_subset).trans
          (Finset.mem_powersetCard.mp (mem_subsetCorePairs_iff.mp hcore).2.1).1, ?_⟩
      rw [Finset.card_sdiff_of_subset hYm.1,
        (Finset.mem_powersetCard.mp (mem_subsetCorePairs_iff.mp hcore).2.1).2, hYm.2]
  · rw [shiftedSubsetSumPairs, Finset.mem_filter, Finset.mem_product]
    have hXm := Finset.mem_powersetCard.mp hX
    have hYm := Finset.mem_powersetCard.mp hY
    have hGL := (Finset.mem_powersetCard.mp (mem_subsetCorePairs_iff.mp hcore).1).1
    have hGR := (Finset.mem_powersetCard.mp (mem_subsetCorePairs_iff.mp hcore).2.1).1
    refine ⟨⟨Finset.mem_powersetCard.mpr ⟨hXm.1.trans hGL, hXm.2⟩,
      Finset.mem_powersetCard.mpr ⟨hYm.1.trans hGR, hYm.2⟩⟩, ?_⟩
    have hsum := (mem_subsetCorePairs_iff.mp hcore).2.2.2.1
    have hleft := Finset.sum_sdiff hXm.1 (f := fun x : F => x)
    have hright := Finset.sum_sdiff hYm.1 (f := fun x : F => x)
    dsimp [q]
    calc
      (∑ x ∈ z.2.1, x) =
          (∑ x ∈ z.1.1, x) - ∑ x ∈ z.1.1 \ z.2.1, x := by
        rw [← hleft]
        abel
      _ = (∑ x ∈ z.1.2, x) - ∑ x ∈ z.1.1 \ z.2.1, x := by rw [hsum]
      _ = (∑ y ∈ z.2.2, y) +
          ((∑ y ∈ z.1.2 \ z.2.2, y) - ∑ x ∈ z.1.1 \ z.2.1, x) := by
        rw [← hright]
        abel

theorem rDeletionCode_injOn (G : Finset F) (t r : ℕ) :
    Set.InjOn rDeletionCode
      (↑(rMarkedCorePairs G t r) :
        Set (Σ _c : Finset F × Finset F, Finset F × Finset F)) := by
  intro z hz w hw hcode
  change z ∈ rMarkedCorePairs G t r at hz
  change w ∈ rMarkedCorePairs G t r at hw
  rw [mem_rMarkedCorePairs_iff] at hz hw
  have hmarks : z.2 = w.2 := congrArg Prod.snd hcode
  have hred := congrArg Prod.fst hcode
  change (z.1.1 \ z.2.1, z.1.2 \ z.2.2) =
    (w.1.1 \ w.2.1, w.1.2 \ w.2.2) at hred
  rw [hmarks] at hred
  have hredL : z.1.1 \ w.2.1 = w.1.1 \ w.2.1 := by
    exact congrArg Prod.fst hred
  have hredR : z.1.2 \ w.2.2 = w.1.2 \ w.2.2 := by
    exact congrArg Prod.snd hred
  have hL : z.1.1 = w.1.1 := by
    rw [← sdiff_union_of_subset (Finset.mem_powersetCard.mp hz.2.1).1,
      ← sdiff_union_of_subset (Finset.mem_powersetCard.mp hw.2.1).1, hmarks, hredL]
  have hR : z.1.2 = w.1.2 := by
    rw [← sdiff_union_of_subset (Finset.mem_powersetCard.mp hz.2.2).1,
      ← sdiff_union_of_subset (Finset.mem_powersetCard.mp hw.2.2).1, hmarks, hredR]
  apply Sigma.ext
  · exact Prod.ext hL hR
  · exact heq_of_eq hmarks

theorem rDeletionAmbient_card_le (G : Finset F) (t r : ℕ) :
    (rDeletionAmbient G t r).card ≤
      (G.card.choose (t - r)) ^ 2 * rEnergy G r := by
  classical
  unfold rDeletionAmbient
  calc
    _ ≤ ((G.powersetCard (t - r) ×ˢ G.powersetCard (t - r)).sigma fun q =>
        shiftedSubsetSumPairs G r ((∑ y ∈ q.2, y) - ∑ x ∈ q.1, x)).card :=
      Finset.card_image_le
    _ = ∑ q ∈ G.powersetCard (t - r) ×ˢ G.powersetCard (t - r),
        (shiftedSubsetSumPairs G r ((∑ y ∈ q.2, y) - ∑ x ∈ q.1, x)).card := by
      rw [Finset.card_sigma]
    _ ≤ ∑ _q ∈ G.powersetCard (t - r) ×ˢ G.powersetCard (t - r),
        rEnergy G r := by
      apply Finset.sum_le_sum
      intro q _hq
      exact shiftedSubsetSumPairs_card_le_rEnergy G r _
    _ = (G.card.choose (t - r)) ^ 2 * rEnergy G r := by
      simp [Finset.card_product, Finset.card_powersetCard, pow_two]

/-- **G173 all-depth capstone.** -/
theorem subsetCorePairs_mul_choose_sq_le_choose_sq_mul_rEnergy
    (G : Finset F) (t r : ℕ) :
    (subsetCorePairs G t).card * (t.choose r) ^ 2 ≤
      (G.card.choose (t - r)) ^ 2 * rEnergy G r := by
  rw [← rMarkedCorePairs_card]
  exact (Finset.card_le_card_of_injOn rDeletionCode
    (fun _ hz => rDeletionCode_maps hz) (rDeletionCode_injOn G t r)).trans
      (rDeletionAmbient_card_le G t r)

theorem primitiveCorePairs_mul_choose_sq_le_choose_sq_mul_rEnergy
    (G : Finset F) (t r : ℕ) :
    (ArkLib.ProximityGap.Frontier.G152DepthFourCompositeCensus.primitiveCorePairs G t).card *
        (t.choose r) ^ 2 ≤ (G.card.choose (t - r)) ^ 2 * rEnergy G r := by
  classical
  exact (Nat.mul_le_mul_right ((t.choose r) ^ 2)
    (Finset.card_le_card (Finset.filter_subset _ _))).trans
      (subsetCorePairs_mul_choose_sq_le_choose_sq_mul_rEnergy G t r)

#print axioms rMarkedCorePairs_card
#print axioms rDeletionCode_injOn
#print axioms rDeletionAmbient_card_le
#print axioms subsetCorePairs_mul_choose_sq_le_choose_sq_mul_rEnergy
#print axioms primitiveCorePairs_mul_choose_sq_le_choose_sq_mul_rEnergy

end ArkLib.ProximityGap.Frontier.G173AllDepthDeletionREnergy
