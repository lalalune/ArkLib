/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G169StepanovDoubleDeletionBound
import ArkLib.Data.CodingTheory.ProximityGap.QuadZeroSumEnergy
import ArkLib.Data.CodingTheory.ProximityGap.AutocorrelationMax
import ArkLib.Data.CodingTheory.ProximityGap.RepCountCosetConcentration

/-!
# G170: two-deletion additive-energy bound

Delete an ordered pair of distinct marks from each endpoint of a balanced depth-`t` core.  The
four deleted marks form a shifted additive-energy fiber, while the two reduced supports determine
the shift.  Translation of one mark identifies every shifted fiber with a subset of the ordinary
additive-energy quadruples.  This gives

`#cores * (t(t-1))^2 <= C(|G|,t-2)^2 * E_+(G)`.

Thus an `E_+(G) = O(|G|^(5/2))` HBK input would improve the census exponent to `2t-3/2`.
The currently formalized pointwise Stepanov input gives only the `8/3` energy scale and hence ties,
rather than improves, G169.  This file is an unconditional combinatorial consumer, not a claim of
the missing HBK estimate.

Issue #466.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G170TwoDeletionEnergyBound

open scoped BigOperators
open ArkLib.ProximityGap.AdditiveEnergyRepBound
open ArkLib.ProximityGap.AddEnergyGroupRepBound
open ArkLib.ProximityGap.AutocorrelationMax
open ArkLib.ProximityGap.Frontier.G145LowerDepthMultiplicityEnvelope

variable {F : Type*} [AddCommGroup F] [Fintype F] [DecidableEq F]

def distinctPairs (S : Finset F) : Finset (F × F) :=
  (S ×ˢ S).filter fun x => x.1 ≠ x.2

noncomputable def twiceMarkedCorePairs (G : Finset F) (t : ℕ) :
    Finset (Σ _c : Finset F × Finset F, (F × F) × (F × F)) :=
  (subsetCorePairs G t).sigma fun c => distinctPairs c.1 ×ˢ distinctPairs c.2

def erasePair (S : Finset F) (x : F × F) : Finset F :=
  (S.erase x.1).erase x.2

def shiftedEnergyQuads (G : Finset F) (c : F) : Finset ((F × F) × (F × F)) :=
  ((G ×ˢ G) ×ˢ (G ×ˢ G)).filter fun q =>
    q.1.1 + q.1.2 = q.2.1 + q.2.2 + c

noncomputable def twiceDeletionAmbient (G : Finset F) (t : ℕ) :
    Finset ((Finset F × Finset F) × ((F × F) × (F × F))) :=
  ((G.powersetCard (t - 2) ×ˢ G.powersetCard (t - 2)).sigma fun q =>
    shiftedEnergyQuads G ((∑ y ∈ q.2, y) - ∑ x ∈ q.1, x)) |>.image
      fun z => (z.1, z.2)

def twiceDeletionCode
    (z : Σ _c : Finset F × Finset F, (F × F) × (F × F)) :
    (Finset F × Finset F) × ((F × F) × (F × F)) :=
  ((erasePair z.1.1 z.2.1, erasePair z.1.2 z.2.2), z.2)

theorem distinctPairs_card (S : Finset F) :
    (distinctPairs S).card = S.card * (S.card - 1) := by
  classical
  rw [distinctPairs, Finset.card_filter, Finset.sum_product]
  calc
    (∑ x ∈ S, ∑ y ∈ S, if (x, y).1 ≠ (x, y).2 then 1 else 0) =
        ∑ _x ∈ S, (S.card - 1) := by
      apply Finset.sum_congr rfl
      intro x hx
      calc
        (∑ y ∈ S, if (x, y).1 ≠ (x, y).2 then 1 else 0) =
            (S.filter fun y => x ≠ y).card := by
          rw [Finset.card_filter]
        _ = (S.erase x).card := by
          congr 1
          ext y
          simp [eq_comm, and_comm]
        _ = S.card - 1 := Finset.card_erase_of_mem hx
    _ = S.card * (S.card - 1) := by simp

theorem twiceMarkedCorePairs_card (G : Finset F) (t : ℕ) :
    (twiceMarkedCorePairs G t).card =
      (subsetCorePairs G t).card * (t * (t - 1)) ^ 2 := by
  classical
  rw [twiceMarkedCorePairs, Finset.card_sigma]
  calc
    (∑ c ∈ subsetCorePairs G t,
        (distinctPairs c.1 ×ˢ distinctPairs c.2).card) =
        ∑ _c ∈ subsetCorePairs G t, (t * (t - 1)) ^ 2 := by
      apply Finset.sum_congr rfl
      intro c hc
      rw [Finset.card_product, distinctPairs_card, distinctPairs_card]
      have hL := (Finset.mem_powersetCard.mp (mem_subsetCorePairs_iff.mp hc).1).2
      have hR := (Finset.mem_powersetCard.mp (mem_subsetCorePairs_iff.mp hc).2.1).2
      rw [hL, hR]
      ring
    _ = (subsetCorePairs G t).card * (t * (t - 1)) ^ 2 := by simp

theorem shiftedEnergyQuads_card_eq (G : Finset F) (c : F) :
    (shiftedEnergyQuads G c).card =
      ∑ t : F, repCount G t * repCount G (t - c) := by
  classical
  unfold shiftedEnergyQuads
  change (((G ×ˢ G) ×ˢ (G ×ˢ G)).filter (fun q =>
    (fun p r => p.1 + p.2 = r.1 + r.2 + c) q.1 q.2)).card = _
  rw [Finset.card_filter, Finset.sum_product]
  simp_rw [← Finset.card_filter]
  change (∑ p ∈ G ×ˢ G,
    ((G ×ˢ G).filter fun q => p.1 + p.2 = q.1 + q.2 + c).card) = _
  have hmaps : ∀ p ∈ G ×ˢ G, p.1 + p.2 ∈ (Finset.univ : Finset F) := by simp
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  apply Finset.sum_congr rfl
  intro t _ht
  calc
    (∑ i ∈ (G ×ˢ G).filter (fun i => i.1 + i.2 = t),
        ((G ×ˢ G).filter fun q => i.1 + i.2 = q.1 + q.2 + c).card) =
        ∑ _i ∈ (G ×ˢ G).filter (fun i => i.1 + i.2 = t),
          repCount G (t - c) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mem_filter] at hi
      rw [hi.2]
      have hpair := repCount_add_eq_pairCard G (t - c) 0
      simp only [add_zero] at hpair
      rw [hpair]
      congr 1
      ext q
      simp only [Finset.mem_filter, Finset.mem_product]
      constructor
      · rintro ⟨hq, heq⟩
        exact ⟨hq, by rw [eq_sub_iff_add_eq]; exact heq.symm⟩
      · rintro ⟨hq, heq⟩
        exact ⟨hq, by rw [heq]; abel⟩
    _ = ((G ×ˢ G).filter (fun i => i.1 + i.2 = t)).card * repCount G (t - c) := by
      simp
    _ = repCount G t * repCount G (t - c) := by
      have hpair := repCount_add_eq_pairCard G t 0
      simp only [add_zero] at hpair
      rw [← hpair]

theorem shiftedEnergyQuads_card_le_energy (G : Finset F) (c : F) :
    (shiftedEnergyQuads G c).card ≤ additiveEnergy G := by
  classical
  rw [shiftedEnergyQuads_card_eq]
  have hauto := autocorr_le_autocorr_zero
    (fun t : F => (repCount G t : ℝ)) (fun _ => by positivity) c
  have hcast :
      (((∑ t : F, repCount G t * repCount G (t - c)) : ℕ) : ℝ) ≤
        (((∑ t : F, repCount G t ^ 2) : ℕ) : ℝ) := by
    exact_mod_cast hauto
  have hfull : ∑ t : F, repCount G t ^ 2 = additiveEnergy G := by
    have hzero := shiftedEnergyQuads_card_eq G 0
    simp only [sub_zero] at hzero
    simp only [pow_two]
    rw [← hzero]
    rw [additiveEnergy_eq_energyQuad]
    unfold shiftedEnergyQuads energyQuad
    congr 1
    ext q
    simp only [Finset.mem_filter, Finset.mem_product]
    constructor
    · rintro ⟨hq, heq⟩
      exact ⟨hq, by simpa using heq⟩
    · rintro ⟨hq, heq⟩
      exact ⟨hq, by simpa using heq⟩
  exact_mod_cast hcast.trans_eq (congrArg Nat.cast hfull)

theorem mem_twiceMarkedCorePairs_iff {G : Finset F} {t : ℕ}
    {z : Σ _c : Finset F × Finset F, (F × F) × (F × F)} :
    z ∈ twiceMarkedCorePairs G t ↔
      z.1 ∈ subsetCorePairs G t ∧
      z.2.1 ∈ distinctPairs z.1.1 ∧ z.2.2 ∈ distinctPairs z.1.2 := by
  classical
  simp [twiceMarkedCorePairs]

theorem erasePair_card {S : Finset F} {x : F × F}
    (hx : x ∈ distinctPairs S) : (erasePair S x).card = S.card - 2 := by
  rw [distinctPairs, Finset.mem_filter, Finset.mem_product] at hx
  unfold erasePair
  rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hx.2.symm, hx.1.2⟩),
    Finset.card_erase_of_mem hx.1.1]
  omega

theorem erasePair_subset (S : Finset F) (x : F × F) : erasePair S x ⊆ S :=
  (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)

theorem insert_pair_erasePair {S : Finset F} {x : F × F}
    (hx : x ∈ distinctPairs S) : insert x.1 (insert x.2 (erasePair S x)) = S := by
  rw [distinctPairs, Finset.mem_filter, Finset.mem_product] at hx
  unfold erasePair
  rw [Finset.insert_erase (Finset.mem_erase.mpr ⟨hx.2.symm, hx.1.2⟩),
    Finset.insert_erase hx.1.1]

theorem twiceDeletionCode_maps {G : Finset F} {t : ℕ}
    {z : Σ _c : Finset F × Finset F, (F × F) × (F × F)}
    (hz : z ∈ twiceMarkedCorePairs G t) :
    twiceDeletionCode z ∈ twiceDeletionAmbient G t := by
  classical
  rw [mem_twiceMarkedCorePairs_iff] at hz
  obtain ⟨hcore, hx, hy⟩ := hz
  rw [twiceDeletionAmbient, Finset.mem_image]
  let q : Finset F × Finset F := (erasePair z.1.1 z.2.1, erasePair z.1.2 z.2.2)
  refine ⟨⟨q, z.2⟩, ?_, rfl⟩
  rw [Finset.mem_sigma]
  refine ⟨?_, ?_⟩
  · rw [Finset.mem_product]
    constructor <;> rw [Finset.mem_powersetCard]
    · refine ⟨(erasePair_subset z.1.1 z.2.1).trans
          (Finset.mem_powersetCard.mp (mem_subsetCorePairs_iff.mp hcore).1).1, ?_⟩
      rw [erasePair_card hx,
        (Finset.mem_powersetCard.mp (mem_subsetCorePairs_iff.mp hcore).1).2]
    · refine ⟨(erasePair_subset z.1.2 z.2.2).trans
          (Finset.mem_powersetCard.mp (mem_subsetCorePairs_iff.mp hcore).2.1).1, ?_⟩
      rw [erasePair_card hy,
        (Finset.mem_powersetCard.mp (mem_subsetCorePairs_iff.mp hcore).2.1).2]
  · rw [shiftedEnergyQuads, Finset.mem_filter]
    refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
    · rw [distinctPairs, Finset.mem_filter, Finset.mem_product] at hx
      have hsub := (Finset.mem_powersetCard.mp (mem_subsetCorePairs_iff.mp hcore).1).1
      exact Finset.mem_product.mpr ⟨hsub hx.1.1, hsub hx.1.2⟩
    · rw [distinctPairs, Finset.mem_filter, Finset.mem_product] at hy
      have hsub := (Finset.mem_powersetCard.mp (mem_subsetCorePairs_iff.mp hcore).2.1).1
      exact Finset.mem_product.mpr ⟨hsub hy.1.1, hsub hy.1.2⟩
    · have hsum := (mem_subsetCorePairs_iff.mp hcore).2.2.2.1
      have hleft :
          (∑ a ∈ erasePair z.1.1 z.2.1, a) + z.2.1.1 + z.2.1.2 =
            ∑ a ∈ z.1.1, a := by
        unfold erasePair
        have hx' := hx
        rw [distinctPairs, Finset.mem_filter, Finset.mem_product] at hx'
        have h2 := Finset.sum_erase_add (z.1.1.erase z.2.1.1) (fun a : F => a)
          (Finset.mem_erase.mpr ⟨hx'.2.symm, hx'.1.2⟩)
        have h1 := Finset.sum_erase_add z.1.1 (fun a : F => a) hx'.1.1
        rw [← h1, ← h2]
        abel
      have hright :
          (∑ b ∈ erasePair z.1.2 z.2.2, b) + z.2.2.1 + z.2.2.2 =
            ∑ b ∈ z.1.2, b := by
        unfold erasePair
        have hy' := hy
        rw [distinctPairs, Finset.mem_filter, Finset.mem_product] at hy'
        have h2 := Finset.sum_erase_add (z.1.2.erase z.2.2.1) (fun b : F => b)
          (Finset.mem_erase.mpr ⟨hy'.2.symm, hy'.1.2⟩)
        have h1 := Finset.sum_erase_add z.1.2 (fun b : F => b) hy'.1.1
        rw [← h1, ← h2]
        abel
      dsimp [q]
      calc
        z.2.1.1 + z.2.1.2 =
            (∑ a ∈ z.1.1, a) - ∑ a ∈ erasePair z.1.1 z.2.1, a := by
          rw [← hleft]
          abel
        _ = (∑ b ∈ z.1.2, b) - ∑ a ∈ erasePair z.1.1 z.2.1, a := by
          rw [hsum]
        _ = z.2.2.1 + z.2.2.2 +
            ((∑ b ∈ erasePair z.1.2 z.2.2, b) -
              ∑ a ∈ erasePair z.1.1 z.2.1, a) := by
          rw [← hright]
          abel

theorem twiceDeletionCode_injOn (G : Finset F) (t : ℕ) :
    Set.InjOn twiceDeletionCode
      (↑(twiceMarkedCorePairs G t) :
        Set (Σ _c : Finset F × Finset F, (F × F) × (F × F))) := by
  intro z hz w hw hcode
  have hmarks : z.2 = w.2 := congrArg Prod.snd hcode
  have hred :
      (erasePair z.1.1 z.2.1, erasePair z.1.2 z.2.2) =
        (erasePair w.1.1 w.2.1, erasePair w.1.2 w.2.2) := congrArg Prod.fst hcode
  change z ∈ twiceMarkedCorePairs G t at hz
  change w ∈ twiceMarkedCorePairs G t at hw
  rw [mem_twiceMarkedCorePairs_iff] at hz hw
  have hredL : erasePair z.1.1 w.2.1 = erasePair w.1.1 w.2.1 := by
    have h := congrArg Prod.fst hred
    rw [hmarks] at h
    simpa using h
  have hredR : erasePair z.1.2 w.2.2 = erasePair w.1.2 w.2.2 := by
    have h := congrArg Prod.snd hred
    rw [hmarks] at h
    simpa using h
  have hL : z.1.1 = w.1.1 := by
    rw [← insert_pair_erasePair hz.2.1, ← insert_pair_erasePair hw.2.1,
      hmarks, hredL]
  have hR : z.1.2 = w.1.2 := by
    rw [← insert_pair_erasePair hz.2.2, ← insert_pair_erasePair hw.2.2,
      hmarks, hredR]
  apply Sigma.ext
  · exact Prod.ext hL hR
  · exact heq_of_eq hmarks

theorem twiceDeletionAmbient_card_le (G : Finset F) (t : ℕ) :
    (twiceDeletionAmbient G t).card ≤
      (G.card.choose (t - 2)) ^ 2 * additiveEnergy G := by
  classical
  unfold twiceDeletionAmbient
  calc
    (((G.powersetCard (t - 2) ×ˢ G.powersetCard (t - 2)).sigma fun q =>
        shiftedEnergyQuads G ((∑ y ∈ q.2, y) - ∑ x ∈ q.1, x)).image
          fun z => (z.1, z.2)).card ≤
        ((G.powersetCard (t - 2) ×ˢ G.powersetCard (t - 2)).sigma fun q =>
          shiftedEnergyQuads G ((∑ y ∈ q.2, y) - ∑ x ∈ q.1, x)).card :=
      Finset.card_image_le
    _ = ∑ q ∈ G.powersetCard (t - 2) ×ˢ G.powersetCard (t - 2),
        (shiftedEnergyQuads G ((∑ y ∈ q.2, y) - ∑ x ∈ q.1, x)).card := by
      rw [Finset.card_sigma]
    _ ≤ ∑ _q ∈ G.powersetCard (t - 2) ×ˢ G.powersetCard (t - 2),
        additiveEnergy G := by
      apply Finset.sum_le_sum
      intro q _hq
      exact shiftedEnergyQuads_card_le_energy G _
    _ = (G.card.choose (t - 2)) ^ 2 * additiveEnergy G := by
      simp [Finset.card_product, Finset.card_powersetCard, pow_two]

/-- **G170 capstone.** Two ordered deletions on each side charge the complete balanced-core
census to one shifted additive-energy fiber. -/
theorem subsetCorePairs_mul_pair_marks_sq_le_choose_sq_mul_energy
    (G : Finset F) (t : ℕ) :
    (subsetCorePairs G t).card * (t * (t - 1)) ^ 2 ≤
      (G.card.choose (t - 2)) ^ 2 * additiveEnergy G := by
  rw [← twiceMarkedCorePairs_card]
  exact (Finset.card_le_card_of_injOn twiceDeletionCode
    (fun _ hz => twiceDeletionCode_maps hz) (twiceDeletionCode_injOn G t)).trans
      (twiceDeletionAmbient_card_le G t)

theorem primitiveCorePairs_mul_pair_marks_sq_le_choose_sq_mul_energy
    (G : Finset F) (t : ℕ) :
    (ArkLib.ProximityGap.Frontier.G152DepthFourCompositeCensus.primitiveCorePairs G t).card *
        (t * (t - 1)) ^ 2 ≤
      (G.card.choose (t - 2)) ^ 2 * additiveEnergy G := by
  classical
  exact (Nat.mul_le_mul_right ((t * (t - 1)) ^ 2)
    (Finset.card_le_card (Finset.filter_subset _ _))).trans
      (subsetCorePairs_mul_pair_marks_sq_le_choose_sq_mul_energy G t)

#print axioms distinctPairs_card
#print axioms twiceMarkedCorePairs_card
#print axioms shiftedEnergyQuads_card_le_energy
#print axioms twiceDeletionCode_injOn
#print axioms twiceDeletionAmbient_card_le
#print axioms subsetCorePairs_mul_pair_marks_sq_le_choose_sq_mul_energy
#print axioms primitiveCorePairs_mul_pair_marks_sq_le_choose_sq_mul_energy

end ArkLib.ProximityGap.Frontier.G170TwoDeletionEnergyBound
