/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G167MinimalZeroSumDeletionBound
import Mathlib.Data.Finset.Sigma

/-!
# G168: double marked deletion bound for all balanced cores

Mark one element `x` on the left and `y` on the right of an equal-sum depth-`t` core, then delete
both.  The reduced supports and the left mark determine the right mark from

`sum(S\{x}) + x = sum(T\{y}) + y`.

Thus doubly marked cores inject into two `(t-1)`-subsets and one free element of `G`, yielding

`#subsetCorePairs(G,t) * t^2 ≤ C(|G|,t-1)^2 * |G|`.

Unlike G167, this controls the complete core census, including the generic free four-orbit sector.
It is an unconditional one-ambient-power saving, though not yet the square-root/BGK-scale gain.

Issue #466.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G168DoubleDeletionCoreBound

open scoped BigOperators
open ArkLib.ProximityGap.Frontier.G145LowerDepthMultiplicityEnvelope

variable {F : Type*} [AddCommGroup F] [Fintype F] [DecidableEq F]

noncomputable def doublyMarkedCorePairs (G : Finset F) (t : ℕ) :
    Finset (Σ _c : Finset F × Finset F, F × F) :=
  (subsetCorePairs G t).sigma fun c => c.1 ×ˢ c.2

def doubleDeletionCode (z : Σ _c : Finset F × Finset F, F × F) :
    (Finset F × Finset F) × F :=
  ((z.1.1.erase z.2.1, z.1.2.erase z.2.2), z.2.1)

def doubleDeletionAmbient (G : Finset F) (t : ℕ) :
    Finset ((Finset F × Finset F) × F) :=
  (G.powersetCard (t - 1) ×ˢ G.powersetCard (t - 1)) ×ˢ G

theorem mem_doublyMarkedCorePairs_iff {G : Finset F} {t : ℕ}
    {z : Σ _c : Finset F × Finset F, F × F} :
    z ∈ doublyMarkedCorePairs G t ↔
      z.1 ∈ subsetCorePairs G t ∧ z.2.1 ∈ z.1.1 ∧ z.2.2 ∈ z.1.2 := by
  classical
  simp [doublyMarkedCorePairs]

theorem doubleDeletionCode_maps {G : Finset F} {t : ℕ}
    {z : Σ _c : Finset F × Finset F, F × F}
    (hz : z ∈ doublyMarkedCorePairs G t) :
    doubleDeletionCode z ∈ doubleDeletionAmbient G t := by
  rw [mem_doublyMarkedCorePairs_iff] at hz
  obtain ⟨hzCore, hzx, hzy⟩ := hz
  rw [doubleDeletionAmbient, Finset.mem_product]
  refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
  · rw [Finset.mem_powersetCard]
    refine ⟨(Finset.erase_subset _ _).trans
      (Finset.mem_powersetCard.mp (mem_subsetCorePairs_iff.mp hzCore).1).1, ?_⟩
    change (z.1.1.erase z.2.1).card = t - 1
    rw [Finset.card_erase_of_mem hzx,
      (Finset.mem_powersetCard.mp (mem_subsetCorePairs_iff.mp hzCore).1).2]
  · rw [Finset.mem_powersetCard]
    refine ⟨(Finset.erase_subset _ _).trans
      (Finset.mem_powersetCard.mp (mem_subsetCorePairs_iff.mp hzCore).2.1).1, ?_⟩
    change (z.1.2.erase z.2.2).card = t - 1
    rw [Finset.card_erase_of_mem hzy,
      (Finset.mem_powersetCard.mp (mem_subsetCorePairs_iff.mp hzCore).2.1).2]
  · exact (Finset.mem_powersetCard.mp (mem_subsetCorePairs_iff.mp hzCore).1).1 hzx

theorem marked_core_sum_identity {G : Finset F} {t : ℕ}
    {z : Σ _c : Finset F × Finset F, F × F}
    (hz : z ∈ doublyMarkedCorePairs G t) :
    (∑ a ∈ z.1.1.erase z.2.1, a) + z.2.1 =
      (∑ b ∈ z.1.2.erase z.2.2, b) + z.2.2 := by
  rw [mem_doublyMarkedCorePairs_iff] at hz
  obtain ⟨hzCore, hzx, hzy⟩ := hz
  calc
    (∑ a ∈ z.1.1.erase z.2.1, a) + z.2.1 = ∑ a ∈ z.1.1, a :=
      Finset.sum_erase_add _ (fun a : F => a) hzx
    _ = ∑ b ∈ z.1.2, b := (mem_subsetCorePairs_iff.mp hzCore).2.2.2.1
    _ = (∑ b ∈ z.1.2.erase z.2.2, b) + z.2.2 :=
      (Finset.sum_erase_add _ (fun b : F => b) hzy).symm

/-- Equal deletion codes recover both marks and both original supports. -/
theorem doubleDeletionCode_injOn (G : Finset F) (t : ℕ) :
    Set.InjOn doubleDeletionCode
      (↑(doublyMarkedCorePairs G t) : Set (Σ _c : Finset F × Finset F, F × F)) := by
  intro z hz w hw hcode
  have hA : z.1.1.erase z.2.1 = w.1.1.erase w.2.1 :=
    congrArg (fun q => q.1.1) hcode
  have hB : z.1.2.erase z.2.2 = w.1.2.erase w.2.2 :=
    congrArg (fun q => q.1.2) hcode
  have hx : z.2.1 = w.2.1 := congrArg Prod.snd hcode
  have hy : z.2.2 = w.2.2 := by
    have hzsum := marked_core_sum_identity hz
    have hwsum := marked_core_sum_identity hw
    rw [hA, hB, hx] at hzsum
    exact add_left_cancel (hzsum.symm.trans hwsum)
  have hS : z.1.1 = w.1.1 := by
    have hzx := (mem_doublyMarkedCorePairs_iff.mp hz).2.1
    have hwx := (mem_doublyMarkedCorePairs_iff.mp hw).2.1
    calc
      z.1.1 = insert z.2.1 (z.1.1.erase z.2.1) := (Finset.insert_erase hzx).symm
      _ = insert z.2.1 (w.1.1.erase w.2.1) := congrArg (insert z.2.1) hA
      _ = insert w.2.1 (w.1.1.erase w.2.1) := by rw [hx]
      _ = w.1.1 := Finset.insert_erase hwx
  have hT : z.1.2 = w.1.2 := by
    have hzy := (mem_doublyMarkedCorePairs_iff.mp hz).2.2
    have hwy := (mem_doublyMarkedCorePairs_iff.mp hw).2.2
    calc
      z.1.2 = insert z.2.2 (z.1.2.erase z.2.2) := (Finset.insert_erase hzy).symm
      _ = insert z.2.2 (w.1.2.erase w.2.2) := congrArg (insert z.2.2) hB
      _ = insert w.2.2 (w.1.2.erase w.2.2) := by rw [hy]
      _ = w.1.2 := Finset.insert_erase hwy
  apply Sigma.ext
  · exact Prod.ext hS hT
  · exact heq_of_eq (Prod.ext hx hy)

theorem doublyMarkedCorePairs_card (G : Finset F) (t : ℕ) :
    (doublyMarkedCorePairs G t).card = (subsetCorePairs G t).card * (t ^ 2) := by
  classical
  rw [doublyMarkedCorePairs, Finset.card_sigma]
  calc
    (∑ c ∈ subsetCorePairs G t, (c.1 ×ˢ c.2).card) =
        ∑ _c ∈ subsetCorePairs G t, t ^ 2 := by
      apply Finset.sum_congr rfl
      intro c hc
      rw [Finset.card_product]
      have hL := (Finset.mem_powersetCard.mp (mem_subsetCorePairs_iff.mp hc).1).2
      have hR := (Finset.mem_powersetCard.mp (mem_subsetCorePairs_iff.mp hc).2.1).2
      rw [hL, hR]
      simp [pow_two]
    _ = (subsetCorePairs G t).card * t ^ 2 := by simp

theorem doubleDeletionAmbient_card (G : Finset F) (t : ℕ) :
    (doubleDeletionAmbient G t).card = (G.card.choose (t - 1)) ^ 2 * G.card := by
  simp [doubleDeletionAmbient, Finset.card_product, Finset.card_powersetCard, pow_two]

/-- **G168 capstone.** Every balanced core census receives an unconditional one-power ambient
saving from double marked deletion. -/
theorem subsetCorePairs_mul_sq_le_choose_sq_mul_card (G : Finset F) (t : ℕ) :
    (subsetCorePairs G t).card * (t ^ 2) ≤
      (G.card.choose (t - 1)) ^ 2 * G.card := by
  rw [← doublyMarkedCorePairs_card, ← doubleDeletionAmbient_card]
  exact Finset.card_le_card_of_injOn doubleDeletionCode
    (fun _ hz => doubleDeletionCode_maps hz) (doubleDeletionCode_injOn G t)

theorem primitiveCorePairs_mul_sq_le_choose_sq_mul_card (G : Finset F) (t : ℕ) :
    (ArkLib.ProximityGap.Frontier.G152DepthFourCompositeCensus.primitiveCorePairs G t).card *
        (t ^ 2) ≤ (G.card.choose (t - 1)) ^ 2 * G.card :=
  by
    classical
    exact (Nat.mul_le_mul_right (t ^ 2)
      (Finset.card_le_card (Finset.filter_subset _ _))).trans
        (subsetCorePairs_mul_sq_le_choose_sq_mul_card G t)

#print axioms doubleDeletionCode_injOn
#print axioms doublyMarkedCorePairs_card
#print axioms subsetCorePairs_mul_sq_le_choose_sq_mul_card
#print axioms primitiveCorePairs_mul_sq_le_choose_sq_mul_card

end ArkLib.ProximityGap.Frontier.G168DoubleDeletionCoreBound
