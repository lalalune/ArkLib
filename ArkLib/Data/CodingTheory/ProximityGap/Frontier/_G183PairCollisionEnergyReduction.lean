/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G182AllDepthDefectCarrier

/-!
# G183: all-depth repetition energy reduces to pair-collision fibers

Every noninjective tuple has a colliding coordinate pair.  This file covers G182's exact repeated
carrier by those pair-collision fibers and applies finite Cauchy--Schwarz.  The resulting centered
defect bound depends on squared lower-dimensional weighted-sum fibers rather than the square of the
entire birthday mass.

Issue #466.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G183PairCollisionEnergyReduction

open scoped BigOperators
open ArkLib.ProximityGap.Frontier.G175CenteredDeletionMonotonicityNoGo
open ArkLib.ProximityGap.Frontier.G179RepetitionPenaltyTransfer
open ArkLib.ProximityGap.Frontier.G182AllDepthDefectCarrier

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def collisionIndices (r : ℕ) : Finset (Fin r × Fin r) :=
  ((Finset.univ : Finset (Fin r)) ×ˢ Finset.univ).filter fun ij => ij.1 ≠ ij.2

noncomputable def pairCollisionFiber (G : Finset F) (r : ℕ) (t : F)
    (ij : Fin r × Fin r) : Finset (Fin r → F) :=
  (tupleSumFiber G r t).filter fun v => v ij.1 = v ij.2

noncomputable def pairCollisionCover (G : Finset F) (r : ℕ) (t : F) :
    Finset (Fin r → F) :=
  (collisionIndices r).biUnion fun ij => pairCollisionFiber G r t ij

theorem repeatedTupleSumFiber_subset_pairCollisionCover
    (G : Finset F) (r : ℕ) (t : F) :
    repeatedTupleSumFiber G r t ⊆ pairCollisionCover G r t := by
  intro v hv
  rw [repeatedTupleSumFiber, Finset.mem_filter] at hv
  obtain ⟨hvsum, hvrep⟩ := hv
  obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hvrep
  rw [pairCollisionCover, Finset.mem_biUnion]
  refine ⟨(i, j), ?_, ?_⟩
  · rw [collisionIndices, Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨Finset.mem_univ i, Finset.mem_univ j⟩, hne⟩
  · rw [pairCollisionFiber, Finset.mem_filter]
    exact ⟨hvsum, hij⟩

theorem repeatedTupleSumFiber_card_le_sum_pairCollisionFiber_card
    (G : Finset F) (r : ℕ) (t : F) :
    (repeatedTupleSumFiber G r t).card ≤
      ∑ ij ∈ collisionIndices r, (pairCollisionFiber G r t ij).card := by
  exact (Finset.card_le_card (repeatedTupleSumFiber_subset_pairCollisionCover G r t)).trans
    (Finset.card_biUnion_le (s := collisionIndices r) (t := pairCollisionFiber G r t))

theorem centeredSqMass_le_card_mul_sum_sq' {A : Type*} [Fintype A] (f : A → ℝ) :
    centeredSqMass f ≤ (Fintype.card A : ℝ) * ∑ a, f a ^ 2 := by
  unfold centeredSqMass
  nlinarith [sq_nonneg (∑ a, f a)]

theorem repeated_card_sq_le_pair_collision_sq_sum
    (G : Finset F) (r : ℕ) (t : F) :
    ((repeatedTupleSumFiber G r t).card : ℝ) ^ 2 ≤
      ((collisionIndices r).card : ℝ) *
        ∑ ij ∈ collisionIndices r, ((pairCollisionFiber G r t ij).card : ℝ) ^ 2 := by
  have hcoverNat := repeatedTupleSumFiber_card_le_sum_pairCollisionFiber_card G r t
  have hcover : ((repeatedTupleSumFiber G r t).card : ℝ) ≤
      ∑ ij ∈ collisionIndices r, ((pairCollisionFiber G r t ij).card : ℝ) := by
    exact_mod_cast hcoverNat
  have hcs := sq_sum_le_card_mul_sum_sq
    (s := collisionIndices r)
    (f := fun ij => ((pairCollisionFiber G r t ij).card : ℝ))
  have hrep : 0 ≤ ((repeatedTupleSumFiber G r t).card : ℝ) := Nat.cast_nonneg _
  have hsum : 0 ≤ ∑ ij ∈ collisionIndices r,
      ((pairCollisionFiber G r t ij).card : ℝ) := by positivity
  have hsq : ((repeatedTupleSumFiber G r t).card : ℝ) ^ 2 ≤
      (∑ ij ∈ collisionIndices r, ((pairCollisionFiber G r t ij).card : ℝ)) ^ 2 := by
    nlinarith
  exact hsq.trans (by simpa only [Finset.card_eq_sum_ones] using hcs)

/-- **All-depth pair-collision energy reduction.** -/
theorem factorialRepetitionDefect_centeredMass_le_pairCollisionEnergy
    (G : Finset F) (r : ℕ) :
    centeredSqMass (factorialRepetitionDefect G r) ≤
      (Fintype.card F : ℝ) * (collisionIndices r).card *
        ∑ t : F, ∑ ij ∈ collisionIndices r,
          ((pairCollisionFiber G r t ij).card : ℝ) ^ 2 := by
  have hbase := centeredSqMass_le_card_mul_sum_sq'
    (fun t : F => ((repeatedTupleSumFiber G r t).card : ℝ))
  have hpoint : ∑ t : F, ((repeatedTupleSumFiber G r t).card : ℝ) ^ 2 ≤
      ∑ t : F, ((collisionIndices r).card : ℝ) *
        ∑ ij ∈ collisionIndices r,
          ((pairCollisionFiber G r t ij).card : ℝ) ^ 2 := by
    exact Finset.sum_le_sum fun t _ => repeated_card_sq_le_pair_collision_sq_sum G r t
  have hcard : 0 ≤ (Fintype.card F : ℝ) := Nat.cast_nonneg _
  have hmul := mul_le_mul_of_nonneg_left hpoint hcard
  rw [show factorialRepetitionDefect G r =
      (fun t : F => ((repeatedTupleSumFiber G r t).card : ℝ)) by
    funext t
    exact factorialRepetitionDefect_eq_repeatedTupleSumFiber_card G r t]
  calc
    centeredSqMass (fun t : F => ((repeatedTupleSumFiber G r t).card : ℝ)) ≤
        (Fintype.card F : ℝ) *
          ∑ t : F, ((repeatedTupleSumFiber G r t).card : ℝ) ^ 2 := hbase
    _ ≤ (Fintype.card F : ℝ) * ∑ t : F, ((collisionIndices r).card : ℝ) *
        ∑ ij ∈ collisionIndices r,
          ((pairCollisionFiber G r t ij).card : ℝ) ^ 2 := hmul
    _ = _ := by
      rw [← Finset.mul_sum]
      ring

#print axioms repeatedTupleSumFiber_subset_pairCollisionCover
#print axioms repeatedTupleSumFiber_card_le_sum_pairCollisionFiber_card
#print axioms repeated_card_sq_le_pair_collision_sq_sum
#print axioms factorialRepetitionDefect_centeredMass_le_pairCollisionEnergy

end ArkLib.ProximityGap.Frontier.G183PairCollisionEnergyReduction
