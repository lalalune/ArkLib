/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G187WeightedConvolutionBridge
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G174DCDeletionConsumer

/-!
# G188: explicit DC barrier for the unsigned repetition-defect route

The ordered collision-index set has exactly `r(r-1)` elements.  Substituting the existing DC/Wick
bound at depth `r-2` into G187 gives a fully explicit spike-plus-Wick estimate for the repetition
defect.  Its DC term exhibits the unavoidable `r^4` loss of the unsigned pair-cover route.

Issue #466.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G188ExplicitDefectDCBarrier

open ArkLib.ProximityGap.DCEnergyCorrection
open ArkLib.ProximityGap.Frontier.G171ShiftedREnergyAutocorrelation
open ArkLib.ProximityGap.Frontier.G174DCDeletionConsumer
open ArkLib.ProximityGap.Frontier.G175CenteredDeletionMonotonicityNoGo
open ArkLib.ProximityGap.Frontier.G179RepetitionPenaltyTransfer
open ArkLib.ProximityGap.Frontier.G183PairCollisionEnergyReduction
open ArkLib.ProximityGap.Frontier.G187WeightedConvolutionBridge

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem collisionIndices_eq_offDiag (r : ℕ) :
    collisionIndices r = (Finset.univ : Finset (Fin r)).offDiag := by
  ext ij
  simp [collisionIndices, Finset.mem_offDiag]

theorem collisionIndices_card (r : ℕ) :
    (collisionIndices r).card = r * (r - 1) := by
  rw [collisionIndices_eq_offDiag, Finset.offDiag_card, Finset.card_univ,
    Fintype.card_fin]
  simp [Nat.mul_sub_left_distrib]

/-- **Explicit DC/Wick repetition-defect bound.** -/
theorem factorialRepetitionDefect_centeredMass_le_dc_spike_add_wick
    (G : Finset F) {r : ℕ} (hr : 2 ≤ r) (hdc : DCEnergyBound G (r - 2)) :
    centeredSqMass (factorialRepetitionDefect G r) ≤
      ((r * (r - 1) : ℕ) : ℝ) ^ 2 * (G.card : ℝ) ^ 2 *
        ((G.card : ℝ) ^ (2 * (r - 2)) +
          (Fintype.card F : ℝ) * wickTerm G (r - 2)) := by
  have hbase := factorialRepetitionDefect_centeredMass_le_lowerEnergy G hr
  rw [collisionIndices_card] at hbase
  have hdcEnergy := rEnergy_le_dc_spike_add_wick G (r - 2) hdc
  rw [rEnergy_eq_addREnergy] at hdcEnergy
  have hcoeff : 0 ≤ ((r * (r - 1) : ℕ) : ℝ) ^ 2 * (G.card : ℝ) ^ 2 := by positivity
  calc
    centeredSqMass (factorialRepetitionDefect G r) ≤
        (Fintype.card F : ℝ) * ((r * (r - 1) : ℕ) : ℝ) ^ 2 *
          ((G.card : ℝ) ^ 2 * Finset.addREnergy (r - 2) G) := hbase
    _ = (((r * (r - 1) : ℕ) : ℝ) ^ 2 * (G.card : ℝ) ^ 2) *
        ((Fintype.card F : ℝ) * Finset.addREnergy (r - 2) G) := by ring
    _ ≤ (((r * (r - 1) : ℕ) : ℝ) ^ 2 * (G.card : ℝ) ^ 2) *
        ((G.card : ℝ) ^ (2 * (r - 2)) +
          (Fintype.card F : ℝ) * wickTerm G (r - 2)) :=
      mul_le_mul_of_nonneg_left hdcEnergy hcoeff
    _ = _ := by ring

/-- The DC spike term alone has the exact scale `r²(r-1)² |G|^(2r-2)`. -/
theorem defect_dc_spike_normal_form (G : Finset F) {r : ℕ} (hr : 2 ≤ r) :
    ((r * (r - 1) : ℕ) : ℝ) ^ 2 * (G.card : ℝ) ^ 2 *
        (G.card : ℝ) ^ (2 * (r - 2)) =
      ((r * (r - 1) : ℕ) : ℝ) ^ 2 * (G.card : ℝ) ^ (2 * r - 2) := by
  have hpow : 2 + 2 * (r - 2) = 2 * r - 2 := by omega
  calc
    _ = ((r * (r - 1) : ℕ) : ℝ) ^ 2 *
        ((G.card : ℝ) ^ 2 * (G.card : ℝ) ^ (2 * (r - 2))) := by ring
    _ = ((r * (r - 1) : ℕ) : ℝ) ^ 2 *
        (G.card : ℝ) ^ (2 + 2 * (r - 2)) := by rw [pow_add]
    _ = _ := by rw [hpow]

#print axioms collisionIndices_card
#print axioms factorialRepetitionDefect_centeredMass_le_dc_spike_add_wick
#print axioms defect_dc_spike_normal_form

end ArkLib.ProximityGap.Frontier.G188ExplicitDefectDCBarrier
