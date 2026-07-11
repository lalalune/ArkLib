/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G190FirstCollisionCovariancePolarization

/-!
# G191: lexicographic first-collision covariance can be positive

The nonpositive aggregate-covariance gate from G190 is false even for a genuine multiplicative
subgroup.  Over `ZMod 5`, take the full nonzero subgroup and depth three.  The repeated profile has
centered mass `100`, the sum of stratum centered masses is `36`, and the aggregate off-diagonal
covariance is therefore `64 > 0`.

Issue #466.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G191FirstCollisionCovarianceRefuted

open ArkLib.ProximityGap.Frontier.G175CenteredDeletionMonotonicityNoGo
open ArkLib.ProximityGap.Frontier.G179RepetitionPenaltyTransfer
open ArkLib.ProximityGap.Frontier.G182AllDepthDefectCarrier
open ArkLib.ProximityGap.Frontier.G183PairCollisionEnergyReduction
open ArkLib.ProximityGap.Frontier.G189DisjointFirstCollisionPartition
open ArkLib.ProximityGap.Frontier.G190FirstCollisionCovariancePolarization

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

def G : Finset (ZMod 5) := {1, 2, 3, 4}

theorem G_eq_nonzero : G = Finset.univ.erase 0 := by decide

def hr : 2 ≤ 3 := by omega

theorem defect_profile_values :
    (fun t : ZMod 5 => (repeatedTupleSumFiber G 3 t).card) =
      fun t => if t = 0 then 12 else 7 := by
  decide

theorem first01_profile_values :
    (fun t : ZMod 5 => (firstCollisionFiber G hr t ((0 : Fin 3), (1 : Fin 3))).card) =
      fun t => if t = 0 then 4 else 3 := by
  decide

theorem first02_profile_values :
    (fun t : ZMod 5 => (firstCollisionFiber G hr t ((0 : Fin 3), (2 : Fin 3))).card) =
      fun t => if t = 0 then 4 else 2 := by
  decide

theorem first12_profile_values :
    (fun t : ZMod 5 => (firstCollisionFiber G hr t ((1 : Fin 3), (2 : Fin 3))).card) =
      fun t => if t = 0 then 4 else 2 := by
  decide

theorem first10_profile_values :
    (fun t : ZMod 5 => (firstCollisionFiber G hr t ((1 : Fin 3), (0 : Fin 3))).card) =
      fun _ => 0 := by
  decide

theorem first20_profile_values :
    (fun t : ZMod 5 => (firstCollisionFiber G hr t ((2 : Fin 3), (0 : Fin 3))).card) =
      fun _ => 0 := by
  decide

theorem first21_profile_values :
    (fun t : ZMod 5 => (firstCollisionFiber G hr t ((2 : Fin 3), (1 : Fin 3))).card) =
      fun _ => 0 := by
  decide

theorem centeredSqMass_if_zero (a b : ℝ) :
    centeredSqMass (fun t : ZMod 5 => if t = 0 then a else b) = 4 * (a - b) ^ 2 := by
  unfold centeredSqMass
  have hsum : (∑ t : ZMod 5, if t = 0 then a else b) = a + 4 * b := by
    calc
      _ = ∑ t : ZMod 5, (b + if t = 0 then a - b else 0) := by
        apply Finset.sum_congr rfl
        intro t _
        split_ifs <;> ring
      _ = a + 4 * b := by
        rw [Finset.sum_add_distrib, Fintype.sum_ite_eq' 0]
        simp
        ring
  have hsq : (∑ t : ZMod 5, (if t = 0 then a else b) ^ 2) = a ^ 2 + 4 * b ^ 2 := by
    calc
      _ = ∑ t : ZMod 5, (b ^ 2 + if t = 0 then a ^ 2 - b ^ 2 else 0) := by
        apply Finset.sum_congr rfl
        intro t _
        split_ifs <;> ring
      _ = a ^ 2 + 4 * b ^ 2 := by
        rw [Finset.sum_add_distrib, Fintype.sum_ite_eq' 0]
        simp
        ring
  rw [hsum, hsq]
  norm_num
  ring

theorem defect_centeredSqMass :
    centeredSqMass (factorialRepetitionDefect G 3) = 100 := by
  rw [show factorialRepetitionDefect G 3 =
      (fun t : ZMod 5 => if t = 0 then (12 : ℝ) else 7) by
    funext t
    rw [factorialRepetitionDefect_eq_repeatedTupleSumFiber_card]
    exact_mod_cast congrFun defect_profile_values t]
  rw [centeredSqMass_if_zero]
  norm_num

theorem first01_centeredSqMass :
    centeredSqMass (firstCollisionProfile G hr ((0 : Fin 3), (1 : Fin 3))) = 4 := by
  rw [show firstCollisionProfile G hr ((0 : Fin 3), (1 : Fin 3)) =
      (fun t : ZMod 5 => if t = 0 then (4 : ℝ) else 3) by
    funext t
    unfold firstCollisionProfile
    exact_mod_cast congrFun first01_profile_values t]
  rw [centeredSqMass_if_zero]
  norm_num

theorem first02_centeredSqMass :
    centeredSqMass (firstCollisionProfile G hr ((0 : Fin 3), (2 : Fin 3))) = 16 := by
  rw [show firstCollisionProfile G hr ((0 : Fin 3), (2 : Fin 3)) =
      (fun t : ZMod 5 => if t = 0 then (4 : ℝ) else 2) by
    funext t
    unfold firstCollisionProfile
    exact_mod_cast congrFun first02_profile_values t]
  rw [centeredSqMass_if_zero]
  norm_num

theorem first12_centeredSqMass :
    centeredSqMass (firstCollisionProfile G hr ((1 : Fin 3), (2 : Fin 3))) = 16 := by
  rw [show firstCollisionProfile G hr ((1 : Fin 3), (2 : Fin 3)) =
      (fun t : ZMod 5 => if t = 0 then (4 : ℝ) else 2) by
    funext t
    unfold firstCollisionProfile
    exact_mod_cast congrFun first12_profile_values t]
  rw [centeredSqMass_if_zero]
  norm_num

theorem collisionIndices_three : collisionIndices 3 =
    {((0 : Fin 3), (1 : Fin 3)), ((0 : Fin 3), (2 : Fin 3)),
      ((1 : Fin 3), (0 : Fin 3)), ((1 : Fin 3), (2 : Fin 3)),
      ((2 : Fin 3), (0 : Fin 3)), ((2 : Fin 3), (1 : Fin 3))} := by
  decide

theorem sum_strata_centeredSqMass :
    ∑ ij ∈ collisionIndices 3, centeredSqMass (firstCollisionProfile G hr ij) = 36 := by
  have h10 : firstCollisionProfile G hr ((1 : Fin 3), (0 : Fin 3)) = 0 := by
    funext t
    unfold firstCollisionProfile
    change ((firstCollisionFiber G hr t ((1 : Fin 3), (0 : Fin 3))).card : ℝ) = 0
    exact_mod_cast congrFun first10_profile_values t
  have h20 : firstCollisionProfile G hr ((2 : Fin 3), (0 : Fin 3)) = 0 := by
    funext t
    unfold firstCollisionProfile
    change ((firstCollisionFiber G hr t ((2 : Fin 3), (0 : Fin 3))).card : ℝ) = 0
    exact_mod_cast congrFun first20_profile_values t
  have h21 : firstCollisionProfile G hr ((2 : Fin 3), (1 : Fin 3)) = 0 := by
    funext t
    unfold firstCollisionProfile
    change ((firstCollisionFiber G hr t ((2 : Fin 3), (1 : Fin 3))).card : ℝ) = 0
    exact_mod_cast congrFun first21_profile_values t
  have hz : centeredSqMass (0 : ZMod 5 → ℝ) = 0 := by
    simp [centeredSqMass]
  rw [collisionIndices_three]
  simp [first01_centeredSqMass, first02_centeredSqMass, first12_centeredSqMass,
    h10, h20, h21, hz]
  norm_num

/-- **Actual-subgroup refutation.** The aggregate covariance is strictly positive. -/
theorem firstCollisionAggregateCovariance_eq :
    firstCollisionAggregateCovariance G hr = 64 := by
  have h := factorialRepetitionDefect_centeredMass_eq_strata_add_covariance G hr
  rw [defect_centeredSqMass, sum_strata_centeredSqMass] at h
  linarith

theorem not_firstCollisionAggregateCovariance_nonpos :
    ¬firstCollisionAggregateCovariance G hr ≤ 0 := by
  rw [firstCollisionAggregateCovariance_eq]
  norm_num

#print axioms defect_centeredSqMass
#print axioms sum_strata_centeredSqMass
#print axioms firstCollisionAggregateCovariance_eq
#print axioms not_firstCollisionAggregateCovariance_nonpos

end ArkLib.ProximityGap.Frontier.G191FirstCollisionCovarianceRefuted
