/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G177FactorialSubsetFiberAmplification

/-!
# G178: factorial-normalized centered contraction fails for a genuine subgroup

G177 gives the sharp pointwise comparison between the ordered injective profile and the ordered
with-replacement profile.  It is tempting to hope that the same comparison survives after DC
subtraction.  This file refutes that hope inside the actual multiplicative-subgroup model.

For the nonzero subgroup `G = {1,2}` of `ZMod 3` at depth two, the ordered injective profile is
`[2,0,0]`, while the with-replacement profile is `[2,1,1]`.  Their centered squared masses are
respectively `8` and `2`.  Thus even factorial normalization does not make deletion contract the
DC-subtracted energy.

Issue #466.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G178FactorialContractionSubgroupRefuted

open ArkLib.ProximityGap.Frontier.G171ShiftedREnergyAutocorrelation
open ArkLib.ProximityGap.Frontier.G172SubsetSumToREnergy
open ArkLib.ProximityGap.Frontier.G175CenteredDeletionMonotonicityNoGo

def G : Finset (ZMod 3) := {1, 2}

theorem G_eq_nonzero : G = Finset.univ.erase 0 := by decide

theorem factorial_subset_profile_values :
    (fun t : ZMod 3 => (2 : ℕ).factorial * (subsetSumFiber G 2 t).card) =
      fun t => if t = 0 then 2 else 0 := by
  decide

theorem replacement_profile_values :
    (fun t : ZMod 3 => rSumCount G 2 t) =
      fun t => if t = 0 then 2 else 1 := by
  decide

theorem factorial_subset_centeredSqMass :
    centeredSqMass (fun t : ZMod 3 =>
      ((2 : ℕ).factorial * (subsetSumFiber G 2 t).card : ℝ)) = 8 := by
  rw [show (fun t : ZMod 3 => ((2 : ℕ).factorial * (subsetSumFiber G 2 t).card : ℝ)) =
      (fun t => if t = 0 then (2 : ℝ) else 0) by
    funext t
    exact_mod_cast congrFun factorial_subset_profile_values t]
  simp [centeredSqMass]
  norm_num

theorem replacement_centeredSqMass :
    centeredSqMass (fun t : ZMod 3 => (rSumCount G 2 t : ℝ)) = 2 := by
  rw [show (fun t : ZMod 3 => (rSumCount G 2 t : ℝ)) =
      (fun t => if t = 0 then (2 : ℝ) else 1) by
    funext t
    exact_mod_cast congrFun replacement_profile_values t]
  unfold centeredSqMass
  have hsum : (∑ x : ZMod 3, if x = 0 then (2 : ℝ) else 1) = 4 := by
    calc
      _ = ∑ x : ZMod 3, (1 + if x = 0 then (1 : ℝ) else 0) := by
        apply Finset.sum_congr rfl
        intro x _
        split_ifs <;> norm_num
      _ = 4 := by
        rw [Finset.sum_add_distrib, Fintype.sum_ite_eq' 0]
        simp
        norm_num
  have hsq : (∑ x : ZMod 3, (if x = 0 then (2 : ℝ) else 1) ^ 2) = 6 := by
    calc
      _ = ∑ x : ZMod 3, (1 + if x = 0 then (3 : ℝ) else 0) := by
        apply Finset.sum_congr rfl
        intro x _
        split_ifs <;> norm_num
      _ = 6 := by
        rw [Finset.sum_add_distrib, Fintype.sum_ite_eq' 0]
        simp
        norm_num
  rw [hsum, hsq]
  norm_num

/-- **Actual-subgroup no-go.** Factorial normalization does not make the distinct-subset profile
contractive after centering. -/
theorem not_factorial_normalized_centered_contraction :
    ¬ centeredSqMass (fun t : ZMod 3 =>
        ((2 : ℕ).factorial * (subsetSumFiber G 2 t).card : ℝ)) ≤
      centeredSqMass (fun t : ZMod 3 => (rSumCount G 2 t : ℝ)) := by
  rw [factorial_subset_centeredSqMass, replacement_centeredSqMass]
  norm_num

#print axioms factorial_subset_profile_values
#print axioms replacement_profile_values
#print axioms not_factorial_normalized_centered_contraction

end ArkLib.ProximityGap.Frontier.G178FactorialContractionSubgroupRefuted
