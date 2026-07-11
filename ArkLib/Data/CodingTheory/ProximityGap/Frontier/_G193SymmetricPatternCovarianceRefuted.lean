/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G192DepthThreeSymmetricPatterns

/-!
# G193: symmetric pattern covariance can be positive

The nonpositive covariance gate for the permutation-symmetric depth-three kernel partition is also
false in a genuine subgroup.  Over `ZMod 7`, the order-three subgroup `{1,2,4}` has covariance `9`
between its `2+1` and `3` equality-pattern profiles.

Issue #466.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G193SymmetricPatternCovarianceRefuted

open scoped BigOperators
open ArkLib.ProximityGap.Frontier.G175CenteredDeletionMonotonicityNoGo
open ArkLib.ProximityGap.Frontier.G176RepetitionDefectCovariance
open ArkLib.ProximityGap.Frontier.G179RepetitionPenaltyTransfer
open ArkLib.ProximityGap.Frontier.G182AllDepthDefectCarrier
open ArkLib.ProximityGap.Frontier.G192DepthThreeSymmetricPatterns

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

def G : Finset (ZMod 7) := {1, 2, 4}
def tripleSupport : Finset (ZMod 7) := {3, 5, 6}

theorem G_is_order_three_subgroup : G.card = 3 ∧
    (∀ x ∈ G, ∀ y ∈ G, x * y ∈ G) ∧ (1 : ZMod 7) ∈ G := by
  decide

def repeatedFiberC (t : ZMod 7) : Finset (Fin 3 → ZMod 7) :=
  (((Fintype.piFinset fun _ : Fin 3 => G).filter fun v => ∑ i, v i = t).filter
    fun v => ¬Function.Injective v)

def exactlyTwoFiberC (t : ZMod 7) : Finset (Fin 3 → ZMod 7) :=
  (repeatedFiberC t).filter fun v => ¬(v 0 = v 1 ∧ v 1 = v 2)

def allThreeFiberC (t : ZMod 7) : Finset (Fin 3 → ZMod 7) :=
  (repeatedFiberC t).filter fun v => v 0 = v 1 ∧ v 1 = v 2

theorem exactlyTwoFiberC_eq (t : ZMod 7) : exactlyTwoFiberC t = exactlyTwoEqualFiber G t := by
  classical
  ext v
  simp [exactlyTwoFiberC, repeatedFiberC, exactlyTwoEqualFiber, repeatedTupleSumFiber,
    tupleSumFiber, allThreeEqual]

theorem allThreeFiberC_eq (t : ZMod 7) : allThreeFiberC t = allThreeEqualFiber G t := by
  classical
  ext v
  simp [allThreeFiberC, repeatedFiberC, allThreeEqualFiber, repeatedTupleSumFiber,
    tupleSumFiber, allThreeEqual]

theorem exactlyTwo_profile_values_computable :
    (fun t : ZMod 7 => (exactlyTwoFiberC t).card) = fun t => if t = 0 then 0 else 3 := by
  decide

theorem allThree_profile_values_computable :
    (fun t : ZMod 7 => (allThreeFiberC t).card) =
      fun t => if t ∈ tripleSupport then 1 else 0 := by
  decide

theorem exactlyTwo_profile_values :
    (fun t : ZMod 7 => (exactlyTwoEqualFiber G t).card) =
      fun t => if t = 0 then 0 else 3 := by
  funext t
  rw [← exactlyTwoFiberC_eq]
  exact congrFun exactlyTwo_profile_values_computable t

theorem allThree_profile_values :
    (fun t : ZMod 7 => (allThreeEqualFiber G t).card) =
      fun t => if t ∈ tripleSupport then 1 else 0 := by
  funext t
  rw [← allThreeFiberC_eq]
  exact congrFun allThree_profile_values_computable t

theorem tripleSupport_card : tripleSupport.card = 3 := by decide
theorem zero_not_mem_tripleSupport : (0 : ZMod 7) ∉ tripleSupport := by decide

theorem exactlyTwo_profile_real :
    exactlyTwoEqualProfile G = fun t : ZMod 7 => if t = 0 then 0 else 3 := by
  funext t
  unfold exactlyTwoEqualProfile
  exact_mod_cast congrFun exactlyTwo_profile_values t

theorem allThree_profile_real :
    allThreeEqualProfile G = fun t : ZMod 7 => if t ∈ tripleSupport then 1 else 0 := by
  funext t
  unfold allThreeEqualProfile
  exact_mod_cast congrFun allThree_profile_values t

theorem exactlyTwo_sum : ∑ t : ZMod 7, exactlyTwoEqualProfile G t = 18 := by
  rw [exactlyTwo_profile_real]
  calc
    _ = ∑ t : ZMod 7, (3 - if t = 0 then (3 : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro t _
      split_ifs <;> simp_all <;> norm_num
    _ = 18 := by
      rw [Finset.sum_sub_distrib, Fintype.sum_ite_eq' 0]
      simp
      norm_num

theorem exactlyTwo_sum_sq : ∑ t : ZMod 7, exactlyTwoEqualProfile G t ^ 2 = 54 := by
  rw [exactlyTwo_profile_real]
  calc
    _ = ∑ t : ZMod 7, (9 - if t = 0 then (9 : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro t _
      split_ifs <;> simp_all <;> norm_num
    _ = 54 := by
      rw [Finset.sum_sub_distrib, Fintype.sum_ite_eq' 0]
      simp
      norm_num

theorem allThree_sum : ∑ t : ZMod 7, allThreeEqualProfile G t = 3 := by
  rw [allThree_profile_real]
  simp [tripleSupport_card]

theorem allThree_sum_sq : ∑ t : ZMod 7, allThreeEqualProfile G t ^ 2 = 3 := by
  simpa [allThree_profile_real] using allThree_sum

theorem pattern_product_sum :
    ∑ t : ZMod 7, exactlyTwoEqualProfile G t * allThreeEqualProfile G t = 9 := by
  rw [exactlyTwo_profile_real, allThree_profile_real]
  calc
    _ = ∑ t : ZMod 7, (3 : ℝ) * (if t ∈ tripleSupport then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro t _
      by_cases ht : t ∈ tripleSupport
      · have ht0 : t ≠ 0 := fun h => zero_not_mem_tripleSupport (h ▸ ht)
        simp [ht, ht0]
      · simp [ht]
    _ = 9 := by
      rw [← Finset.mul_sum]
      simp [tripleSupport_card]
      norm_num

theorem exactlyTwo_centeredSqMass : centeredSqMass (exactlyTwoEqualProfile G) = 54 := by
  unfold centeredSqMass
  rw [exactlyTwo_sum, exactlyTwo_sum_sq]
  norm_num

theorem allThree_centeredSqMass : centeredSqMass (allThreeEqualProfile G) = 12 := by
  unfold centeredSqMass
  rw [allThree_sum, allThree_sum_sq]
  norm_num

/-- **Actual-subgroup symmetric-pattern obstruction.** -/
theorem symmetricPatternCovariance_eq :
    centeredInner (exactlyTwoEqualProfile G) (allThreeEqualProfile G) = 9 := by
  unfold centeredInner
  rw [pattern_product_sum, exactlyTwo_sum, allThree_sum]
  norm_num

theorem not_symmetricPatternCovariance_nonpos :
    ¬centeredInner (exactlyTwoEqualProfile G) (allThreeEqualProfile G) ≤ 0 := by
  rw [symmetricPatternCovariance_eq]
  norm_num

theorem defect_centeredSqMass : centeredSqMass (factorialRepetitionDefect G 3) = 84 := by
  rw [factorialRepetitionDefect_three_centeredMass_eq_patterns,
    exactlyTwo_centeredSqMass, allThree_centeredSqMass, symmetricPatternCovariance_eq]
  norm_num

#print axioms symmetricPatternCovariance_eq
#print axioms not_symmetricPatternCovariance_nonpos
#print axioms defect_centeredSqMass

end ArkLib.ProximityGap.Frontier.G193SymmetricPatternCovarianceRefuted
