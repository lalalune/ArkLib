/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G196F7MobiusCancellation

/-!
# G197: universal depth-three Möbius sign refuted

The favorable sign `0 ≤ ⟨B,C⟩_c` from the F₇ order-three subgroup is not universal.  For the
full multiplicative subgroup `F₅ˣ = {1,2,3,4}`, the pair-collision profile is `(4,3,3,3,3)`
and the triple profile is `(0,1,1,1,1)`.  Their centered covariance is `-4`.

Consequently the signed term in `D₃ = 3B - 2C` is an energy penalty of `48`: the unsigned
diagonal is `52`, while the exact repetition-defect energy is `100`.  This closes the universal
nonnegative pair/triple-correlation route.

Issue #466.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G197F5MobiusSignRefuted

open scoped BigOperators
open ArkLib.ProximityGap.Frontier.G175CenteredDeletionMonotonicityNoGo
open ArkLib.ProximityGap.Frontier.G176RepetitionDefectCovariance
open ArkLib.ProximityGap.Frontier.G179RepetitionPenaltyTransfer
open ArkLib.ProximityGap.Frontier.G182AllDepthDefectCarrier
open ArkLib.ProximityGap.Frontier.G183PairCollisionEnergyReduction
open ArkLib.ProximityGap.Frontier.G192DepthThreeSymmetricPatterns
open ArkLib.ProximityGap.Frontier.G194DepthThreeMobiusTransform
open ArkLib.ProximityGap.Frontier.G195DepthThreeCenteredMobius

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

def G : Finset (ZMod 5) := {1, 2, 3, 4}

theorem G_is_full_multiplicative_subgroup : G.card = 4 ∧
    (∀ x ∈ G, ∀ y ∈ G, x * y ∈ G) ∧ (1 : ZMod 5) ∈ G := by
  decide

def pairFiberC (t : ZMod 5) : Finset (Fin 3 → ZMod 5) :=
  ((Fintype.piFinset fun _ : Fin 3 => G).filter fun v => ∑ i, v i = t).filter
    fun v => v 0 = v 1

def repeatedFiberC (t : ZMod 5) : Finset (Fin 3 → ZMod 5) :=
  ((Fintype.piFinset fun _ : Fin 3 => G).filter fun v => ∑ i, v i = t).filter
    fun v => ¬Function.Injective v

def allThreeFiberC (t : ZMod 5) : Finset (Fin 3 → ZMod 5) :=
  (repeatedFiberC t).filter
    fun v => v 0 = v 1 ∧ v 1 = v 2

theorem pairFiberC_eq (t : ZMod 5) :
    pairFiberC t = pairCollisionFiber G 3 t ((0 : Fin 3), (1 : Fin 3)) := by
  classical
  ext v
  simp [pairFiberC, pairCollisionFiber, tupleSumFiber]

theorem allThreeFiberC_eq (t : ZMod 5) : allThreeFiberC t = allThreeEqualFiber G t := by
  classical
  ext v
  simp [allThreeFiberC, repeatedFiberC, allThreeEqualFiber, repeatedTupleSumFiber,
    tupleSumFiber, allThreeEqual]

theorem pair_profile_values_computable :
    (fun t : ZMod 5 => (pairFiberC t).card) = fun t => if t = 0 then 4 else 3 := by
  decide

theorem allThree_profile_values_computable :
    (fun t : ZMod 5 => (allThreeFiberC t).card) = fun t => if t = 0 then 0 else 1 := by
  decide

theorem pair_profile_real :
    pair01Profile G = fun t : ZMod 5 => if t = 0 then 4 else 3 := by
  funext t
  unfold pair01Profile
  rw [← pairFiberC_eq]
  exact_mod_cast congrFun pair_profile_values_computable t

theorem allThree_profile_real :
    allThreeEqualProfile G = fun t : ZMod 5 => if t = 0 then 0 else 1 := by
  funext t
  unfold allThreeEqualProfile
  rw [← allThreeFiberC_eq]
  exact_mod_cast congrFun allThree_profile_values_computable t

theorem pair_sum : ∑ t : ZMod 5, pair01Profile G t = 16 := by
  rw [pair_profile_real]
  calc
    _ = ∑ t : ZMod 5, (3 + if t = 0 then (1 : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro t _
      split_ifs <;> simp_all <;> norm_num
    _ = 16 := by
      rw [Finset.sum_add_distrib, Fintype.sum_ite_eq' 0]
      simp
      norm_num

theorem triple_sum : ∑ t : ZMod 5, allThreeEqualProfile G t = 4 := by
  rw [allThree_profile_real]
  calc
    _ = ∑ t : ZMod 5, (1 - if t = 0 then (1 : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro t _
      split_ifs <;> simp_all
    _ = 4 := by
      rw [Finset.sum_sub_distrib, Fintype.sum_ite_eq' 0]
      simp
      norm_num

theorem pair_product_triple_sum :
    ∑ t : ZMod 5, pair01Profile G t * allThreeEqualProfile G t = 12 := by
  rw [pair_profile_real, allThree_profile_real]
  calc
    _ = ∑ t : ZMod 5, (3 - if t = 0 then (3 : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro t _
      split_ifs <;> simp_all
    _ = 12 := by
      rw [Finset.sum_sub_distrib, Fintype.sum_ite_eq' 0]
      simp
      norm_num

/-- **Actual-subgroup refutation of the favorable Möbius sign.** -/
theorem pair_triple_centeredInner_eq :
    centeredInner (pair01Profile G) (allThreeEqualProfile G) = -4 := by
  unfold centeredInner
  rw [pair_product_triple_sum, pair_sum, triple_sum]
  norm_num

theorem not_pair_triple_centeredInner_nonneg :
    ¬0 ≤ centeredInner (pair01Profile G) (allThreeEqualProfile G) := by
  rw [pair_triple_centeredInner_eq]
  norm_num

theorem pair_centeredSqMass_eq : centeredSqMass (pair01Profile G) = 4 := by
  unfold centeredSqMass
  rw [pair_sum, pair_profile_real]
  have hs : ∑ t : ZMod 5, (if t = 0 then (4 : ℝ) else 3) ^ 2 = 52 := by
    calc
      _ = ∑ t : ZMod 5, (9 + if t = 0 then (7 : ℝ) else 0) := by
        apply Finset.sum_congr rfl
        intro t _
        split_ifs <;> simp_all <;> norm_num
      _ = 52 := by
        rw [Finset.sum_add_distrib, Fintype.sum_ite_eq' 0]
        simp
        norm_num
  rw [hs]
  norm_num

theorem triple_centeredSqMass_eq : centeredSqMass (allThreeEqualProfile G) = 4 := by
  unfold centeredSqMass
  rw [triple_sum, allThree_profile_real]
  have hs : ∑ t : ZMod 5, (if t = 0 then (0 : ℝ) else 1) ^ 2 = 4 := by
    calc
      _ = ∑ t : ZMod 5, (1 - if t = 0 then (1 : ℝ) else 0) := by
        apply Finset.sum_congr rfl
        intro t _
        split_ifs <;> simp_all
      _ = 4 := by
        rw [Finset.sum_sub_distrib, Fintype.sum_ite_eq' 0]
        simp
        norm_num
  rw [hs]
  norm_num

theorem mobius_unsigned_diagonal_eq :
    9 * centeredSqMass (pair01Profile G) +
      4 * centeredSqMass (allThreeEqualProfile G) = 52 := by
  rw [pair_centeredSqMass_eq, triple_centeredSqMass_eq]
  norm_num

theorem mobius_signed_term_eq :
    -(12 * centeredInner (pair01Profile G) (allThreeEqualProfile G)) = 48 := by
  rw [pair_triple_centeredInner_eq]
  norm_num

theorem defect_centeredSqMass_eq :
    centeredSqMass (factorialRepetitionDefect G 3) = 100 := by
  rw [factorialRepetitionDefect_three_centeredMass_eq_mobius,
    pair_centeredSqMass_eq, triple_centeredSqMass_eq, pair_triple_centeredInner_eq]
  norm_num

#print axioms pair_triple_centeredInner_eq
#print axioms not_pair_triple_centeredInner_nonneg
#print axioms pair_centeredSqMass_eq
#print axioms triple_centeredSqMass_eq
#print axioms mobius_unsigned_diagonal_eq
#print axioms mobius_signed_term_eq
#print axioms defect_centeredSqMass_eq

end ArkLib.ProximityGap.Frontier.G197F5MobiusSignRefuted
