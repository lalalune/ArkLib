/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G191FirstCollisionCovarianceRefuted

/-!
# G192: symmetric depth-three equality-pattern decomposition

At depth three, every repeated tuple has kernel type `2+1` (exactly two equal values) or `3` (all
three equal).  These classes are permutation-invariant and disjoint.  This file partitions the
exact G182 carrier accordingly and polarizes their two target-sum profiles.

Issue #466.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G192DepthThreeSymmetricPatterns

open ArkLib.ProximityGap.Frontier.G175CenteredDeletionMonotonicityNoGo
open ArkLib.ProximityGap.Frontier.G176RepetitionDefectCovariance
open ArkLib.ProximityGap.Frontier.G179RepetitionPenaltyTransfer
open ArkLib.ProximityGap.Frontier.G182AllDepthDefectCarrier

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def allThreeEqual (v : Fin 3 → F) : Prop := v 0 = v 1 ∧ v 1 = v 2

noncomputable def allThreeEqualFiber (G : Finset F) (t : F) : Finset (Fin 3 → F) :=
  by classical exact (repeatedTupleSumFiber G 3 t).filter allThreeEqual

noncomputable def exactlyTwoEqualFiber (G : Finset F) (t : F) : Finset (Fin 3 → F) :=
  by classical exact (repeatedTupleSumFiber G 3 t).filter fun v => ¬allThreeEqual v

theorem allThreeEqualFiber_disjoint_exactlyTwoEqualFiber (G : Finset F) (t : F) :
    Disjoint (allThreeEqualFiber G t) (exactlyTwoEqualFiber G t) := by
  classical
  rw [Finset.disjoint_left]
  intro v hvall hvexact
  rw [allThreeEqualFiber, Finset.mem_filter] at hvall
  rw [exactlyTwoEqualFiber, Finset.mem_filter] at hvexact
  exact hvexact.2 hvall.2

theorem repeatedTupleSumFiber_three_card_eq_pattern_sum (G : Finset F) (t : F) :
    (repeatedTupleSumFiber G 3 t).card =
      (exactlyTwoEqualFiber G t).card + (allThreeEqualFiber G t).card := by
  classical
  have h := Finset.card_filter_add_card_filter_not
    (s := repeatedTupleSumFiber G 3 t) (p := allThreeEqual)
  simpa [allThreeEqualFiber, exactlyTwoEqualFiber, Nat.add_comm] using h.symm

noncomputable def exactlyTwoEqualProfile (G : Finset F) : F → ℝ :=
  fun t => (exactlyTwoEqualFiber G t).card

noncomputable def allThreeEqualProfile (G : Finset F) : F → ℝ :=
  fun t => (allThreeEqualFiber G t).card

theorem factorialRepetitionDefect_three_eq_pattern_sum (G : Finset F) :
    factorialRepetitionDefect G 3 =
      fun t => exactlyTwoEqualProfile G t + allThreeEqualProfile G t := by
  funext t
  rw [factorialRepetitionDefect_eq_repeatedTupleSumFiber_card,
    repeatedTupleSumFiber_three_card_eq_pattern_sum]
  push_cast
  rfl

/-- **Exact symmetric-pattern polarization.** -/
theorem factorialRepetitionDefect_three_centeredMass_eq_patterns (G : Finset F) :
    centeredSqMass (factorialRepetitionDefect G 3) =
      centeredSqMass (exactlyTwoEqualProfile G) +
        centeredSqMass (allThreeEqualProfile G) +
          2 * centeredInner (exactlyTwoEqualProfile G) (allThreeEqualProfile G) := by
  rw [factorialRepetitionDefect_three_eq_pattern_sum]
  exact centeredSqMass_add _ _

theorem factorialRepetitionDefect_three_centeredMass_le_patterns_of_covariance_nonpos
    (G : Finset F)
    (hcov : centeredInner (exactlyTwoEqualProfile G) (allThreeEqualProfile G) ≤ 0) :
    centeredSqMass (factorialRepetitionDefect G 3) ≤
      centeredSqMass (exactlyTwoEqualProfile G) + centeredSqMass (allThreeEqualProfile G) := by
  rw [factorialRepetitionDefect_three_centeredMass_eq_patterns]
  linarith

#print axioms repeatedTupleSumFiber_three_card_eq_pattern_sum
#print axioms factorialRepetitionDefect_three_eq_pattern_sum
#print axioms factorialRepetitionDefect_three_centeredMass_eq_patterns
#print axioms factorialRepetitionDefect_three_centeredMass_le_patterns_of_covariance_nonpos

end ArkLib.ProximityGap.Frontier.G192DepthThreeSymmetricPatterns
