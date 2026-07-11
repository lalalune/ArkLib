/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G195DepthThreeCenteredMobius

/-!
# G196: explicit F₇ Möbius cancellation certificate

For the genuine order-three subgroup `{1,2,4} ⊂ (ZMod 7)ˣ`, G193 computed the symmetric
pattern energies.  G195's coordinate bridge converts those values into the signed Möbius basis:

* `V(B) = 24`;
* `⟨B,C⟩_c = 15`;
* the unsigned diagonal is `264` and the signed correction is `180`;
* their difference is the exact defect energy `84`.

This is a concrete benchmark showing that triple-overlap cancellation removes more than two thirds
of the unsigned Möbius envelope.

Issue #466.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G196F7MobiusCancellation

open ArkLib.ProximityGap.Frontier.G175CenteredDeletionMonotonicityNoGo
open ArkLib.ProximityGap.Frontier.G176RepetitionDefectCovariance
open ArkLib.ProximityGap.Frontier.G179RepetitionPenaltyTransfer
open ArkLib.ProximityGap.Frontier.G192DepthThreeSymmetricPatterns
open ArkLib.ProximityGap.Frontier.G194DepthThreeMobiusTransform
open ArkLib.ProximityGap.Frontier.G195DepthThreeCenteredMobius

namespace F7

open ArkLib.ProximityGap.Frontier.G193SymmetricPatternCovarianceRefuted

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

theorem pair_triple_centeredInner_eq :
    centeredInner (pair01Profile G) (allThreeEqualProfile G) = 15 := by
  have h := exactlyTwo_triple_centeredInner_eq_pair_bridge G
  rw [symmetricPatternCovariance_eq, allThree_centeredSqMass] at h
  linarith

theorem pair_centeredSqMass_eq : centeredSqMass (pair01Profile G) = 24 := by
  have h := factorialRepetitionDefect_three_centeredMass_eq_mobius G
  rw [defect_centeredSqMass, allThree_centeredSqMass, pair_triple_centeredInner_eq] at h
  linarith

theorem mobius_unsigned_diagonal_eq :
    9 * centeredSqMass (pair01Profile G) +
      4 * centeredSqMass (allThreeEqualProfile G) = 264 := by
  rw [pair_centeredSqMass_eq, allThree_centeredSqMass]
  norm_num

theorem mobius_signed_correction_eq :
    12 * centeredInner (pair01Profile G) (allThreeEqualProfile G) = 180 := by
  rw [pair_triple_centeredInner_eq]
  norm_num

/-- The signed overlap removes exactly `15/22` of the unsigned diagonal envelope. -/
theorem mobius_cancellation_ratio : (180 : ℝ) / 264 = 15 / 22 := by norm_num

theorem defect_energy_eq_unsigned_sub_correction :
    centeredSqMass (factorialRepetitionDefect G 3) = 264 - 180 := by
  rw [factorialRepetitionDefect_three_centeredMass_eq_mobius,
    pair_centeredSqMass_eq, allThree_centeredSqMass, pair_triple_centeredInner_eq]
  norm_num

#print axioms pair_triple_centeredInner_eq
#print axioms pair_centeredSqMass_eq
#print axioms mobius_unsigned_diagonal_eq
#print axioms mobius_signed_correction_eq
#print axioms mobius_cancellation_ratio
#print axioms defect_energy_eq_unsigned_sub_correction

end F7

end ArkLib.ProximityGap.Frontier.G196F7MobiusCancellation
