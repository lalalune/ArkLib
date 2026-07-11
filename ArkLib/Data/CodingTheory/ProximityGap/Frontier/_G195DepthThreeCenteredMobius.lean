/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G194DepthThreeMobiusTransform

/-!
# G195: centered depth-three Möbius polarization

G194 identifies the depth-three repetition defect pointwise as `D₃ = 3 B - 2 C`, where `B`
is a canonical pair-collision profile and `C` is the all-three-equal profile.  This file performs
the exact centered polarization:

`V(D₃) = 9 V(B) + 4 V(C) - 12 ⟨B,C⟩_c`.

Thus the triple-overlap term has a favorable sign precisely when the centered pair/triple
correlation is positive.  No sign hypothesis is imposed here.

Issue #466.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G195DepthThreeCenteredMobius

open ArkLib.ProximityGap.Frontier.G175CenteredDeletionMonotonicityNoGo
open ArkLib.ProximityGap.Frontier.G176RepetitionDefectCovariance
open ArkLib.ProximityGap.Frontier.G179RepetitionPenaltyTransfer
open ArkLib.ProximityGap.Frontier.G192DepthThreeSymmetricPatterns
open ArkLib.ProximityGap.Frontier.G194DepthThreeMobiusTransform

theorem centeredInner_smul_left {A : Type*} [Fintype A]
    (c : ℝ) (f g : A → ℝ) :
    centeredInner (fun a => c * f a) g = c * centeredInner f g := by
  unfold centeredInner
  rw [show (∑ a, c * f a * g a) = c * ∑ a, f a * g a by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring]
  rw [show (∑ a, c * f a) = c * ∑ a, f a by
    rw [Finset.mul_sum]]
  ring

theorem centeredInner_smul_right {A : Type*} [Fintype A]
    (c : ℝ) (f g : A → ℝ) :
    centeredInner f (fun a => c * g a) = c * centeredInner f g := by
  rw [centeredInner_comm, centeredInner_smul_left, centeredInner_comm]

theorem centeredSqMass_smul {A : Type*} [Fintype A]
    (c : ℝ) (f : A → ℝ) :
    centeredSqMass (fun a => c * f a) = c ^ 2 * centeredSqMass f := by
  rw [centeredSqMass_eq_inner, centeredInner_smul_left,
    centeredInner_smul_right, centeredSqMass_eq_inner]
  ring

theorem centeredSqMass_sub {A : Type*} [Fintype A] (f d : A → ℝ) :
    centeredSqMass (fun a => f a - d a) =
      centeredSqMass f + centeredSqMass d - 2 * centeredInner f d := by
  rw [show (fun a => f a - d a) = (fun a => f a + (-1) * d a) by
    funext a
    ring]
  rw [centeredSqMass_add, centeredSqMass_smul, centeredInner_smul_right]
  ring

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The symmetric `2+1` profile is three copies of the pair profile with its triple-overlap
removed. -/
theorem exactlyTwoEqualProfile_eq_three_pair_sub_triple (G : Finset F) :
    exactlyTwoEqualProfile G =
      fun t => 3 * (pair01Profile G t - allThreeEqualProfile G t) := by
  funext t
  have hpattern := congrFun (factorialRepetitionDefect_three_eq_pattern_sum G) t
  have hmobius := congrFun (factorialRepetitionDefect_three_eq_mobius G) t
  linarith

/-- Covariance bridge between the disjoint symmetric-pattern coordinates and the signed Möbius
coordinates. -/
theorem exactlyTwo_triple_centeredInner_eq_pair_bridge (G : Finset F) :
    centeredInner (exactlyTwoEqualProfile G) (allThreeEqualProfile G) =
      3 * centeredInner (pair01Profile G) (allThreeEqualProfile G) -
        3 * centeredSqMass (allThreeEqualProfile G) := by
  rw [exactlyTwoEqualProfile_eq_three_pair_sub_triple]
  rw [show (fun t => 3 * (pair01Profile G t - allThreeEqualProfile G t)) =
      (fun t => 3 * pair01Profile G t + (-3) * allThreeEqualProfile G t) by
    funext t
    ring]
  rw [centeredInner_add_left, centeredInner_smul_left, centeredInner_smul_left,
    ← centeredSqMass_eq_inner]
  ring

/-- **Exact centered depth-three Möbius identity.** -/
theorem factorialRepetitionDefect_three_centeredMass_eq_mobius (G : Finset F) :
    centeredSqMass (factorialRepetitionDefect G 3) =
      9 * centeredSqMass (pair01Profile G) +
        4 * centeredSqMass (allThreeEqualProfile G) -
          12 * centeredInner (pair01Profile G) (allThreeEqualProfile G) := by
  rw [factorialRepetitionDefect_three_eq_mobius]
  rw [show (fun t => 3 * pair01Profile G t - 2 * allThreeEqualProfile G t) =
      (fun t => 3 * pair01Profile G t - (2 * allThreeEqualProfile G t)) by rfl]
  rw [centeredSqMass_sub, centeredSqMass_smul, centeredSqMass_smul,
    centeredInner_smul_left, centeredInner_smul_right]
  ring

/-- Positive centered pair/triple correlation gives a strict improvement over the unsigned
`9 V(B) + 4 V(C)` envelope. -/
theorem factorialRepetitionDefect_three_centeredMass_le_mobius_diagonal
    (G : Finset F)
    (hcov : 0 ≤ centeredInner (pair01Profile G) (allThreeEqualProfile G)) :
    centeredSqMass (factorialRepetitionDefect G 3) ≤
      9 * centeredSqMass (pair01Profile G) +
        4 * centeredSqMass (allThreeEqualProfile G) := by
  rw [factorialRepetitionDefect_three_centeredMass_eq_mobius]
  linarith

#print axioms centeredInner_smul_left
#print axioms centeredSqMass_smul
#print axioms centeredSqMass_sub
#print axioms exactlyTwoEqualProfile_eq_three_pair_sub_triple
#print axioms exactlyTwo_triple_centeredInner_eq_pair_bridge
#print axioms factorialRepetitionDefect_three_centeredMass_eq_mobius
#print axioms factorialRepetitionDefect_three_centeredMass_le_mobius_diagonal

end ArkLib.ProximityGap.Frontier.G195DepthThreeCenteredMobius
