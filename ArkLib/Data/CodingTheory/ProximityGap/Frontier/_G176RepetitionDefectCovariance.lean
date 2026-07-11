/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G175CenteredDeletionMonotonicityNoGo

/-!
# G176: the exact repetition-defect covariance gate

Let `R` be the ordered `r`-tuple sum profile, `A` the distinct `r`-subset sum profile, and
`D = R-A` the repetition defect.  G175 shows that `0 <= A <= R` does not compare centered masses.
The missing signed information is exactly exposed by polarization:

`V(R) = V(A) + V(D) + 2 Cov(A,D)`.

Consequently `V(A) <= V(R)` follows precisely from

`-2 Cov(A,D) <= V(D)`.

This file proves that identity, the sharp sufficient condition, and the concrete nonnegativity of
the repetition defect from G172.  The covariance condition—not fiber domination—is the next honest
deletion-side analytic target.

Issue #466.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G176RepetitionDefectCovariance

open scoped BigOperators
open ArkLib.ProximityGap.Frontier.G171ShiftedREnergyAutocorrelation
open ArkLib.ProximityGap.Frontier.G172SubsetSumToREnergy
open ArkLib.ProximityGap.Frontier.G175CenteredDeletionMonotonicityNoGo
open ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance

def centeredInner {A : Type*} [Fintype A] (f g : A → ℝ) : ℝ :=
  (Fintype.card A : ℝ) * ∑ a, f a * g a - (∑ a, f a) * ∑ a, g a

theorem centeredSqMass_eq_inner {A : Type*} [Fintype A] (f : A → ℝ) :
    centeredSqMass f = centeredInner f f := by
  unfold centeredSqMass centeredInner
  congr 1 <;> simp only [pow_two]

theorem centeredInner_add_left {A : Type*} [Fintype A] (f g h : A → ℝ) :
    centeredInner (fun a => f a + g a) h = centeredInner f h + centeredInner g h := by
  unfold centeredInner
  simp_rw [add_mul, Finset.sum_add_distrib]
  ring

theorem centeredInner_add_right {A : Type*} [Fintype A] (f g h : A → ℝ) :
    centeredInner f (fun a => g a + h a) = centeredInner f g + centeredInner f h := by
  unfold centeredInner
  simp_rw [mul_add, Finset.sum_add_distrib]
  ring

theorem centeredInner_comm {A : Type*} [Fintype A] (f g : A → ℝ) :
    centeredInner f g = centeredInner g f := by
  unfold centeredInner
  simp_rw [mul_comm]

/-- **Exact repetition-defect polarization identity.** -/
theorem centeredSqMass_add {A : Type*} [Fintype A] (f d : A → ℝ) :
    centeredSqMass (fun a => f a + d a) =
      centeredSqMass f + centeredSqMass d + 2 * centeredInner f d := by
  rw [centeredSqMass_eq_inner]
  calc
    centeredInner (fun a => f a + d a) (fun a => f a + d a) =
        centeredInner f (fun a => f a + d a) +
          centeredInner d (fun a => f a + d a) := centeredInner_add_left f d _
    _ = (centeredInner f f + centeredInner f d) +
        (centeredInner d f + centeredInner d d) := by
      rw [centeredInner_add_right f f d, centeredInner_add_right d f d]
    _ = centeredSqMass f + centeredSqMass d + 2 * centeredInner f d := by
      rw [centeredInner_comm d f, centeredSqMass_eq_inner, centeredSqMass_eq_inner]
      ring

/-- **Sharp signed covariance gate.** This is the exact extra condition needed to transfer a
centered bound from `f+d` to `f`. -/
theorem centeredSqMass_le_of_covariance_gate {A : Type*} [Fintype A] (f d : A → ℝ)
    (hcov : -(2 * centeredInner f d) ≤ centeredSqMass d) :
    centeredSqMass f ≤ centeredSqMass (fun a => f a + d a) := by
  rw [centeredSqMass_add]
  linarith

theorem centeredSqMass_le_of_nonneg_covariance {A : Type*} [Fintype A] (f d : A → ℝ)
    (hcov : 0 ≤ centeredInner f d) :
    centeredSqMass f ≤ centeredSqMass (fun a => f a + d a) := by
  apply centeredSqMass_le_of_covariance_gate
  have hvar : 0 ≤ centeredSqMass d := by
    unfold centeredSqMass
    have hcs := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset A)) (f := d)
    exact sub_nonneg.mpr (by simpa only [Finset.card_univ] using hcs)
  linarith

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem rSumCount_eq_repR (G : Finset F) (r : ℕ) (t : F) :
    rSumCount G r t = repR G r t := by
  classical
  unfold rSumCount repR
  rw [Finset.card_filter]

noncomputable def distinctSubsetProfile (G : Finset F) (r : ℕ) : F → ℝ :=
  fun t => (subsetSumFiber G r t).card

noncomputable def repetitionDefect (G : Finset F) (r : ℕ) : F → ℝ :=
  fun t => (repR G r t : ℝ) - distinctSubsetProfile G r t

theorem distinctSubsetProfile_le_repR (G : Finset F) (r : ℕ) (t : F) :
    distinctSubsetProfile G r t ≤ (repR G r t : ℝ) := by
  unfold distinctSubsetProfile
  exact_mod_cast (subsetSumFiber_card_le_rSumCount G r t).trans_eq (rSumCount_eq_repR G r t)

theorem repetitionDefect_nonneg (G : Finset F) (r : ℕ) (t : F) :
    0 ≤ repetitionDefect G r t := by
  unfold repetitionDefect
  exact sub_nonneg.mpr (distinctSubsetProfile_le_repR G r t)

theorem repR_eq_subset_add_defect (G : Finset F) (r : ℕ) (t : F) :
    (repR G r t : ℝ) = distinctSubsetProfile G r t + repetitionDefect G r t := by
  unfold repetitionDefect
  ring

/-- Concrete form of the covariance gate for the distinct-subset deletion profile. -/
theorem distinctSubset_centeredMass_le_repR_of_covariance_gate (G : Finset F) (r : ℕ)
    (hcov : -(2 * centeredInner (distinctSubsetProfile G r) (repetitionDefect G r)) ≤
      centeredSqMass (repetitionDefect G r)) :
    centeredSqMass (distinctSubsetProfile G r) ≤
      centeredSqMass (fun t : F => (repR G r t : ℝ)) := by
  have h := centeredSqMass_le_of_covariance_gate
    (distinctSubsetProfile G r) (repetitionDefect G r) hcov
  convert h using 2
  funext t
  exact repR_eq_subset_add_defect G r t

#print axioms centeredSqMass_add
#print axioms centeredSqMass_le_of_covariance_gate
#print axioms repetitionDefect_nonneg
#print axioms distinctSubset_centeredMass_le_repR_of_covariance_gate

end ArkLib.ProximityGap.Frontier.G176RepetitionDefectCovariance
