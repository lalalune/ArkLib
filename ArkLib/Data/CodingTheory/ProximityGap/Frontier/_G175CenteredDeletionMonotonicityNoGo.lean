/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G174DCDeletionConsumer
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R240GeneralRFoldVariance

/-!
# G175: centered deletion monotonicity no-go

The DC-subtracted energy is the centered square mass

`q * sum R(t)^2 - (sum R(t))^2`.

G172 gives pointwise domination of distinct-subset fibers by tuple fibers.  A tempting next step is
to center both profiles and transfer the DC bound by monotonicity.  This is false in the smallest
possible example: on a two-point space, `(1,0) <= (1,1)` coordinatewise, but their centered square
masses are respectively `1` and `0`.

Thus neither G172's injection nor any coordinatewise fiber cap can by itself transport
`DCEnergyBound` to a DC-subtracted deletion census.  One needs a signed correlation/discrepancy
relation between the two profiles, not mere domination.

Issue #466.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G175CenteredDeletionMonotonicityNoGo

open scoped BigOperators
open ArkLib.ProximityGap.DCEnergyCorrection
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance

def centeredSqMass {A : Type*} [Fintype A] (f : A → ℝ) : ℝ :=
  (Fintype.card A : ℝ) * ∑ a, f a ^ 2 - (∑ a, f a) ^ 2

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The DC numerator is exactly the centered square mass of the representation profile. -/
theorem centeredSqMass_repR (G : Finset F) (r : ℕ) :
    centeredSqMass (fun c : F => (repR G r c : ℝ)) =
      (Fintype.card F : ℝ) * (rEnergy G r : ℝ) - (G.card : ℝ) ^ (2 * r) := by
  unfold centeredSqMass
  have hE := rEnergy_eq_sum_repR_sq G r
  have hmass := sum_repR G r
  have hER : (∑ c : F, (repR G r c : ℝ) ^ 2) = (rEnergy G r : ℝ) := by
    exact_mod_cast hE.symm
  have hmassR : (∑ c : F, (repR G r c : ℝ)) = (G.card : ℝ) ^ r := by
    exact_mod_cast hmass
  rw [hER, hmassR, pow_two, ← pow_add]
  congr 2
  omega

theorem dcEnergyBound_iff_centeredSqMass (G : Finset F) (r : ℕ) :
    DCEnergyBound G r ↔
      centeredSqMass (fun c : F => (repR G r c : ℝ)) ≤
        (Fintype.card F : ℝ) *
          ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r) := by
  rw [centeredSqMass_repR]
  rfl

def spikeProfile : Fin 2 → ℝ := fun i => if i = 0 then 1 else 0

def flatProfile : Fin 2 → ℝ := fun _ => 1

theorem spikeProfile_le_flatProfile : ∀ i, 0 ≤ spikeProfile i ∧ spikeProfile i ≤ flatProfile i := by
  intro i
  fin_cases i <;> norm_num [spikeProfile, flatProfile]

theorem centeredSqMass_spikeProfile : centeredSqMass spikeProfile = 1 := by
  norm_num [centeredSqMass, spikeProfile]

theorem centeredSqMass_flatProfile : centeredSqMass flatProfile = 0 := by
  norm_num [centeredSqMass, flatProfile]

def CenteredMassMonotone : Prop :=
  ∀ f g : Fin 2 → ℝ, (∀ i, 0 ≤ f i ∧ f i ≤ g i) → centeredSqMass f ≤ centeredSqMass g

/-- **Centered monotonicity is false.** Coordinatewise fiber domination does not transfer a
DC-subtracted energy bound. -/
theorem not_centeredMassMonotone : ¬ CenteredMassMonotone := by
  intro h
  have := h spikeProfile flatProfile spikeProfile_le_flatProfile
  rw [centeredSqMass_spikeProfile, centeredSqMass_flatProfile] at this
  norm_num at this

#print axioms centeredSqMass_repR
#print axioms dcEnergyBound_iff_centeredSqMass
#print axioms not_centeredMassMonotone

end ArkLib.ProximityGap.Frontier.G175CenteredDeletionMonotonicityNoGo
