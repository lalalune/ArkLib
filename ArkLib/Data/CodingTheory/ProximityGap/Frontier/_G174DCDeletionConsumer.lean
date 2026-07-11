/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G173AllDepthDeletionREnergy
import ArkLib.Data.CodingTheory.ProximityGap.DCEnergyCorrection

/-!
# G174: DC-subtracted energy consumer for all-depth deletion

G173 bounds the balanced-core census by the **full** energy `E_r`.  The production hypothesis only
controls its DC-subtracted part:

`q E_r - n^(2r) <= q Wick_r`.

This file composes the two statements without discarding the DC spike.  The exact cleared bound is

`q * #cores * C(t,r)^2 <= C(n,t-r)^2 * (n^(2r) + q Wick_r)`.

It also records the spike-dominant regime: if `q Wick_r <= n^(2r)`, the consumer is bounded by
`2 C(n,t-r)^2 n^(2r)`.  Thus the DC hypothesis alone leaves a large diagonal term in this unsigned
core census; eliminating it requires a DC-subtracted/signed deletion census, not a stronger use of
the same full-energy inequality.

Issue #466.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G174DCDeletionConsumer

open ArkLib.ProximityGap.DCEnergyCorrection
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.Frontier.G145LowerDepthMultiplicityEnvelope
open ArkLib.ProximityGap.Frontier.G173AllDepthDeletionREnergy

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def wickTerm (G : Finset F) (r : ℕ) : ℝ :=
  (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r

theorem rEnergy_le_dc_spike_add_wick (G : Finset F) (r : ℕ)
    (hdc : DCEnergyBound G r) :
    (Fintype.card F : ℝ) * (rEnergy G r : ℝ) ≤
      (G.card : ℝ) ^ (2 * r) + (Fintype.card F : ℝ) * wickTerm G r := by
  unfold DCEnergyBound at hdc
  unfold wickTerm
  linarith

/-- **Cleared DC deletion capstone.** -/
theorem subsetCorePairs_dcDeletionBound (G : Finset F) (t r : ℕ)
    (hdc : DCEnergyBound G r) :
    (Fintype.card F : ℝ) *
        ((subsetCorePairs G t).card * (t.choose r) ^ 2 : ℕ) ≤
      ((G.card.choose (t - r)) ^ 2 : ℕ) *
        ((G.card : ℝ) ^ (2 * r) + (Fintype.card F : ℝ) * wickTerm G r) := by
  have hcore := subsetCorePairs_mul_choose_sq_le_choose_sq_mul_rEnergy G t r
  have hcoreR :
      (((subsetCorePairs G t).card * (t.choose r) ^ 2 : ℕ) : ℝ) ≤
        (((G.card.choose (t - r)) ^ 2 : ℕ) : ℝ) * (rEnergy G r : ℝ) := by
    exact_mod_cast hcore
  have hq : (0 : ℝ) ≤ (Fintype.card F : ℝ) := by positivity
  have hchoose : (0 : ℝ) ≤ (((G.card.choose (t - r)) ^ 2 : ℕ) : ℝ) := by positivity
  calc
    (Fintype.card F : ℝ) *
        ((subsetCorePairs G t).card * (t.choose r) ^ 2 : ℕ) ≤
        (Fintype.card F : ℝ) *
          ((((G.card.choose (t - r)) ^ 2 : ℕ) : ℝ) * (rEnergy G r : ℝ)) :=
      mul_le_mul_of_nonneg_left hcoreR hq
    _ = (((G.card.choose (t - r)) ^ 2 : ℕ) : ℝ) *
        ((Fintype.card F : ℝ) * (rEnergy G r : ℝ)) := by ring
    _ ≤ (((G.card.choose (t - r)) ^ 2 : ℕ) : ℝ) *
        ((G.card : ℝ) ^ (2 * r) + (Fintype.card F : ℝ) * wickTerm G r) :=
      mul_le_mul_of_nonneg_left (rEnergy_le_dc_spike_add_wick G r hdc) hchoose
    _ = ((G.card.choose (t - r)) ^ 2 : ℕ) *
        ((G.card : ℝ) ^ (2 * r) + (Fintype.card F : ℝ) * wickTerm G r) := by norm_num

/-- In the production-relevant regime where the DC spike exceeds the Wick allowance, the unsigned
deletion consumer is controlled only at twice the spike scale. -/
theorem subsetCorePairs_dcDeletionBound_of_wick_le_spike (G : Finset F) (t r : ℕ)
    (hdc : DCEnergyBound G r)
    (hspike : (Fintype.card F : ℝ) * wickTerm G r ≤ (G.card : ℝ) ^ (2 * r)) :
    (Fintype.card F : ℝ) *
        ((subsetCorePairs G t).card * (t.choose r) ^ 2 : ℕ) ≤
      2 * (((G.card.choose (t - r)) ^ 2 : ℕ) : ℝ) * (G.card : ℝ) ^ (2 * r) := by
  have hmain := subsetCorePairs_dcDeletionBound G t r hdc
  have hchoose : (0 : ℝ) ≤ (((G.card.choose (t - r)) ^ 2 : ℕ) : ℝ) := by positivity
  calc
    (Fintype.card F : ℝ) *
        ((subsetCorePairs G t).card * (t.choose r) ^ 2 : ℕ) ≤
        (((G.card.choose (t - r)) ^ 2 : ℕ) : ℝ) *
          ((G.card : ℝ) ^ (2 * r) + (Fintype.card F : ℝ) * wickTerm G r) := hmain
    _ ≤ (((G.card.choose (t - r)) ^ 2 : ℕ) : ℝ) *
        (2 * (G.card : ℝ) ^ (2 * r)) := by
      apply mul_le_mul_of_nonneg_left _ hchoose
      linarith
    _ = 2 * (((G.card.choose (t - r)) ^ 2 : ℕ) : ℝ) *
        (G.card : ℝ) ^ (2 * r) := by ring

#print axioms rEnergy_le_dc_spike_add_wick
#print axioms subsetCorePairs_dcDeletionBound
#print axioms subsetCorePairs_dcDeletionBound_of_wick_le_spike

end ArkLib.ProximityGap.Frontier.G174DCDeletionConsumer
