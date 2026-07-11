/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G178FactorialContractionSubgroupRefuted

/-!
# G179: unconditional centered transfer with a repetition penalty

G178 refutes a zero-cost centered contraction from with-replacement tuples to distinct subsets.
The valid replacement is a quantitative triangle inequality.  If `R = A + D`, where `A` is the
factorial-normalized distinct profile and `D` is the nonnegative repetition defect, then

`V(A) <= 2 V(R) + 2 |F| (sum D)^2`.

Thus deletion remains usable provided the total repeated-tuple mass is controlled at the relevant
parameter scale.  No covariance sign is assumed.

Issue #466.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G179RepetitionPenaltyTransfer

open scoped BigOperators
open ArkLib.ProximityGap.Frontier.G171ShiftedREnergyAutocorrelation
open ArkLib.ProximityGap.Frontier.G172SubsetSumToREnergy
open ArkLib.ProximityGap.Frontier.G175CenteredDeletionMonotonicityNoGo
open ArkLib.ProximityGap.Frontier.G176RepetitionDefectCovariance
open ArkLib.ProximityGap.Frontier.G177FactorialSubsetFiberAmplification
open ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance

theorem centeredSqMass_nonneg {A : Type*} [Fintype A] (f : A → ℝ) :
    0 ≤ centeredSqMass f := by
  unfold centeredSqMass
  have hcs := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset A)) (f := f)
  exact sub_nonneg.mpr (by simpa only [Finset.card_univ] using hcs)

theorem centeredSqMass_neg {A : Type*} [Fintype A] (f : A → ℝ) :
    centeredSqMass (fun a => -f a) = centeredSqMass f := by
  unfold centeredSqMass
  simp_rw [Finset.sum_neg_distrib]
  ring

theorem centeredInner_neg_right {A : Type*} [Fintype A] (f d : A → ℝ) :
    centeredInner f (fun a => -d a) = -centeredInner f d := by
  unfold centeredInner
  simp_rw [mul_neg, Finset.sum_neg_distrib]
  ring

/-- Centered squared mass obeys the squared triangle inequality with constant two. -/
theorem centeredSqMass_sub_le_two_mul {A : Type*} [Fintype A] (f d : A → ℝ) :
    centeredSqMass (fun a => f a - d a) ≤
      2 * centeredSqMass f + 2 * centeredSqMass d := by
  have hplus := centeredSqMass_nonneg (fun a => f a + d a)
  rw [centeredSqMass_add] at hplus
  have hsub := centeredSqMass_add f (fun a => -d a)
  rw [centeredSqMass_neg, centeredInner_neg_right] at hsub
  have hfun : (fun a => f a + -d a) = (fun a => f a - d a) := by
    funext a
    ring
  rw [hfun] at hsub
  linarith

/-- For a nonnegative profile, its centered mass is at most `|A|` times its squared total mass. -/
theorem centeredSqMass_le_card_mul_sum_sq {A : Type*} [Fintype A] (d : A → ℝ)
    (hd : ∀ a, 0 ≤ d a) :
    centeredSqMass d ≤ (Fintype.card A : ℝ) * (∑ a, d a) ^ 2 := by
  have hsquares : ∑ a, d a ^ 2 ≤ (∑ a, d a) ^ 2 := by
    exact Finset.sum_sq_le_sq_sum_of_nonneg fun a _ => hd a
  have hcard : 0 ≤ (Fintype.card A : ℝ) := Nat.cast_nonneg _
  unfold centeredSqMass
  have hmul := mul_le_mul_of_nonneg_left hsquares hcard
  nlinarith [sq_nonneg (∑ a, d a)]

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

noncomputable def factorialDistinctProfile (G : Finset F) (r : ℕ) : F → ℝ :=
  fun t => (r.factorial * (subsetSumFiber G r t).card : ℕ)

noncomputable def factorialRepetitionDefect (G : Finset F) (r : ℕ) : F → ℝ :=
  fun t => (repR G r t : ℝ) - factorialDistinctProfile G r t

theorem factorialDistinctProfile_le_repR (G : Finset F) (r : ℕ) (t : F) :
    factorialDistinctProfile G r t ≤ (repR G r t : ℝ) := by
  unfold factorialDistinctProfile
  exact_mod_cast
    (factorial_mul_subsetSumFiber_card_le_rSumCount G r t).trans_eq (rSumCount_eq_repR G r t)

theorem factorialRepetitionDefect_nonneg (G : Finset F) (r : ℕ) (t : F) :
    0 ≤ factorialRepetitionDefect G r t := by
  exact sub_nonneg.mpr (factorialDistinctProfile_le_repR G r t)

theorem factorialDistinctProfile_eq_repR_sub_defect (G : Finset F) (r : ℕ) (t : F) :
    factorialDistinctProfile G r t =
      (repR G r t : ℝ) - factorialRepetitionDefect G r t := by
  unfold factorialRepetitionDefect
  ring

theorem sum_rSumCount (G : Finset F) (r : ℕ) :
    ∑ t : F, rSumCount G r t = G.card ^ r := by
  classical
  let P := Fintype.piFinset fun _ : Fin r => G
  have hmaps : ∀ v ∈ P, (∑ i, v i) ∈ (Finset.univ : Finset F) := by simp
  have h := Finset.card_eq_sum_card_fiberwise hmaps
  simpa [P, rSumCount] using h.symm

theorem sum_subsetSumFiber_card (G : Finset F) (r : ℕ) :
    ∑ t : F, (subsetSumFiber G r t).card = G.card.choose r := by
  classical
  have hmaps : ∀ S ∈ G.powersetCard r,
      (∑ x ∈ S, x) ∈ (Finset.univ : Finset F) := by simp
  have h := Finset.card_eq_sum_card_fiberwise hmaps
  simpa [subsetSumFiber, Finset.card_powersetCard] using h.symm

/-- The total factorial-normalized repetition defect is exactly the number of ordered tuples with
a repeated coordinate. -/
theorem sum_factorialRepetitionDefect (G : Finset F) (r : ℕ) :
    ∑ t : F, factorialRepetitionDefect G r t =
      (G.card ^ r : ℝ) - (r.factorial * G.card.choose r : ℕ) := by
  unfold factorialRepetitionDefect factorialDistinctProfile
  simp_rw [Finset.sum_sub_distrib]
  rw [show (∑ t : F, (repR G r t : ℝ)) = (G.card ^ r : ℝ) by
    rw [← Nat.cast_sum]
    exact_mod_cast (by
      simpa only [rSumCount_eq_repR] using sum_rSumCount G r)]
  rw [← Nat.cast_sum]
  norm_cast
  rw [← Finset.mul_sum]
  rw [sum_subsetSumFiber_card]

theorem sum_factorialRepetitionDefect_eq_birthday (G : Finset F) (r : ℕ) :
    ∑ t : F, factorialRepetitionDefect G r t =
      (G.card ^ r : ℝ) - G.card.descFactorial r := by
  rw [sum_factorialRepetitionDefect, Nat.descFactorial_eq_factorial_mul_choose]

/-- **Unconditional deletion transfer.** The failure of centered contraction is isolated in the
explicit total repeated-tuple mass. -/
theorem factorialDistinct_centeredMass_le_with_repetition_penalty (G : Finset F) (r : ℕ) :
    centeredSqMass (factorialDistinctProfile G r) ≤
      2 * centeredSqMass (fun t : F => (repR G r t : ℝ)) +
        2 * (Fintype.card F : ℝ) * (∑ t, factorialRepetitionDefect G r t) ^ 2 := by
  have htriangle := centeredSqMass_sub_le_two_mul
    (fun t : F => (repR G r t : ℝ)) (factorialRepetitionDefect G r)
  have hdefect := centeredSqMass_le_card_mul_sum_sq
    (factorialRepetitionDefect G r) (factorialRepetitionDefect_nonneg G r)
  have hprofile :
      (fun t : F => (repR G r t : ℝ) - factorialRepetitionDefect G r t) =
        factorialDistinctProfile G r := by
    funext t
    exact (factorialDistinctProfile_eq_repR_sub_defect G r t).symm
  rw [hprofile] at htriangle
  linarith

/-- Closed-form version of the unconditional deletion transfer. -/
theorem factorialDistinct_centeredMass_le_explicit_repetition_penalty
    (G : Finset F) (r : ℕ) :
    centeredSqMass (factorialDistinctProfile G r) ≤
      2 * centeredSqMass (fun t : F => (repR G r t : ℝ)) +
        2 * (Fintype.card F : ℝ) *
          ((G.card ^ r : ℝ) - (r.factorial * G.card.choose r : ℕ)) ^ 2 := by
  simpa only [sum_factorialRepetitionDefect] using
    factorialDistinct_centeredMass_le_with_repetition_penalty G r

#print axioms centeredSqMass_sub_le_two_mul
#print axioms centeredSqMass_le_card_mul_sum_sq
#print axioms factorialRepetitionDefect_nonneg
#print axioms sum_factorialRepetitionDefect
#print axioms sum_factorialRepetitionDefect_eq_birthday
#print axioms factorialDistinct_centeredMass_le_with_repetition_penalty
#print axioms factorialDistinct_centeredMass_le_explicit_repetition_penalty

end ArkLib.ProximityGap.Frontier.G179RepetitionPenaltyTransfer
