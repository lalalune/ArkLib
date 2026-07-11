/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G180DiagonalDefectDispersion

/-!
# G181: the depth-two repetition defect is exactly the diagonal profile

This file closes the bridge left explicit in G180.  At depth two, the ordered tuple fiber splits
into the two orderings of every distinct pair and the diagonal tuples.  Rather than depend on a
canonical-ordering surjectivity proof, we inject those two disjoint sectors into the tuple fiber,
obtain pointwise domination, and upgrade it to equality using G179's exact total defect mass.

Consequently, in odd characteristic, the factorial repetition defect has exact centered mass
`|F||G|-|G|²`, and the G179 transfer pays this linear-mass term instead of the squared birthday
ceiling.

Issue #466.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G181DepthTwoDefectIdentification

open scoped BigOperators
open ArkLib.ProximityGap.Frontier.G171ShiftedREnergyAutocorrelation
open ArkLib.ProximityGap.Frontier.G172SubsetSumToREnergy
open ArkLib.ProximityGap.Frontier.G175CenteredDeletionMonotonicityNoGo
open ArkLib.ProximityGap.Frontier.G176RepetitionDefectCovariance
open ArkLib.ProximityGap.Frontier.G177FactorialSubsetFiberAmplification
open ArkLib.ProximityGap.Frontier.G179RepetitionPenaltyTransfer
open ArkLib.ProximityGap.Frontier.G180DiagonalDefectDispersion
open ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

noncomputable def diagonalFiber (G : Finset F) (t : F) : Finset F :=
  G.filter fun x => x + x = t

noncomputable def depthTwoSectorDomain (G : Finset F) (t : F) :
    Finset (F ⊕ (Σ _S : Finset F, Equiv.Perm (Fin 2))) :=
  (diagonalFiber G t).disjSum (permutedSubsetFiber G 2 t)

noncomputable def depthTwoSectorCode :
    F ⊕ (Σ _S : Finset F, Equiv.Perm (Fin 2)) → (Fin 2 → F)
  | Sum.inl x => fun _ => x
  | Sum.inr z => permutedEnum z

theorem depthTwoSectorCode_maps {G : Finset F} {t : F}
    {z : F ⊕ (Σ _S : Finset F, Equiv.Perm (Fin 2))}
    (hz : z ∈ depthTwoSectorDomain G t) :
    depthTwoSectorCode z ∈
      (Fintype.piFinset fun _ : Fin 2 => G).filter (fun v => ∑ i, v i = t) := by
  classical
  rcases z with x | z
  · have hx : x ∈ diagonalFiber G t := by
      simpa [depthTwoSectorDomain] using hz
    rw [Finset.mem_filter, Fintype.mem_piFinset]
    refine ⟨fun _ => (Finset.mem_filter.mp hx).1, ?_⟩
    simpa [depthTwoSectorCode, Fin.sum_univ_two, two_mul] using
      (Finset.mem_filter.mp hx).2
  · have hz' : z ∈ permutedSubsetFiber G 2 t := by
      simpa [depthTwoSectorDomain] using hz
    exact permutedEnum_maps hz'

theorem depthTwoSectorCode_injOn (G : Finset F) (t : F) :
    Set.InjOn depthTwoSectorCode (↑(depthTwoSectorDomain G t) :
      Set (F ⊕ (Σ _S : Finset F, Equiv.Perm (Fin 2)))) := by
  intro z hz w hw hcode
  change z ∈ depthTwoSectorDomain G t at hz
  change w ∈ depthTwoSectorDomain G t at hw
  rcases z with x | z <;> rcases w with y | w
  · congr
    exact congrFun hcode 0
  · exfalso
    simp only [depthTwoSectorCode] at hcode
    have hwmem : w ∈ permutedSubsetFiber G 2 t := by
      simpa [depthTwoSectorDomain] using hw
    rw [permutedSubsetFiber, Finset.mem_sigma] at hwmem
    have hwcard := (Finset.mem_powersetCard.mp
      (Finset.mem_filter.mp hwmem.1).1).2
    have hinj := (enumSubset_injective hwcard).comp w.2.injective
    have heq : permutedEnum w 0 = permutedEnum w 1 := by
      rw [← congrFun hcode 0, ← congrFun hcode 1]
    exact (by decide : (0 : Fin 2) ≠ 1) (hinj heq)
  · exfalso
    simp only [depthTwoSectorCode] at hcode
    have hzmem : z ∈ permutedSubsetFiber G 2 t := by
      simpa [depthTwoSectorDomain] using hz
    rw [permutedSubsetFiber, Finset.mem_sigma] at hzmem
    have hzcard := (Finset.mem_powersetCard.mp
      (Finset.mem_filter.mp hzmem.1).1).2
    have hinj := (enumSubset_injective hzcard).comp z.2.injective
    have heq : permutedEnum z 0 = permutedEnum z 1 := by
      rw [congrFun hcode 0, congrFun hcode 1]
    exact (by decide : (0 : Fin 2) ≠ 1) (hinj heq)
  · congr
    exact permutedEnum_injOn G 2 t
      (by simpa [depthTwoSectorDomain] using hz)
      (by simpa [depthTwoSectorDomain] using hw) hcode

theorem diagonal_add_factorial_subset_le_rSumCount (G : Finset F) (t : F) :
    (diagonalFiber G t).card + (2 : ℕ).factorial * (subsetSumFiber G 2 t).card ≤
      rSumCount G 2 t := by
  rw [show (2 : ℕ).factorial * (subsetSumFiber G 2 t).card =
      (permutedSubsetFiber G 2 t).card by
    rw [permutedSubsetFiber_card]
    norm_num [Nat.mul_comm]]
  rw [← Finset.card_disjSum]
  exact Finset.card_le_card_of_injOn depthTwoSectorCode
    (fun _ hz => depthTwoSectorCode_maps hz) (depthTwoSectorCode_injOn G t)

theorem diagonalDefectProfile_le_factorialRepetitionDefect (G : Finset F) (t : F) :
    diagonalDefectProfile G t ≤ factorialRepetitionDefect G 2 t := by
  change ((diagonalFiber G t).card : ℝ) ≤ factorialRepetitionDefect G 2 t
  unfold factorialRepetitionDefect factorialDistinctProfile
  rw [← rSumCount_eq_repR]
  have h := diagonal_add_factorial_subset_le_rSumCount G t
  have hr : ((diagonalFiber G t).card : ℝ) +
      2 * ((subsetSumFiber G 2 t).card : ℝ) ≤ (rSumCount G 2 t : ℝ) := by
    exact_mod_cast h
  norm_num
  linarith

theorem sum_diagonalDefectProfile (G : Finset F) :
    ∑ t, diagonalDefectProfile G t = G.card :=
  sum_imageFiberProfile G _

theorem sum_factorialRepetitionDefect_two (G : Finset F) :
    ∑ t, factorialRepetitionDefect G 2 t = G.card := by
  rw [sum_factorialRepetitionDefect]
  by_cases hG : G.card = 0
  · simp [hG]
  · have h1 : 1 ≤ G.card := Nat.one_le_iff_ne_zero.mpr hG
    push_cast
    norm_num
    rw [Nat.cast_choose_two]
    ring

/-- **Exact depth-two profile identification.** -/
theorem factorialRepetitionDefect_two_eq_diagonal (G : Finset F) :
    factorialRepetitionDefect G 2 = diagonalDefectProfile G := by
  funext t
  apply le_antisymm
  · by_contra hnot
    have hstrict : diagonalDefectProfile G t < factorialRepetitionDefect G 2 t :=
      lt_of_not_ge hnot
    have hsumlt : (∑ x : F, diagonalDefectProfile G x) <
        ∑ x : F, factorialRepetitionDefect G 2 x := by
      apply Finset.sum_lt_sum
      · exact fun x _ => diagonalDefectProfile_le_factorialRepetitionDefect G x
      · exact ⟨t, Finset.mem_univ t, hstrict⟩
    rw [sum_diagonalDefectProfile, sum_factorialRepetitionDefect_two] at hsumlt
    exact (lt_irrefl _ hsumlt)
  · exact diagonalDefectProfile_le_factorialRepetitionDefect G t

/-- Exact centered mass of the complete factorial repetition defect at depth two. -/
theorem centeredSqMass_factorialRepetitionDefect_two (G : Finset F)
    (htwo : (2 : F) ≠ 0) :
    centeredSqMass (factorialRepetitionDefect G 2) =
      (Fintype.card F : ℝ) * G.card - G.card ^ 2 := by
  rw [factorialRepetitionDefect_two_eq_diagonal]
  exact centeredSqMass_diagonalDefectProfile G htwo

/-- Improved depth-two deletion transfer with the exact dispersed diagonal cost. -/
theorem factorialDistinct_centeredMass_two_le (G : Finset F) (htwo : (2 : F) ≠ 0) :
    centeredSqMass (factorialDistinctProfile G 2) ≤
      2 * centeredSqMass (fun t : F => (repR G 2 t : ℝ)) +
        2 * ((Fintype.card F : ℝ) * G.card - G.card ^ 2) := by
  have htriangle := centeredSqMass_sub_le_two_mul
    (fun t : F => (repR G 2 t : ℝ)) (factorialRepetitionDefect G 2)
  have hprofile :
      (fun t : F => (repR G 2 t : ℝ) - factorialRepetitionDefect G 2 t) =
        factorialDistinctProfile G 2 := by
    funext t
    exact (factorialDistinctProfile_eq_repR_sub_defect G 2 t).symm
  rw [hprofile, centeredSqMass_factorialRepetitionDefect_two G htwo] at htriangle
  exact htriangle

#print axioms diagonal_add_factorial_subset_le_rSumCount
#print axioms factorialRepetitionDefect_two_eq_diagonal
#print axioms centeredSqMass_factorialRepetitionDefect_two
#print axioms factorialDistinct_centeredMass_two_le

end ArkLib.ProximityGap.Frontier.G181DepthTwoDefectIdentification
