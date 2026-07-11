/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G181DepthTwoDefectIdentification

/-!
# G182: all-depth exact carrier of the factorial repetition defect

For every depth, the ordered tuple sum fiber splits into injective and noninjective words.  The
injective words are exactly all permutations of distinct subsets, not merely a subfamily.  Hence
the G179 factorial repetition defect is pointwise the cardinality of the noninjective tuple fiber.

This removes real subtraction from the defect and gives the canonical finite carrier needed to
partition higher-depth repetitions by equality patterns.

Issue #466.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G182AllDepthDefectCarrier

open scoped BigOperators
open ArkLib.ProximityGap.Frontier.G171ShiftedREnergyAutocorrelation
open ArkLib.ProximityGap.Frontier.G172SubsetSumToREnergy
open ArkLib.ProximityGap.Frontier.G176RepetitionDefectCovariance
open ArkLib.ProximityGap.Frontier.G177FactorialSubsetFiberAmplification
open ArkLib.ProximityGap.Frontier.G179RepetitionPenaltyTransfer
open ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

noncomputable def tupleSumFiber (G : Finset F) (r : ℕ) (t : F) : Finset (Fin r → F) :=
  (Fintype.piFinset fun _ : Fin r => G).filter fun v => ∑ i, v i = t

noncomputable def injectiveTupleSumFiber (G : Finset F) (r : ℕ) (t : F) :
    Finset (Fin r → F) :=
  (tupleSumFiber G r t).filter Function.Injective

noncomputable def repeatedTupleSumFiber (G : Finset F) (r : ℕ) (t : F) :
    Finset (Fin r → F) :=
  (tupleSumFiber G r t).filter fun v => ¬Function.Injective v

theorem tupleSumFiber_card (G : Finset F) (r : ℕ) (t : F) :
    (tupleSumFiber G r t).card = rSumCount G r t := by
  rfl

theorem tupleSumFiber_card_eq_injective_add_repeated (G : Finset F) (r : ℕ) (t : F) :
    (tupleSumFiber G r t).card =
      (injectiveTupleSumFiber G r t).card + (repeatedTupleSumFiber G r t).card := by
  have h := Finset.card_filter_add_card_filter_not
    (s := tupleSumFiber G r t) (p := Function.Injective)
  simpa [injectiveTupleSumFiber, repeatedTupleSumFiber, Nat.add_comm] using h.symm

theorem permutedEnum_mem_injectiveTupleSumFiber {G : Finset F} {r : ℕ} {t : F}
    {z : Σ _S : Finset F, Equiv.Perm (Fin r)} (hz : z ∈ permutedSubsetFiber G r t) :
    permutedEnum z ∈ injectiveTupleSumFiber G r t := by
  rw [injectiveTupleSumFiber, Finset.mem_filter]
  refine ⟨permutedEnum_maps hz, ?_⟩
  rw [permutedSubsetFiber, Finset.mem_sigma] at hz
  have hcard := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hz.1).1).2
  exact (enumSubset_injective hcard).comp z.2.injective

theorem exists_permutedEnum_eq_of_mem_injectiveTupleSumFiber
    {G : Finset F} {r : ℕ} {t : F} {v : Fin r → F}
    (hv : v ∈ injectiveTupleSumFiber G r t) :
    ∃ z ∈ permutedSubsetFiber G r t, permutedEnum z = v := by
  classical
  rw [injectiveTupleSumFiber, Finset.mem_filter, tupleSumFiber,
    Finset.mem_filter, Fintype.mem_piFinset] at hv
  obtain ⟨⟨hvG, hvsum⟩, hvinj⟩ := hv
  let S : Finset F := Finset.univ.image v
  have hScard : S.card = r := by
    change (Finset.univ.image v).card = r
    rw [Finset.card_image_of_injective _ hvinj]
    simp
  have hSsub : S ⊆ G := by
    intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    exact hvG i
  have hSsum : ∑ x ∈ S, x = t := by
    change ∑ x ∈ Finset.univ.image v, x = t
    rw [Finset.sum_image]
    · simpa using hvsum
    · exact fun i _ j _ hij => hvinj hij
  have hSmem : S ∈ subsetSumFiber G r t := by
    rw [subsetSumFiber, Finset.mem_filter, Finset.mem_powersetCard]
    exact ⟨⟨hSsub, hScard⟩, hSsum⟩
  let ev : Fin r ≃ S := Equiv.ofBijective
    (fun i => ⟨v i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩)
    ⟨fun i j hij => hvinj (congrArg Subtype.val hij), fun y => by
      obtain ⟨i, -, hi⟩ := Finset.mem_image.mp y.2
      refine ⟨i, Subtype.ext hi⟩⟩
  let e0 : Fin r ≃ S := (Fin.castOrderIso hScard.symm).toEquiv.trans S.equivFin.symm
  let σ : Equiv.Perm (Fin r) := ev.trans e0.symm
  let z : Σ _S : Finset F, Equiv.Perm (Fin r) := ⟨S, σ⟩
  refine ⟨z, ?_, ?_⟩
  · rw [permutedSubsetFiber, Finset.mem_sigma]
    exact ⟨hSmem, Finset.mem_univ σ⟩
  · funext i
    change enumSubset S r (σ i) = v i
    simp [enumSubset, hScard, σ, e0, ev]

/-- The G177 permutation family is exactly, rather than merely injectively contained in, the
injective ordered tuple fiber. -/
theorem injectiveTupleSumFiber_card (G : Finset F) (r : ℕ) (t : F) :
    (injectiveTupleSumFiber G r t).card =
      r.factorial * (subsetSumFiber G r t).card := by
  have hcard : (permutedSubsetFiber G r t).card =
      (injectiveTupleSumFiber G r t).card := by
    apply Finset.card_bij (fun z _ => permutedEnum z)
    · exact fun z hz => permutedEnum_mem_injectiveTupleSumFiber hz
    · intro z hz w hw heq
      exact permutedEnum_injOn G r t hz hw heq
    · intro v hv
      obtain ⟨z, hz, heq⟩ := exists_permutedEnum_eq_of_mem_injectiveTupleSumFiber hv
      exact ⟨z, hz, heq⟩
  rw [← hcard, permutedSubsetFiber_card, Nat.mul_comm]

theorem rSumCount_eq_factorial_subset_add_repeated (G : Finset F) (r : ℕ) (t : F) :
    rSumCount G r t = r.factorial * (subsetSumFiber G r t).card +
      (repeatedTupleSumFiber G r t).card := by
  rw [← tupleSumFiber_card, tupleSumFiber_card_eq_injective_add_repeated,
    injectiveTupleSumFiber_card]

/-- **All-depth exact defect carrier.** -/
theorem factorialRepetitionDefect_eq_repeatedTupleSumFiber_card
    (G : Finset F) (r : ℕ) (t : F) :
    factorialRepetitionDefect G r t = (repeatedTupleSumFiber G r t).card := by
  unfold factorialRepetitionDefect factorialDistinctProfile
  rw [← rSumCount_eq_repR, rSumCount_eq_factorial_subset_add_repeated]
  push_cast
  ring

#print axioms exists_permutedEnum_eq_of_mem_injectiveTupleSumFiber
#print axioms injectiveTupleSumFiber_card
#print axioms rSumCount_eq_factorial_subset_add_repeated
#print axioms factorialRepetitionDefect_eq_repeatedTupleSumFiber_card

end ArkLib.ProximityGap.Frontier.G182AllDepthDefectCarrier
