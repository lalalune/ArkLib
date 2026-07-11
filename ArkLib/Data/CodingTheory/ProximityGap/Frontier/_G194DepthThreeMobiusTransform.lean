/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G193SymmetricPatternCovarianceRefuted

/-!
# G194: signed depth-three Möbius transform

At depth three, inclusion--exclusion on the equality partition lattice gives

`D₃ = 3 B - 2 C`,

where `B` is one full pair-collision profile and `C` is the all-three-equal profile.  Unlike the
nonnegative pattern split, its centered polarization contains the favorable signed term
`-12 <B,C>_c`.

Issue #466.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G194DepthThreeMobiusTransform

open ArkLib.ProximityGap.Frontier.G175CenteredDeletionMonotonicityNoGo
open ArkLib.ProximityGap.Frontier.G176RepetitionDefectCovariance
open ArkLib.ProximityGap.Frontier.G179RepetitionPenaltyTransfer
open ArkLib.ProximityGap.Frontier.G182AllDepthDefectCarrier
open ArkLib.ProximityGap.Frontier.G183PairCollisionEnergyReduction
open ArkLib.ProximityGap.Frontier.G184PairCollisionSymmetry
open ArkLib.ProximityGap.Frontier.G192DepthThreeSymmetricPatterns

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem injective_fin_three_iff (v : Fin 3 → F) :
    Function.Injective v ↔ v 0 ≠ v 1 ∧ v 0 ≠ v 2 ∧ v 1 ≠ v 2 := by
  constructor
  · intro h
    exact ⟨fun heq => Fin.zero_ne_one (h heq),
      fun heq => (by decide : (0 : Fin 3) ≠ 2) (h heq),
      fun heq => (by decide : (1 : Fin 3) ≠ 2) (h heq)⟩
  · rintro ⟨h01, h02, h12⟩ i j hij
    fin_cases i <;> fin_cases j <;> simp_all

theorem triple_equality_indicator_identity (v : Fin 3 → F) :
    (if ¬Function.Injective v then 1 else 0) +
        2 * (if v 0 = v 1 ∧ v 1 = v 2 then 1 else 0) =
      (if v 0 = v 1 then 1 else 0) + (if v 0 = v 2 then 1 else 0) +
        (if v 1 = v 2 then 1 else 0) := by
  classical
  by_cases h01 : v 0 = v 1 <;> by_cases h02 : v 0 = v 2 <;>
      by_cases h12 : v 1 = v 2
  all_goals simp [h01, h02, h12, injective_fin_three_iff]
  all_goals aesop

theorem allThreeEqual_not_injective {v : Fin 3 → F} (hv : allThreeEqual v) :
    ¬Function.Injective v := by
  intro hinj
  exact Fin.zero_ne_one (hinj hv.1)

theorem repeated_add_two_all_card_eq_sum_pair_cards (G : Finset F) (t : F) :
    (repeatedTupleSumFiber G 3 t).card + 2 * (allThreeEqualFiber G t).card =
      (pairCollisionFiber G 3 t ((0 : Fin 3), (1 : Fin 3))).card +
        (pairCollisionFiber G 3 t ((0 : Fin 3), (2 : Fin 3))).card +
          (pairCollisionFiber G 3 t ((1 : Fin 3), (2 : Fin 3))).card := by
  classical
  let T := tupleSumFiber G 3 t
  have hsum :
      (∑ v ∈ T, ((if ¬Function.Injective v then 1 else 0) +
          2 * (if v 0 = v 1 ∧ v 1 = v 2 then 1 else 0))) =
        ∑ v ∈ T, ((if v 0 = v 1 then 1 else 0) +
          (if v 0 = v 2 then 1 else 0) + (if v 1 = v 2 then 1 else 0)) := by
    exact Finset.sum_congr rfl fun v _ => triple_equality_indicator_identity v
  simp_rw [Finset.sum_add_distrib] at hsum
  simp only [← Finset.mul_sum, Finset.sum_boole] at hsum
  have hall : T.filter (fun v => v 0 = v 1 ∧ v 1 = v 2) = allThreeEqualFiber G t := by
    ext v
    rw [allThreeEqualFiber, repeatedTupleSumFiber]
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hvT, h01, h12⟩
      exact ⟨⟨hvT, allThreeEqual_not_injective ⟨h01, h12⟩⟩, ⟨h01, h12⟩⟩
    · rintro ⟨⟨hvT, _⟩, h01, h12⟩
      exact ⟨hvT, h01, h12⟩
  rw [hall] at hsum
  simpa [T, repeatedTupleSumFiber, pairCollisionFiber] using hsum

noncomputable def pair01Profile (G : Finset F) : F → ℝ :=
  fun t => (pairCollisionFiber G 3 t ((0 : Fin 3), (1 : Fin 3))).card

theorem pairCollisionFiber_three_cards_equal (G : Finset F) (t : F) :
    (pairCollisionFiber G 3 t ((0 : Fin 3), (1 : Fin 3))).card =
      (pairCollisionFiber G 3 t ((0 : Fin 3), (2 : Fin 3))).card ∧
    (pairCollisionFiber G 3 t ((0 : Fin 3), (1 : Fin 3))).card =
      (pairCollisionFiber G 3 t ((1 : Fin 3), (2 : Fin 3))).card := by
  constructor
  · exact pairCollisionFiber_card_eq G 3 t 0 1 0 2 (by decide) (by decide)
  · exact pairCollisionFiber_card_eq G 3 t 0 1 1 2 (by decide) (by decide)

/-- **Pointwise depth-three Möbius identity.** -/
theorem factorialRepetitionDefect_three_eq_mobius (G : Finset F) :
    factorialRepetitionDefect G 3 =
      fun t => 3 * pair01Profile G t - 2 * allThreeEqualProfile G t := by
  funext t
  have hcount := repeated_add_two_all_card_eq_sum_pair_cards G t
  obtain ⟨h02, h12⟩ := pairCollisionFiber_three_cards_equal G t
  unfold pair01Profile allThreeEqualProfile
  rw [← h02, ← h12] at hcount
  rw [factorialRepetitionDefect_eq_repeatedTupleSumFiber_card]
  have hcountR : ((repeatedTupleSumFiber G 3 t).card : ℝ) +
      2 * ((allThreeEqualFiber G t).card : ℝ) =
      ((pairCollisionFiber G 3 t ((0 : Fin 3), (1 : Fin 3))).card : ℝ) +
      ((pairCollisionFiber G 3 t ((0 : Fin 3), (1 : Fin 3))).card : ℝ) +
      ((pairCollisionFiber G 3 t ((0 : Fin 3), (1 : Fin 3))).card : ℝ) := by
    exact_mod_cast hcount
  linarith

#print axioms triple_equality_indicator_identity
#print axioms repeated_add_two_all_card_eq_sum_pair_cards
#print axioms factorialRepetitionDefect_three_eq_mobius

end ArkLib.ProximityGap.Frontier.G194DepthThreeMobiusTransform
