/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G166EvenDepthSignedSectorEmpty
import Mathlib.Data.Finset.Sigma

/-!
# G167: marked deletion bound for minimal zero-sum supports

Mark one element `x` in a zero-sum `t`-subset `S` and delete it.  The remaining support determines
the missing element uniquely as minus its sum.  Hence marked zero-sum supports inject into
ordinary `(t-1)`-subsets of the ambient set.

Since every support has exactly `t` possible marks, this gives

`t * #minimalZeroSumSupports(G,t) ≤ C(|G|, t-1)`.

Via G162/G165 this is an unconditional one-power ambient saving for the sole exceptional
signed-swap primitive residue sector at odd depths.

Issue #466.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G167MinimalZeroSumDeletionBound

open scoped BigOperators
open ArkLib.ProximityGap.Frontier.G162SignedSwapMinimalZeroSum
open ArkLib.ProximityGap.Frontier.G165PrimitiveModFourResidue

variable {F : Type*} [AddCommGroup F] [Fintype F] [DecidableEq F]

noncomputable def markedMinimalZeroSumSupports (G : Finset F) (t : ℕ) :
    Finset (Σ _S : Finset F, F) :=
  (minimalZeroSumSupports G t).sigma fun S => S

def deleteMark (z : Σ _S : Finset F, F) : Finset F := z.1.erase z.2

theorem mem_markedMinimalZeroSumSupports_iff {G : Finset F} {t : ℕ}
    {z : Σ _S : Finset F, F} :
    z ∈ markedMinimalZeroSumSupports G t ↔
      z.1 ∈ minimalZeroSumSupports G t ∧ z.2 ∈ z.1 := by
  classical
  simp [markedMinimalZeroSumSupports]

theorem deleteMark_mem_powersetCard {G : Finset F} {t : ℕ}
    {z : Σ _S : Finset F, F} (hz : z ∈ markedMinimalZeroSumSupports G t) :
    deleteMark z ∈ G.powersetCard (t - 1) := by
  classical
  rw [mem_markedMinimalZeroSumSupports_iff] at hz
  obtain ⟨hzS, hzx⟩ := hz
  rw [minimalZeroSumSupports, Finset.mem_filter] at hzS
  obtain ⟨hSpow, hmin⟩ := hzS
  rw [Finset.mem_powersetCard]
  refine ⟨(Finset.erase_subset _ _).trans (Finset.mem_powersetCard.mp hSpow).1, ?_⟩
  rw [deleteMark, Finset.card_erase_of_mem hzx, (Finset.mem_powersetCard.mp hSpow).2]

theorem mark_eq_neg_sum_delete {G : Finset F} {t : ℕ}
    {z : Σ _S : Finset F, F} (hz : z ∈ markedMinimalZeroSumSupports G t) :
    z.2 = -(∑ y ∈ deleteMark z, y) := by
  classical
  rw [mem_markedMinimalZeroSumSupports_iff] at hz
  obtain ⟨hzS, hzx⟩ := hz
  rw [minimalZeroSumSupports, Finset.mem_filter] at hzS
  have hzero := hzS.2.2.1
  have hsplit := Finset.sum_erase_add (s := z.1) (f := fun y : F => y) hzx
  apply eq_neg_of_add_eq_zero_right
  simpa [deleteMark] using hsplit.trans hzero

/-- The marked deletion code is injective: the deleted support recovers both the mark and the
original support. -/
theorem deleteMark_injOn (G : Finset F) (t : ℕ) :
    Set.InjOn deleteMark
      (↑(markedMinimalZeroSumSupports G t) : Set (Σ _S : Finset F, F)) := by
  intro z hz w hw hdel
  have hmark : z.2 = w.2 := by
    rw [mark_eq_neg_sum_delete hz, mark_eq_neg_sum_delete hw, hdel]
  have hset : z.1 = w.1 := by
    have hzmem := (mem_markedMinimalZeroSumSupports_iff.mp hz).2
    have hwmem := (mem_markedMinimalZeroSumSupports_iff.mp hw).2
    calc
      z.1 = insert z.2 (deleteMark z) :=
        (Finset.insert_erase hzmem).symm
      _ = insert w.2 (deleteMark w) := by rw [hmark, hdel]
      _ = w.1 := Finset.insert_erase hwmem
  exact Sigma.ext hset (heq_of_eq hmark)

theorem markedMinimalZeroSumSupports_card (G : Finset F) (t : ℕ) :
    (markedMinimalZeroSumSupports G t).card =
      (minimalZeroSumSupports G t).card * t := by
  classical
  rw [markedMinimalZeroSumSupports]
  rw [Finset.card_sigma]
  calc
    (∑ S ∈ minimalZeroSumSupports G t, S.card) =
        ∑ _S ∈ minimalZeroSumSupports G t, t := by
      apply Finset.sum_congr rfl
      intro S hS
      rw [minimalZeroSumSupports, Finset.mem_filter] at hS
      exact (Finset.mem_powersetCard.mp hS.1).2
    _ = (minimalZeroSumSupports G t).card * t := by simp

/-- **G167 capstone.** Marked deletion gives a one-power ambient saving for minimal zero-sum
supports. -/
theorem minimalZeroSumSupports_mul_le_choose (G : Finset F) (t : ℕ) :
    (minimalZeroSumSupports G t).card * t ≤ G.card.choose (t - 1) := by
  rw [← markedMinimalZeroSumSupports_card]
  calc
    (markedMinimalZeroSumSupports G t).card ≤ (G.powersetCard (t - 1)).card :=
      Finset.card_le_card_of_injOn deleteMark
        (fun _ hz => deleteMark_mem_powersetCard hz) (deleteMark_injOn G t)
    _ = G.card.choose (t - 1) := Finset.card_powersetCard (t - 1) G

/-- The signed primitive residue inherits the same binomial deletion bound. -/
theorem signedFixedPrimitiveCorePairs_mul_le_choose
    (htwo : ∀ z : F, z + z = 0 → z = 0) (G : Finset F) (t : ℕ) :
    (signedFixedPrimitiveCorePairs G t).card * t ≤ G.card.choose (t - 1) :=
  (Nat.mul_le_mul_right t
    (signedFixedPrimitiveCorePairs_card_le_minimalZeroSumSupports htwo G t)).trans
    (minimalZeroSumSupports_mul_le_choose G t)

#print axioms deleteMark_injOn
#print axioms markedMinimalZeroSumSupports_card
#print axioms minimalZeroSumSupports_mul_le_choose
#print axioms signedFixedPrimitiveCorePairs_mul_le_choose

end ArkLib.ProximityGap.Frontier.G167MinimalZeroSumDeletionBound
