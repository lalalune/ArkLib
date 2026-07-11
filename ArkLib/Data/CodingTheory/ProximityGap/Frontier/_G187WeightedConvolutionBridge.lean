/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G186WeightedConvolutionYoung

/-!
# G187: exact bridge from the weighted fiber to the doubled convolution

Partition the G185 weighted fiber by its doubled coordinate `x`.  Removing that coordinate leaves
exactly `r-2` ordinary coordinates, so the remaining fiber is `rSumCount G (r-2) (t-2x)`.
Consequently the G185 weighted profile equals G186's doubled convolution pointwise.

Issue #466.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G187WeightedConvolutionBridge

open scoped BigOperators
open ArkLib.ProximityGap.Frontier.G171ShiftedREnergyAutocorrelation
open ArkLib.ProximityGap.Frontier.G175CenteredDeletionMonotonicityNoGo
open ArkLib.ProximityGap.Frontier.G179RepetitionPenaltyTransfer
open ArkLib.ProximityGap.Frontier.G183PairCollisionEnergyReduction
open ArkLib.ProximityGap.Frontier.G184PairCollisionSymmetry
open ArkLib.ProximityGap.Frontier.G185CanonicalWeightedCompression
open ArkLib.ProximityGap.Frontier.G186WeightedConvolutionYoung

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

abbrev Tail (r : ℕ) (hr : 2 ≤ r) :=
  {k : DropOne r hr // k ≠ retainedZero r hr}

theorem card_DropOne (r : ℕ) (hr : 2 ≤ r) : Fintype.card (DropOne r hr) = r - 1 := by
  change Fintype.card {k : Fin r // ¬k = (canonicalPair r hr).2} = r - 1
  rw [Fintype.card_subtype_compl (fun k : Fin r => k = (canonicalPair r hr).2)]
  simp

theorem card_Tail (r : ℕ) (hr : 2 ≤ r) : Fintype.card (Tail r hr) = r - 2 := by
  rw [Fintype.card_subtype_compl (fun k : DropOne r hr => k = retainedZero r hr)]
  rw [card_DropOne]
  simp
  omega

noncomputable def tailEquiv (r : ℕ) (hr : 2 ≤ r) : Fin (r - 2) ≃ Tail r hr :=
  Fintype.equivOfCardEq (by simp [card_Tail r hr])

noncomputable def tailSumFiber (G : Finset F) {r : ℕ} (hr : 2 ≤ r) (a : F) :
    Finset (Tail r hr → F) :=
  (Fintype.piFinset fun _ : Tail r hr => G).filter fun w => ∑ k, w k = a

theorem tailSumFiber_card_eq_rSumCount (G : Finset F) {r : ℕ} (hr : 2 ≤ r) (a : F) :
    (tailSumFiber G hr a).card = rSumCount G (r - 2) a := by
  let e := tailEquiv r hr
  unfold rSumCount
  apply Finset.card_bij (fun w _ i => w (e i))
  · intro w hw
    rw [tailSumFiber, Finset.mem_filter, Fintype.mem_piFinset] at hw
    rw [Finset.mem_filter, Fintype.mem_piFinset]
    refine ⟨fun i => hw.1 (e i), ?_⟩
    simpa [e] using (Equiv.sum_comp e (fun k => w k)).trans hw.2
  · intro w hw z hz heq
    funext k
    have hk := congrFun heq (e.symm k)
    simpa using hk
  · intro v hv
    let w : Tail r hr → F := fun k => v (e.symm k)
    refine ⟨w, ?_, ?_⟩
    · rw [tailSumFiber, Finset.mem_filter, Fintype.mem_piFinset]
      rw [Finset.mem_filter, Fintype.mem_piFinset] at hv
      refine ⟨fun k => hv.1 (e.symm k), ?_⟩
      simpa [w] using (Equiv.sum_comp e.symm (fun i => v i)).trans hv.2
    · funext i
      simp [w]

noncomputable def fixedWeightedFiber (G : Finset F) {r : ℕ} (hr : 2 ≤ r)
    (t x : F) : Finset (DropOne r hr → F) :=
  (weightedPairFiber G hr t).filter fun u => u (retainedZero r hr) = x

noncomputable def restrictTail {r : ℕ} (hr : 2 ≤ r) (u : DropOne r hr → F) :
    Tail r hr → F := fun k => u k.1

noncomputable def expandTail {r : ℕ} (hr : 2 ≤ r) (x : F) (w : Tail r hr → F) :
    DropOne r hr → F := fun k =>
  if h : k = retainedZero r hr then x else w ⟨k, h⟩

theorem sum_expandTail {r : ℕ} (hr : 2 ≤ r) (x : F) (w : Tail r hr → F) :
    ∑ k, expandTail hr x w k = x + ∑ k, w k := by
  rw [Fintype.sum_eq_add_sum_subtype_ne _ (retainedZero r hr)]
  simp only [expandTail, dite_true]
  congr 1
  exact Fintype.sum_congr _ _ fun k => by simp [expandTail, k.2]

theorem fixedWeightedFiber_card_eq_tailSumFiber
    (G : Finset F) {r : ℕ} (hr : 2 ≤ r) (t x : F) (hx : x ∈ G) :
    (fixedWeightedFiber G hr t x).card = (tailSumFiber G hr (t - (x + x))).card := by
  apply Finset.card_bij (fun u _ => restrictTail hr u)
  · intro u hu
    rw [fixedWeightedFiber, Finset.mem_filter, weightedPairFiber,
      Finset.mem_filter, Fintype.mem_piFinset] at hu
    rw [tailSumFiber, Finset.mem_filter, Fintype.mem_piFinset]
    refine ⟨fun k => hu.1.1 k.1, ?_⟩
    unfold weightedSum at hu
    rw [Fintype.sum_eq_add_sum_subtype_ne _ (retainedZero r hr), hu.2] at hu
    rw [eq_sub_iff_add_eq]
    change (∑ k : Tail r hr, u k.1) + (x + x) = t
    convert hu.1.2 using 1 <;> abel
  · intro u hu v hv heq
    rw [fixedWeightedFiber, Finset.mem_filter] at hu hv
    funext k
    by_cases hk : k = retainedZero r hr
    · rw [hk, hu.2, hv.2]
    · have h := congrFun heq ⟨k, hk⟩
      exact h
  · intro w hw
    refine ⟨expandTail hr x w, ?_, ?_⟩
    · rw [fixedWeightedFiber, Finset.mem_filter, weightedPairFiber,
        Finset.mem_filter, Fintype.mem_piFinset]
      rw [tailSumFiber, Finset.mem_filter, Fintype.mem_piFinset] at hw
      refine ⟨⟨?_, ?_⟩, by simp [expandTail]⟩
      · intro k
        by_cases hk : k = retainedZero r hr
        · subst k
          simpa [expandTail] using hx
        · simpa [expandTail, hk] using hw.1 ⟨k, hk⟩
      · unfold weightedSum
        rw [show expandTail hr x w (retainedZero r hr) = x by simp [expandTail],
          sum_expandTail]
        rw [hw.2]
        abel
    · funext k
      simp [restrictTail, expandTail, k.2]

/-- **Exact pointwise convolution bridge.** -/
theorem weightedPairFiber_card_eq_doubledConvolutionCount
    (G : Finset F) {r : ℕ} (hr : 2 ≤ r) (t : F) :
    (weightedPairFiber G hr t).card = doubledConvolutionCount G (r - 2) t := by
  classical
  have hmaps : ∀ u ∈ weightedPairFiber G hr t,
      u (retainedZero r hr) ∈ G := by
    intro u hu
    rw [weightedPairFiber, Finset.mem_filter, Fintype.mem_piFinset] at hu
    exact hu.1 (retainedZero r hr)
  have hpart := Finset.card_eq_sum_card_fiberwise hmaps
  unfold doubledConvolutionCount
  rw [hpart]
  apply Finset.sum_congr rfl
  intro x hx
  rw [show (weightedPairFiber G hr t).filter
      (fun u => u (retainedZero r hr) = x) = fixedWeightedFiber G hr t x by rfl]
  rw [fixedWeightedFiber_card_eq_tailSumFiber G hr t x hx,
    tailSumFiber_card_eq_rSumCount]

/-- Fully compositional unsigned defect bound through ordinary lower-depth additive energy. -/
theorem factorialRepetitionDefect_centeredMass_le_lowerEnergy
    (G : Finset F) {r : ℕ} (hr : 2 ≤ r) :
    centeredSqMass (factorialRepetitionDefect G r) ≤
      (Fintype.card F : ℝ) * (collisionIndices r).card ^ 2 *
        ((G.card : ℝ) ^ 2 * Finset.addREnergy (r - 2) G) := by
  have hweighted := factorialRepetitionDefect_centeredMass_le_weightedPairEnergy G hr
  simp_rw [weightedPairFiber_card_eq_doubledConvolutionCount G hr] at hweighted
  have hyoung := doubledConvolution_energy_le G (r - 2)
  have hnonneg : 0 ≤ (Fintype.card F : ℝ) * (collisionIndices r).card ^ 2 := by positivity
  exact hweighted.trans (mul_le_mul_of_nonneg_left hyoung hnonneg)

#print axioms card_Tail
#print axioms tailSumFiber_card_eq_rSumCount
#print axioms fixedWeightedFiber_card_eq_tailSumFiber
#print axioms weightedPairFiber_card_eq_doubledConvolutionCount
#print axioms factorialRepetitionDefect_centeredMass_le_lowerEnergy

end ArkLib.ProximityGap.Frontier.G187WeightedConvolutionBridge
