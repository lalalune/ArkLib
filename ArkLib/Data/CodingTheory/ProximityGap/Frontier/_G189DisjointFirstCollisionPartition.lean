/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G188ExplicitDefectDCBarrier

/-!
# G189: disjoint first-collision partition of the repetition defect

The G183 pair cover counts a tuple once for every equal coordinate pair.  Here we order the pair
indices and assign each noninjective tuple its least witnessing pair.  The resulting strata are
pairwise disjoint and partition the exact G182 repeated carrier pointwise.

This removes the overlap loss entirely.  Any remaining loss in bounding the sum of stratum profiles
is therefore an analytic cross-covariance issue, not combinatorial multiple counting.

Issue #466.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G189DisjointFirstCollisionPartition

open scoped BigOperators
open ArkLib.ProximityGap.Frontier.G179RepetitionPenaltyTransfer
open ArkLib.ProximityGap.Frontier.G182AllDepthDefectCarrier
open ArkLib.ProximityGap.Frontier.G183PairCollisionEnergyReduction
open ArkLib.ProximityGap.Frontier.G184PairCollisionSymmetry

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def collisionWitnesses {r : ℕ} (v : Fin r → F) : Finset (Fin r ×ₗ Fin r) :=
  ((collisionIndices r).image toLex).filter fun ij =>
    v (ofLex ij).1 = v (ofLex ij).2

theorem collisionWitnesses_nonempty_of_not_injective {r : ℕ} {v : Fin r → F}
    (hv : ¬Function.Injective v) : (collisionWitnesses v).Nonempty := by
  obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hv
  refine ⟨toLex (i, j), ?_⟩
  rw [collisionWitnesses, Finset.mem_filter]
  refine ⟨Finset.mem_image.mpr ⟨(i, j), ?_, rfl⟩, hij⟩
  rw [collisionIndices, Finset.mem_filter, Finset.mem_product]
  exact ⟨⟨Finset.mem_univ i, Finset.mem_univ j⟩, hne⟩

noncomputable def firstCollision {r : ℕ} (hr : 2 ≤ r) (v : Fin r → F) : Fin r × Fin r :=
  if h : (collisionWitnesses v).Nonempty then ofLex ((collisionWitnesses v).min' h)
  else canonicalPair r hr

theorem firstCollision_mem_witnesses {r : ℕ} (hr : 2 ≤ r) {v : Fin r → F}
    (hv : ¬Function.Injective v) : toLex (firstCollision hr v) ∈ collisionWitnesses v := by
  unfold firstCollision
  rw [dif_pos (collisionWitnesses_nonempty_of_not_injective hv)]
  simpa using Finset.min'_mem _ _

theorem firstCollision_mem_collisionIndices {r : ℕ} (hr : 2 ≤ r) {v : Fin r → F}
    (hv : ¬Function.Injective v) : firstCollision hr v ∈ collisionIndices r := by
  have h := (Finset.mem_filter.mp (firstCollision_mem_witnesses hr hv)).1
  obtain ⟨ij, hij, heq⟩ := Finset.mem_image.mp h
  have hpair : ij = firstCollision hr v := by
    simpa using congrArg ofLex heq
  simpa [← hpair] using hij

theorem firstCollision_witnesses_eq {r : ℕ} (hr : 2 ≤ r) {v : Fin r → F}
    (hv : ¬Function.Injective v) :
    v (firstCollision hr v).1 = v (firstCollision hr v).2 := by
  simpa using (Finset.mem_filter.mp (firstCollision_mem_witnesses hr hv)).2

noncomputable def firstCollisionFiber (G : Finset F) {r : ℕ} (hr : 2 ≤ r)
    (t : F) (ij : Fin r × Fin r) : Finset (Fin r → F) :=
  (repeatedTupleSumFiber G r t).filter fun v => firstCollision hr v = ij

theorem firstCollisionFiber_pairwise_disjoint (G : Finset F) {r : ℕ} (hr : 2 ≤ r)
    (t : F) {ij kl : Fin r × Fin r} (hne : ij ≠ kl) :
    Disjoint (firstCollisionFiber G hr t ij) (firstCollisionFiber G hr t kl) := by
  rw [Finset.disjoint_left]
  intro v hvij hvkl
  rw [firstCollisionFiber, Finset.mem_filter] at hvij hvkl
  exact hne (hvij.2.symm.trans hvkl.2)

/-- **Exact pointwise disjoint partition.** -/
theorem repeatedTupleSumFiber_card_eq_sum_firstCollisionFiber
    (G : Finset F) {r : ℕ} (hr : 2 ≤ r) (t : F) :
    (repeatedTupleSumFiber G r t).card =
      ∑ ij ∈ collisionIndices r, (firstCollisionFiber G hr t ij).card := by
  have hmaps : ∀ v ∈ repeatedTupleSumFiber G r t,
      firstCollision hr v ∈ collisionIndices r := by
    intro v hv
    rw [repeatedTupleSumFiber, Finset.mem_filter] at hv
    exact firstCollision_mem_collisionIndices hr hv.2
  have h := Finset.card_eq_sum_card_fiberwise hmaps
  simpa [firstCollisionFiber] using h

noncomputable def firstCollisionProfile (G : Finset F) {r : ℕ} (hr : 2 ≤ r)
    (ij : Fin r × Fin r) : F → ℝ :=
  fun t => (firstCollisionFiber G hr t ij).card

/-- The factorial repetition defect is exactly the sum of the disjoint first-collision profiles. -/
theorem factorialRepetitionDefect_eq_sum_firstCollisionProfile
    (G : Finset F) {r : ℕ} (hr : 2 ≤ r) (t : F) :
    factorialRepetitionDefect G r t =
      ∑ ij ∈ collisionIndices r, firstCollisionProfile G hr ij t := by
  rw [factorialRepetitionDefect_eq_repeatedTupleSumFiber_card,
    repeatedTupleSumFiber_card_eq_sum_firstCollisionFiber G hr t]
  push_cast
  rfl

#print axioms firstCollision_mem_witnesses
#print axioms firstCollisionFiber_pairwise_disjoint
#print axioms repeatedTupleSumFiber_card_eq_sum_firstCollisionFiber
#print axioms factorialRepetitionDefect_eq_sum_firstCollisionProfile

end ArkLib.ProximityGap.Frontier.G189DisjointFirstCollisionPartition
