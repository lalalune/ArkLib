/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G183PairCollisionEnergyReduction

/-!
# G184: pair-collision symmetry and canonical energy reduction

Coordinate permutations preserve tuple sums and transport any ordered colliding pair to any other.
Consequently every pair-collision fiber in G183 has the same cardinality.  At depth at least two,
the full pair-energy sum collapses to the energy of the canonical pair `(0,1)`.

Issue #466.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G184PairCollisionSymmetry

open scoped BigOperators
open ArkLib.ProximityGap.Frontier.G175CenteredDeletionMonotonicityNoGo
open ArkLib.ProximityGap.Frontier.G179RepetitionPenaltyTransfer
open ArkLib.ProximityGap.Frontier.G182AllDepthDefectCarrier
open ArkLib.ProximityGap.Frontier.G183PairCollisionEnergyReduction

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The symmetric group is two-transitive on ordered pairs of distinct points. -/
def pairTransportPerm {α : Type*} [DecidableEq α]
    (i j i' j' : α) (hij : i ≠ j) (hij' : i' ≠ j') : Equiv.Perm α :=
  let τ := Equiv.swap i i'
  τ.trans (Equiv.swap (τ j) j')

theorem pairTransportPerm_apply_fst {α : Type*} [DecidableEq α]
    (i j i' j' : α) (hij : i ≠ j) (hij' : i' ≠ j') :
    pairTransportPerm i j i' j' hij hij' i = i' := by
  unfold pairTransportPerm
  simp only [Equiv.coe_trans, Function.comp_apply, Equiv.swap_apply_left]
  rw [Equiv.swap_apply_of_ne_of_ne]
  · intro h
    apply hij
    apply (Equiv.swap i i').injective
    simpa using h
  · exact hij'

theorem pairTransportPerm_apply_snd {α : Type*} [DecidableEq α]
    (i j i' j' : α) (hij : i ≠ j) (hij' : i' ≠ j') :
    pairTransportPerm i j i' j' hij hij' j = j' := by
  unfold pairTransportPerm
  simp

noncomputable def reindexTuple {r : ℕ} (σ : Equiv.Perm (Fin r))
    (v : Fin r → F) : Fin r → F := fun k => v (σ.symm k)

theorem reindexTuple_sum {r : ℕ} (σ : Equiv.Perm (Fin r)) (v : Fin r → F) :
    ∑ k, reindexTuple σ v k = ∑ k, v k := by
  unfold reindexTuple
  exact Equiv.sum_comp σ.symm v

theorem reindexTuple_mem_piFinset_iff {G : Finset F} {r : ℕ}
    (σ : Equiv.Perm (Fin r)) (v : Fin r → F) :
    reindexTuple σ v ∈ Fintype.piFinset (fun _ : Fin r => G) ↔
      v ∈ Fintype.piFinset (fun _ : Fin r => G) := by
  simp only [Fintype.mem_piFinset, reindexTuple]
  constructor
  · intro h k
    simpa using h (σ k)
  · intro h k
    exact h (σ.symm k)

theorem reindexTuple_injective {r : ℕ} (σ : Equiv.Perm (Fin r)) :
    Function.Injective (reindexTuple (F := F) σ) := by
  intro v w h
  funext k
  have hk := congrFun h (σ k)
  simpa [reindexTuple] using hk

theorem reindexTuple_pairCollision_maps_of_apply {G : Finset F} {r : ℕ} {t : F}
    {i j i' j' : Fin r} (σ : Equiv.Perm (Fin r))
    (hi : σ i = i') (hj : σ j = j')
    {v : Fin r → F} (hv : v ∈ pairCollisionFiber G r t (i, j)) :
    reindexTuple σ v ∈ pairCollisionFiber G r t (i', j') := by
  rw [pairCollisionFiber, Finset.mem_filter] at hv ⊢
  rw [tupleSumFiber, Finset.mem_filter] at hv ⊢
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact (reindexTuple_mem_piFinset_iff _ _).mpr hv.1.1
  · rw [reindexTuple_sum]
    exact hv.1.2
  · change v (σ.symm i') = v (σ.symm j')
    rw [← hi, ← hj, σ.symm_apply_apply, σ.symm_apply_apply]
    exact hv.2

theorem reindexTuple_pairCollision_maps {G : Finset F} {r : ℕ} {t : F}
    {i j i' j' : Fin r} (hij : i ≠ j) (hij' : i' ≠ j')
    {v : Fin r → F} (hv : v ∈ pairCollisionFiber G r t (i, j)) :
    reindexTuple (pairTransportPerm i j i' j' hij hij') v ∈
      pairCollisionFiber G r t (i', j') := by
  apply reindexTuple_pairCollision_maps_of_apply
    (pairTransportPerm i j i' j' hij hij')
    (pairTransportPerm_apply_fst i j i' j' hij hij')
    (pairTransportPerm_apply_snd i j i' j' hij hij') hv

/-- Coordinate symmetry of every pair-collision fiber. -/
theorem pairCollisionFiber_card_eq (G : Finset F) (r : ℕ) (t : F)
    (i j i' j' : Fin r) (hij : i ≠ j) (hij' : i' ≠ j') :
    (pairCollisionFiber G r t (i, j)).card =
      (pairCollisionFiber G r t (i', j')).card := by
  let σ := pairTransportPerm i j i' j' hij hij'
  apply Finset.card_bij (fun v _ => reindexTuple σ v)
  · exact fun v hv => reindexTuple_pairCollision_maps hij hij' hv
  · intro v hv w hw heq
    exact reindexTuple_injective σ heq
  · intro w hw
    refine ⟨reindexTuple σ.symm w, ?_, ?_⟩
    · apply reindexTuple_pairCollision_maps_of_apply σ.symm
        (by rw [Equiv.symm_apply_eq]; exact (pairTransportPerm_apply_fst i j i' j' hij hij').symm)
        (by rw [Equiv.symm_apply_eq]; exact (pairTransportPerm_apply_snd i j i' j' hij hij').symm) hw
    · funext k
      simp [reindexTuple]

def canonicalPair (r : ℕ) (hr : 2 ≤ r) : Fin r × Fin r :=
  (⟨0, by omega⟩, ⟨1, by omega⟩)

theorem canonicalPair_ne (r : ℕ) (hr : 2 ≤ r) :
    (canonicalPair r hr).1 ≠ (canonicalPair r hr).2 := by
  simp [canonicalPair]

theorem sum_pairCollisionFiber_sq_eq_card_mul_canonical
    (G : Finset F) {r : ℕ} (hr : 2 ≤ r) (t : F) :
    ∑ ij ∈ collisionIndices r, ((pairCollisionFiber G r t ij).card : ℝ) ^ 2 =
      ((collisionIndices r).card : ℝ) *
        ((pairCollisionFiber G r t (canonicalPair r hr)).card : ℝ) ^ 2 := by
  calc
    _ = ∑ _ij ∈ collisionIndices r,
        ((pairCollisionFiber G r t (canonicalPair r hr)).card : ℝ) ^ 2 := by
      apply Finset.sum_congr rfl
      intro ij hij
      rw [collisionIndices, Finset.mem_filter] at hij
      rw [pairCollisionFiber_card_eq G r t ij.1 ij.2
        (canonicalPair r hr).1 (canonicalPair r hr).2 hij.2 (canonicalPair_ne r hr)]
    _ = _ := by simp

/-- **Canonical pair-energy capstone.** -/
theorem factorialRepetitionDefect_centeredMass_le_canonicalPairEnergy
    (G : Finset F) {r : ℕ} (hr : 2 ≤ r) :
    centeredSqMass (factorialRepetitionDefect G r) ≤
      (Fintype.card F : ℝ) * (collisionIndices r).card ^ 2 *
        ∑ t : F, ((pairCollisionFiber G r t (canonicalPair r hr)).card : ℝ) ^ 2 := by
  have h := factorialRepetitionDefect_centeredMass_le_pairCollisionEnergy G r
  simp_rw [sum_pairCollisionFiber_sq_eq_card_mul_canonical G hr] at h
  rw [← Finset.mul_sum] at h
  convert h using 1 <;> ring

#print axioms pairTransportPerm_apply_fst
#print axioms pairCollisionFiber_card_eq
#print axioms sum_pairCollisionFiber_sq_eq_card_mul_canonical
#print axioms factorialRepetitionDefect_centeredMass_le_canonicalPairEnergy

end ArkLib.ProximityGap.Frontier.G184PairCollisionSymmetry
