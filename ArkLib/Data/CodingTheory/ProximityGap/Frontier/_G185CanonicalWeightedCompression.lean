/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G184PairCollisionSymmetry

/-!
# G185: canonical pair collisions are weighted lower-dimensional sums

Delete coordinate `1` from the canonical collision fiber `v 0 = v 1`.  Re-inserting it as a copy
of coordinate `0` is inverse to restriction, and the sum becomes

`2 x₀ + x₂ + ... + x_{r-1}`.

We use the subtype of coordinates unequal to `1` as the robust `(r-1)`-coordinate domain.  This
file proves an exact fiber bijection and rewrites G184's defect bound as the energy of one explicit
weighted profile.

Issue #466.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G185CanonicalWeightedCompression

open scoped BigOperators
open ArkLib.ProximityGap.Frontier.G175CenteredDeletionMonotonicityNoGo
open ArkLib.ProximityGap.Frontier.G179RepetitionPenaltyTransfer
open ArkLib.ProximityGap.Frontier.G182AllDepthDefectCarrier
open ArkLib.ProximityGap.Frontier.G183PairCollisionEnergyReduction
open ArkLib.ProximityGap.Frontier.G184PairCollisionSymmetry

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

abbrev DropOne (r : ℕ) (hr : 2 ≤ r) :=
  {k : Fin r // k ≠ (canonicalPair r hr).2}

def retainedZero (r : ℕ) (hr : 2 ≤ r) : DropOne r hr :=
  ⟨(canonicalPair r hr).1, canonicalPair_ne r hr⟩

noncomputable def weightedSum {r : ℕ} (hr : 2 ≤ r) (u : DropOne r hr → F) : F :=
  u (retainedZero r hr) + ∑ k, u k

noncomputable def weightedPairFiber (G : Finset F) {r : ℕ} (hr : 2 ≤ r) (t : F) :
    Finset (DropOne r hr → F) :=
  (Fintype.piFinset fun _ : DropOne r hr => G).filter fun u => weightedSum hr u = t

noncomputable def restrictTuple {r : ℕ} (hr : 2 ≤ r) (v : Fin r → F) :
    DropOne r hr → F := fun k => v k.1

noncomputable def expandTuple {r : ℕ} (hr : 2 ≤ r) (u : DropOne r hr → F) :
    Fin r → F := fun k =>
  if h : k = (canonicalPair r hr).2 then u (retainedZero r hr) else u ⟨k, h⟩

theorem expandTuple_at_fst {r : ℕ} (hr : 2 ≤ r) (u : DropOne r hr → F) :
    expandTuple hr u (canonicalPair r hr).1 = u (retainedZero r hr) := by
  simp [expandTuple, retainedZero, canonicalPair_ne]

theorem expandTuple_at_snd {r : ℕ} (hr : 2 ≤ r) (u : DropOne r hr → F) :
    expandTuple hr u (canonicalPair r hr).2 = u (retainedZero r hr) := by
  simp [expandTuple]

theorem restrictTuple_expandTuple {r : ℕ} (hr : 2 ≤ r) (u : DropOne r hr → F) :
    restrictTuple hr (expandTuple hr u) = u := by
  funext k
  simp [restrictTuple, expandTuple, k.2]

theorem expandTuple_restrictTuple_of_collision {r : ℕ} (hr : 2 ≤ r) (v : Fin r → F)
    (hcollision : v (canonicalPair r hr).1 = v (canonicalPair r hr).2) :
    expandTuple hr (restrictTuple hr v) = v := by
  funext k
  by_cases hk : k = (canonicalPair r hr).2
  · subst k
    simp [expandTuple, restrictTuple, retainedZero, hcollision]
  · simp [expandTuple, restrictTuple, hk]

theorem sum_expandTuple {r : ℕ} (hr : 2 ≤ r) (u : DropOne r hr → F) :
    ∑ k, expandTuple hr u k = weightedSum hr u := by
  rw [Fintype.sum_eq_add_sum_subtype_ne _ (canonicalPair r hr).2]
  unfold weightedSum
  rw [expandTuple_at_snd]
  congr 1
  exact Fintype.sum_congr _ _ fun k => by simp [expandTuple, k.2]

theorem restrictTuple_mem_weightedPairFiber {G : Finset F} {r : ℕ} (hr : 2 ≤ r) {t : F}
    {v : Fin r → F} (hv : v ∈ pairCollisionFiber G r t (canonicalPair r hr)) :
    restrictTuple hr v ∈ weightedPairFiber G hr t := by
  rw [pairCollisionFiber, Finset.mem_filter, tupleSumFiber,
    Finset.mem_filter, Fintype.mem_piFinset] at hv
  rw [weightedPairFiber, Finset.mem_filter, Fintype.mem_piFinset]
  refine ⟨fun k => hv.1.1 k.1, ?_⟩
  rw [← sum_expandTuple hr (restrictTuple hr v),
    expandTuple_restrictTuple_of_collision hr v hv.2]
  exact hv.1.2

theorem expandTuple_mem_pairCollisionFiber {G : Finset F} {r : ℕ} (hr : 2 ≤ r) {t : F}
    {u : DropOne r hr → F} (hu : u ∈ weightedPairFiber G hr t) :
    expandTuple hr u ∈ pairCollisionFiber G r t (canonicalPair r hr) := by
  rw [weightedPairFiber, Finset.mem_filter, Fintype.mem_piFinset] at hu
  rw [pairCollisionFiber, Finset.mem_filter, tupleSumFiber,
    Finset.mem_filter, Fintype.mem_piFinset]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro k
    by_cases hk : k = (canonicalPair r hr).2
    · simp [expandTuple, hk]
      exact hu.1 (retainedZero r hr)
    · simp [expandTuple, hk]
      exact hu.1 ⟨k, hk⟩
  · rw [sum_expandTuple]
    exact hu.2
  · rw [expandTuple_at_fst, expandTuple_at_snd]

/-- **Exact compression of the canonical collision fiber.** -/
theorem pairCollisionFiber_card_eq_weightedPairFiber
    (G : Finset F) {r : ℕ} (hr : 2 ≤ r) (t : F) :
    (pairCollisionFiber G r t (canonicalPair r hr)).card =
      (weightedPairFiber G hr t).card := by
  apply Finset.card_bij (fun v _ => restrictTuple hr v)
  · exact fun v hv => restrictTuple_mem_weightedPairFiber hr hv
  · intro v hv w hw heq
    apply_fun expandTuple hr at heq
    rw [expandTuple_restrictTuple_of_collision hr v (Finset.mem_filter.mp hv).2,
      expandTuple_restrictTuple_of_collision hr w (Finset.mem_filter.mp hw).2] at heq
    exact heq
  · intro u hu
    exact ⟨expandTuple hr u, expandTuple_mem_pairCollisionFiber hr hu,
      restrictTuple_expandTuple hr u⟩

/-- **Weighted-profile defect capstone.** -/
theorem factorialRepetitionDefect_centeredMass_le_weightedPairEnergy
    (G : Finset F) {r : ℕ} (hr : 2 ≤ r) :
    centeredSqMass (factorialRepetitionDefect G r) ≤
      (Fintype.card F : ℝ) * (collisionIndices r).card ^ 2 *
        ∑ t : F, ((weightedPairFiber G hr t).card : ℝ) ^ 2 := by
  simpa only [pairCollisionFiber_card_eq_weightedPairFiber G hr] using
    factorialRepetitionDefect_centeredMass_le_canonicalPairEnergy G hr

#print axioms sum_expandTuple
#print axioms pairCollisionFiber_card_eq_weightedPairFiber
#print axioms factorialRepetitionDefect_centeredMass_le_weightedPairEnergy

end ArkLib.ProximityGap.Frontier.G185CanonicalWeightedCompression
