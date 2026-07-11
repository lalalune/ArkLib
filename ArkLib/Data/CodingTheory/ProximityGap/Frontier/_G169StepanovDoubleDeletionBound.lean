/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G168DoubleDeletionCoreBound
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G103FSubgroupCollisionBound

/-!
# G169: Stepanov-refined double deletion bound

G168 stored one free left mark at cost `|G|`.  For fixed reduced supports `(A,B)`, equal sums force
the right mark to be `x-c`, where `c = sum B - sum A`.  Disjointness makes `c ≠ 0`; hence the left
mark lies in the shifted-intersection fiber `{x∈G | x-c∈G}`.

If every nonzero such fiber has size at most `ρ`, the G168 bound sharpens to

`#cores * t² ≤ C(|G|,t-1)² * ρ`.

The existing G103F Stepanov theorem supplies `ρ = 4B² ≈ |G|^{2/3}` for multiplicatively closed
subgroups, replacing G168's factor `|G|` by a genuinely sublinear factor.

Issue #466.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G169StepanovDoubleDeletionBound

open scoped BigOperators
open ArkLib.ProximityGap.Frontier.G102FAdditiveLiftAmplification
open ArkLib.ProximityGap.Frontier.G103FSubgroupCollisionBound
open ArkLib.ProximityGap.Frontier.G145LowerDepthMultiplicityEnvelope
open ArkLib.ProximityGap.Frontier.G168DoubleDeletionCoreBound

variable {F : Type*} [AddCommGroup F] [Fintype F] [DecidableEq F]

def deletionDifference (q : Finset F × Finset F) : F :=
  (∑ y ∈ q.2, y) - ∑ x ∈ q.1, x

def deletionDifferenceFiber (G : Finset F) (q : Finset F × Finset F) : Finset F :=
  G.filter fun x => x - deletionDifference q ∈ G

noncomputable def nonzeroReducedPairs (G : Finset F) (t : ℕ) :
    Finset (Finset F × Finset F) :=
  (G.powersetCard (t - 1) ×ˢ G.powersetCard (t - 1)).filter fun q =>
    deletionDifference q ≠ 0

noncomputable def refinedDeletionAmbient (G : Finset F) (t : ℕ) :
    Finset (Σ _q : Finset F × Finset F, F) :=
  (nonzeroReducedPairs G t).sigma fun q => deletionDifferenceFiber G q

noncomputable def refinedDeletionCode
    (z : Σ _c : Finset F × Finset F, F × F) :
    Σ _q : Finset F × Finset F, F :=
  ⟨(z.1.1.erase z.2.1, z.1.2.erase z.2.2), z.2.1⟩

theorem deletionDifference_eq_mark_sub_mark {G : Finset F} {t : ℕ}
    {z : Σ _c : Finset F × Finset F, F × F}
    (hz : z ∈ doublyMarkedCorePairs G t) :
    deletionDifference (z.1.1.erase z.2.1, z.1.2.erase z.2.2) = z.2.1 - z.2.2 := by
  have hsum := marked_core_sum_identity hz
  unfold deletionDifference
  rw [sub_eq_sub_iff_add_eq_add]
  simpa [add_comm] using hsum.symm

theorem deletionDifference_ne_zero {G : Finset F} {t : ℕ}
    {z : Σ _c : Finset F × Finset F, F × F}
    (hz : z ∈ doublyMarkedCorePairs G t) :
    deletionDifference (z.1.1.erase z.2.1, z.1.2.erase z.2.2) ≠ 0 := by
  rw [deletionDifference_eq_mark_sub_mark hz, sub_ne_zero]
  intro hxy
  rw [mem_doublyMarkedCorePairs_iff] at hz
  exact (Finset.disjoint_left.mp (mem_subsetCorePairs_iff.mp hz.1).2.2.1)
    hz.2.1 (hxy ▸ hz.2.2)

theorem refinedDeletionCode_maps {G : Finset F} {t : ℕ}
    {z : Σ _c : Finset F × Finset F, F × F}
    (hz : z ∈ doublyMarkedCorePairs G t) :
    refinedDeletionCode z ∈ refinedDeletionAmbient G t := by
  classical
  rw [refinedDeletionAmbient, Finset.mem_sigma]
  refine ⟨?_, ?_⟩
  · rw [nonzeroReducedPairs, Finset.mem_filter]
    refine ⟨?_, deletionDifference_ne_zero hz⟩
    have hm := doubleDeletionCode_maps hz
    rw [doubleDeletionAmbient, Finset.mem_product] at hm
    exact hm.1
  · rw [deletionDifferenceFiber, Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · rw [mem_doublyMarkedCorePairs_iff] at hz
      exact (Finset.mem_powersetCard.mp (mem_subsetCorePairs_iff.mp hz.1).1).1 hz.2.1
    · change z.2.1 - deletionDifference
        (z.1.1.erase z.2.1, z.1.2.erase z.2.2) ∈ G
      rw [deletionDifference_eq_mark_sub_mark hz]
      simp only [sub_sub_cancel]
      rw [mem_doublyMarkedCorePairs_iff] at hz
      exact (Finset.mem_powersetCard.mp (mem_subsetCorePairs_iff.mp hz.1).2.1).1 hz.2.2

theorem refinedDeletionCode_injOn (G : Finset F) (t : ℕ) :
    Set.InjOn refinedDeletionCode
      (↑(doublyMarkedCorePairs G t) : Set (Σ _c : Finset F × Finset F, F × F)) := by
  intro z hz w hw h
  apply doubleDeletionCode_injOn G t hz hw
  apply Prod.ext
  · exact congrArg Sigma.fst h
  · exact eq_of_heq (Sigma.mk.inj_iff.mp h).2

theorem refinedDeletionAmbient_card_le
    (G : Finset F) (t ρ : ℕ)
    (hρ : ∀ c : F, c ≠ 0 → (G.filter fun x => x - c ∈ G).card ≤ ρ) :
    (refinedDeletionAmbient G t).card ≤ (G.card.choose (t - 1)) ^ 2 * ρ := by
  classical
  rw [refinedDeletionAmbient, Finset.card_sigma]
  calc
    (∑ q ∈ nonzeroReducedPairs G t, (deletionDifferenceFiber G q).card) ≤
        ∑ _q ∈ nonzeroReducedPairs G t, ρ := by
      apply Finset.sum_le_sum
      intro q hq
      rw [nonzeroReducedPairs, Finset.mem_filter] at hq
      exact hρ (deletionDifference q) hq.2
    _ = (nonzeroReducedPairs G t).card * ρ := by simp
    _ ≤ ((G.powersetCard (t - 1) ×ˢ G.powersetCard (t - 1)).card) * ρ :=
      Nat.mul_le_mul_right ρ (Finset.card_le_card (Finset.filter_subset _ _))
    _ = (G.card.choose (t - 1)) ^ 2 * ρ := by
      simp [Finset.card_product, Finset.card_powersetCard, pow_two]

/-- **Parameterized G169 capstone.** A uniform nonzero shifted-intersection bound replaces G168's
raw factor `|G|`. -/
theorem subsetCorePairs_mul_sq_le_choose_sq_mul_collision
    (G : Finset F) (t ρ : ℕ)
    (hρ : ∀ c : F, c ≠ 0 → (G.filter fun x => x - c ∈ G).card ≤ ρ) :
    (subsetCorePairs G t).card * t ^ 2 ≤ (G.card.choose (t - 1)) ^ 2 * ρ := by
  rw [← doublyMarkedCorePairs_card]
  exact (Finset.card_le_card_of_injOn refinedDeletionCode
    (fun _ hz => refinedDeletionCode_maps hz) (refinedDeletionCode_injOn G t)).trans
      (refinedDeletionAmbient_card_le G t ρ hρ)

section ZMod

variable {p : ℕ} [Fact p.Prime]

/-- **Unconditional Stepanov specialization.** For a multiplicatively closed nonzero subgroup,
the remaining collision factor is `4B² ≈ |G|^{2/3}`. -/
theorem subsetCorePairs_mul_sq_le_stepanov
    (G : Finset (ZMod p)) (t B : ℕ)
    (h0 : (0 : ZMod p) ∉ G) (hmul : ∀ x ∈ G, ∀ y ∈ G, x * y ∈ G)
    (hB : 2 ≤ B) (h2B : 2 * B ≤ G.card) (hB3 : 2 * G.card ≤ B ^ 3)
    (hp : G.card * B ≤ p) :
    (subsetCorePairs G t).card * t ^ 2 ≤
      (G.card.choose (t - 1)) ^ 2 * (4 * B ^ 2) := by
  apply subsetCorePairs_mul_sq_le_choose_sq_mul_collision
  exact addCollisionBound_of_closure G h0 hmul hB h2B hB3 hp

end ZMod

#print axioms refinedDeletionCode_injOn
#print axioms refinedDeletionAmbient_card_le
#print axioms subsetCorePairs_mul_sq_le_choose_sq_mul_collision
#print axioms subsetCorePairs_mul_sq_le_stepanov

end ArkLib.ProximityGap.Frontier.G169StepanovDoubleDeletionBound
