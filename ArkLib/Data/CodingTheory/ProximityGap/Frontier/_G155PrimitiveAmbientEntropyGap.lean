/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G154PrimitiveMajorantClosure

/-!
# G155: primitive ambient census and production entropy gap

G154 reduces the connected-packet route to bounding the finite primitive census.  This file counts
its exact support-level ambient space.  An ordered disjoint pair of `t`-subsets is chosen by first
choosing the left set and then choosing the right set from its complement, so the count is

`choose (|G|) t * choose (|G|-t) t`.

Primitive core pairs inject into this ambient space.  At depths below four, G151 shows every core
is primitive, so the primitive and full core censuses agree exactly.

At the production parameters the ambient space already exceeds `2^160` using only its first
binomial factor (G139's entropy certificate).  Therefore support counting alone is quantitatively
incapable of supplying the G154 primitive majorant: the required gain must use the equal-sum
arithmetic, not merely disjointness.

Issue #466.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G155PrimitiveAmbientEntropyGap

open ArkLib.ProximityGap.Frontier.G139NoAccidentEntropyObstruction
open ArkLib.ProximityGap.Frontier.G145LowerDepthMultiplicityEnvelope
open ArkLib.ProximityGap.Frontier.G151CompositePacketOnsetDepthFour
open ArkLib.ProximityGap.Frontier.G152DepthFourCompositeCensus
open ArkLib.ProximityGap.Frontier.G153AllDepthCompositeConvolution

variable {F : Type*} [AddCommGroup F] [Fintype F] [DecidableEq F]

/-- Ordered disjoint pairs of `t`-subsets, represented by choosing the right set from the
complement of the left set. -/
def disjointSubsetPairAmbient (G : Finset F) (t : ℕ) :
    Finset (Finset F × Finset F) :=
  (G.powersetCard t).biUnion fun S =>
    ({S} ×ˢ (G \ S).powersetCard t)

theorem disjointSubsetPairAmbient_card (G : Finset F) (t : ℕ) :
    (disjointSubsetPairAmbient G t).card =
      G.card.choose t * (G.card - t).choose t := by
  unfold disjointSubsetPairAmbient
  rw [Finset.card_biUnion]
  · calc
      ∑ S ∈ G.powersetCard t, ({S} ×ˢ (G \ S).powersetCard t).card
          = ∑ S ∈ G.powersetCard t, (G.card - t).choose t := by
              apply Finset.sum_congr rfl
              intro S hS
              obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hS
              rw [Finset.card_product, Finset.card_singleton, one_mul,
                Finset.card_powersetCard, Finset.card_sdiff_of_subset hsub, hcard]
      _ = (G.powersetCard t).card * (G.card - t).choose t := by simp
      _ = G.card.choose t * (G.card - t).choose t := by
        rw [Finset.card_powersetCard]
  · intro S hS T hT hne
    apply Finset.disjoint_left.mpr
    intro p hpS hpT
    have hfstS : p.1 = S := by
      exact (Finset.mem_product.mp hpS).1 |> Finset.mem_singleton.mp
    have hfstT : p.1 = T := by
      exact (Finset.mem_product.mp hpT).1 |> Finset.mem_singleton.mp
    exact hne (hfstS.symm.trans hfstT)

/-- Every equal-sum core pair lies in the ordered disjoint support ambient. -/
theorem subsetCorePairs_subset_ambient (G : Finset F) (t : ℕ) :
    subsetCorePairs G t ⊆ disjointSubsetPairAmbient G t := by
  intro c hc
  obtain ⟨hcL, hcR, hcDisj, hcSum, hcNe⟩ := mem_subsetCorePairs_iff.mp hc
  obtain ⟨hcLsub, hcLcard⟩ := Finset.mem_powersetCard.mp hcL
  obtain ⟨hcRsub, hcRcard⟩ := Finset.mem_powersetCard.mp hcR
  rw [disjointSubsetPairAmbient, Finset.mem_biUnion]
  refine ⟨c.1, hcL, Finset.mem_product.mpr ⟨Finset.mem_singleton_self _, ?_⟩⟩
  rw [Finset.mem_powersetCard]
  refine ⟨?_, hcRcard⟩
  intro x hx
  exact Finset.mem_sdiff.mpr ⟨hcRsub hx,
    fun hxL => (Finset.disjoint_left.mp hcDisj) hxL hx⟩

/-- Primitive census ambient bound. -/
theorem primitiveCorePairs_card_le_ambient (G : Finset F) (t : ℕ) :
    (primitiveCorePairs G t).card ≤
      G.card.choose t * (G.card - t).choose t := by
  classical
  rw [← disjointSubsetPairAmbient_card]
  apply Finset.card_le_card
  exact fun c hc => subsetCorePairs_subset_ambient G t (Finset.mem_filter.mp hc).1

/-- Below composite onset, the primitive and complete core censuses coincide exactly. -/
theorem primitiveCorePairs_eq_subsetCorePairs_of_lt_four
    (G : Finset F) {t : ℕ} (ht : t < 4) :
    primitiveCorePairs G t = subsetCorePairs G t := by
  classical
  apply Finset.Subset.antisymm
  · intro c hc
    exact (Finset.mem_filter.mp hc).1
  · intro c hc
    rw [primitiveCorePairs, Finset.mem_filter]
    refine ⟨hc, primitive_of_balanced_of_left_card_lt_four
      (corePair_balanced_of_mem hc) ?_⟩
    exact (Finset.mem_powersetCard.mp (mem_subsetCorePairs_iff.mp hc).1).2 ▸ ht

theorem choose_le_disjointSubsetPairAmbient_card (G : Finset F) {t : ℕ}
    (ht : t ≤ G.card - t) :
    G.card.choose t ≤ (disjointSubsetPairAmbient G t).card := by
  rw [disjointSubsetPairAmbient_card]
  have hright : 1 ≤ (G.card - t).choose t :=
    Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (Nat.choose_pos ht))
  calc
    G.card.choose t = G.card.choose t * 1 := (Nat.mul_one _).symm
    _ ≤ G.card.choose t * (G.card - t).choose t :=
      Nat.mul_le_mul_left _ hright

/-- The production disjoint-support ambient already exceeds the entire `2^160` field cap. -/
theorem production_ambient_card_gt_fieldCap
    (G : Finset F) (hG : G.card = 2 ^ 30) :
    2 ^ 160 < (disjointSubsetPairAmbient G 110).card := by
  calc
    2 ^ 160 < (2 ^ 29).choose 110 := production_choose_gt_fieldCap
    _ ≤ G.card.choose 110 := by
      rw [hG]
      exact Nat.choose_le_choose 110 (by norm_num)
    _ ≤ (disjointSubsetPairAmbient G 110).card :=
      choose_le_disjointSubsetPairAmbient_card G (by rw [hG]; norm_num)

#print axioms disjointSubsetPairAmbient_card
#print axioms subsetCorePairs_subset_ambient
#print axioms primitiveCorePairs_card_le_ambient
#print axioms primitiveCorePairs_eq_subsetCorePairs_of_lt_four
#print axioms choose_le_disjointSubsetPairAmbient_card
#print axioms production_ambient_card_gt_fieldCap

end ArkLib.ProximityGap.Frontier.G155PrimitiveAmbientEntropyGap
