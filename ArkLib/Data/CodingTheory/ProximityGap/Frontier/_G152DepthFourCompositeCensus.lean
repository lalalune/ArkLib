/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G151CompositePacketOnsetDepthFour

/-!
# G152: the depth-four composite census is quadratic in depth two

G151 proves that every nonprimitive balanced depth-four core is the disjoint union of two
depth-two balanced cores.  This file turns that existential structure into a finite census bound.

Inside G145's finite `subsetCorePairs G 4`, filter the nonprimitive cores.  Every member lies in the
image of the union map from an ordered pair of members of `subsetCorePairs G 2`.  Therefore

`# compositeCorePairs(G,4) ≤ #subsetCorePairs(G,2)^2`.

The bound deliberately allows incompatible/cross-overlapping depth-two pairs in the codomain; it
is an upper bound.  The important separation is exact: all nonprimitive depth-four mass is charged
to the ordinary additive-energy/parallelogram census, leaving only primitive depth-four packets as
new arithmetic.

Issue #466.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G152DepthFourCompositeCensus

open ArkLib.ProximityGap.Frontier.G145LowerDepthMultiplicityEnvelope
open ArkLib.ProximityGap.Frontier.G147ConnectedBalancedCoreRecursion
open ArkLib.ProximityGap.Frontier.G150PrimitivePacketDepthTwoBase
open ArkLib.ProximityGap.Frontier.G151CompositePacketOnsetDepthFour

variable {F : Type*} [AddCommGroup F] [Fintype F] [DecidableEq F]

/-- Finite primitive sector inside the G145 depth-`t` core census. -/
noncomputable def primitiveCorePairs (G : Finset F) (t : ℕ) :
    Finset (Finset F × Finset F) := by
  classical
  exact (subsetCorePairs G t).filter IsPrimitiveBalancedCore

/-- Finite nonprimitive/composite sector inside the G145 depth-`t` core census. -/
noncomputable def compositeCorePairs (G : Finset F) (t : ℕ) :
    Finset (Finset F × Finset F) := by
  classical
  exact (subsetCorePairs G t).filter fun c => ¬ IsPrimitiveBalancedCore c

/-- Primitive and composite sectors partition the complete core-pair census. -/
theorem subsetCorePairs_eq_primitive_union_composite (G : Finset F) (t : ℕ) :
    subsetCorePairs G t = primitiveCorePairs G t ∪ compositeCorePairs G t := by
  classical
  ext c
  simp [primitiveCorePairs, compositeCorePairs]
  tauto

theorem primitive_disjoint_composite (G : Finset F) (t : ℕ) :
    Disjoint (primitiveCorePairs G t) (compositeCorePairs G t) := by
  classical
  apply Finset.disjoint_left.mpr
  intro c hp hc
  rw [primitiveCorePairs, Finset.mem_filter] at hp
  rw [compositeCorePairs, Finset.mem_filter] at hc
  exact hc.2 hp.2

theorem subsetCorePairs_card_eq_primitive_add_composite (G : Finset F) (t : ℕ) :
    (subsetCorePairs G t).card =
      (primitiveCorePairs G t).card + (compositeCorePairs G t).card := by
  rw [subsetCorePairs_eq_primitive_union_composite,
    Finset.card_union_of_disjoint (primitive_disjoint_composite G t)]

theorem balancedCore_left_ne_right {c : Finset F × Finset F}
    (hc : IsBalancedCore c) : c.1 ≠ c.2 := by
  intro h
  obtain ⟨x, hx⟩ := hc.1
  exact (Finset.disjoint_left.mp hc.2.2.1) hx (h ▸ hx)

theorem balancedCore_mem_subsetCorePairs {G : Finset F} {t : ℕ}
    {c : Finset F × Finset F} (hc : IsBalancedCore c)
    (hcard : c.1.card = t) (hL : c.1 ⊆ G) (hR : c.2 ⊆ G) :
    c ∈ subsetCorePairs G t := by
  rw [mem_subsetCorePairs_iff]
  exact ⟨Finset.mem_powersetCard.mpr ⟨hL, hcard⟩,
    Finset.mem_powersetCard.mpr ⟨hR, hc.2.1.symm.trans hcard⟩,
    hc.2.2.1, hc.2.2.2, balancedCore_left_ne_right hc⟩

/-- Union of two ordered core pairs. -/
def unionCorePair
    (z : (Finset F × Finset F) × (Finset F × Finset F)) : Finset F × Finset F :=
  (z.1.1 ∪ z.2.1, z.1.2 ∪ z.2.2)

/-- Every composite depth-four core is covered by the union image of two depth-two core pairs. -/
theorem compositeDepthFour_subset_twoCoreUnionImage (G : Finset F) :
    compositeCorePairs G 4 ⊆
      ((subsetCorePairs G 2 ×ˢ subsetCorePairs G 2).image unionCorePair) := by
  classical
  intro c hccomp
  rw [compositeCorePairs, Finset.mem_filter] at hccomp
  obtain ⟨hcCore, hcNotPrim⟩ := hccomp
  obtain ⟨hcL, hcR, hcDisj, hcSum, hcNe⟩ := mem_subsetCorePairs_iff.mp hcCore
  obtain ⟨hcLsub, hcLcard⟩ := Finset.mem_powersetCard.mp hcL
  obtain ⟨hcRsub, hcRcard⟩ := Finset.mem_powersetCard.mp hcR
  have hcBal : IsBalancedCore c := by
    refine ⟨?_, hcLcard.trans hcRcard.symm, hcDisj, hcSum⟩
    exact Finset.card_pos.mp (by omega)
  rcases depthFour_primitive_or_two_depthTwo hcBal hcLcard with hprim |
    ⟨d, e, hd, he, hdcard, hecard, hdprim, heprim,
      hdisjL, hdisjR, hreconL, hreconR⟩
  · exact (hcNotPrim hprim).elim
  · have hdLsub : d.1 ⊆ G := by
      intro x hx
      exact hcLsub (hreconL ▸ Finset.mem_union_left e.1 hx)
    have hdRsub : d.2 ⊆ G := by
      intro x hx
      exact hcRsub (hreconR ▸ Finset.mem_union_left e.2 hx)
    have heLsub : e.1 ⊆ G := by
      intro x hx
      exact hcLsub (hreconL ▸ Finset.mem_union_right d.1 hx)
    have heRsub : e.2 ⊆ G := by
      intro x hx
      exact hcRsub (hreconR ▸ Finset.mem_union_right d.2 hx)
    have hdmem := balancedCore_mem_subsetCorePairs hd hdcard hdLsub hdRsub
    have hemel := balancedCore_mem_subsetCorePairs he hecard heLsub heRsub
    rw [Finset.mem_image]
    refine ⟨(d, e), Finset.mem_product.mpr ⟨hdmem, hemel⟩, ?_⟩
    exact Prod.ext hreconL hreconR

/-- **G152 capstone.** Composite depth-four mass is at most the square of the depth-two core
census. -/
theorem compositeDepthFour_card_le_corePairsTwo_sq (G : Finset F) :
    (compositeCorePairs G 4).card ≤ (subsetCorePairs G 2).card ^ 2 := by
  calc
    (compositeCorePairs G 4).card ≤
        (((subsetCorePairs G 2 ×ˢ subsetCorePairs G 2).image unionCorePair).card) :=
      Finset.card_le_card (compositeDepthFour_subset_twoCoreUnionImage G)
    _ ≤ (subsetCorePairs G 2 ×ˢ subsetCorePairs G 2).card := Finset.card_image_le
    _ = (subsetCorePairs G 2).card ^ 2 := by
      rw [Finset.card_product, pow_two]

#print axioms subsetCorePairs_eq_primitive_union_composite
#print axioms subsetCorePairs_card_eq_primitive_add_composite
#print axioms balancedCore_mem_subsetCorePairs
#print axioms compositeDepthFour_subset_twoCoreUnionImage
#print axioms compositeDepthFour_card_le_corePairsTwo_sq

end ArkLib.ProximityGap.Frontier.G152DepthFourCompositeCensus
