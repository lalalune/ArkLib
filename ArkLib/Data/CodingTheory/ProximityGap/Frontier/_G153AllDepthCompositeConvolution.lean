/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G152DepthFourCompositeCensus

/-!
# G153: all-depth composite packet convolution

G152 proves the first census recursion at depth four.  This file establishes its all-depth form.
For each split depth `s ∈ [2,t-2]`, take an ordered depth-`s` core and depth-`(t-s)` core and
union their two coordinates.  The union images over all `s` form a finite split-code envelope.

Every nonprimitive depth-`t` core lies in this envelope: G147 supplies its two balanced children,
G150 forces both depths to be at least two, and exact reconstruction identifies the parent with
their union code.  Hence

`#composite(t) ≤ Σ_{s=2}^{t-2} #corePairs(s) * #corePairs(t-s)`.

Together with G152's exact primitive/composite partition this is the connected-packet convolution
recurrence.  It removes all composite packet counts as independent arithmetic inputs; only the
primitive census at each depth remains.

Issue #466.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G153AllDepthCompositeConvolution

open ArkLib.ProximityGap.Frontier.G145LowerDepthMultiplicityEnvelope
open ArkLib.ProximityGap.Frontier.G147ConnectedBalancedCoreRecursion
open ArkLib.ProximityGap.Frontier.G150PrimitivePacketDepthTwoBase
open ArkLib.ProximityGap.Frontier.G152DepthFourCompositeCensus

variable {F : Type*} [AddCommGroup F] [Fintype F] [DecidableEq F]

/-- Finite union-code envelope over every admissible split depth. -/
noncomputable def compositeSplitEnvelope (G : Finset F) (t : ℕ) :
    Finset (Finset F × Finset F) := by
  classical
  exact (Finset.Icc 2 (t - 2)).biUnion fun s =>
    ((subsetCorePairs G s ×ˢ subsetCorePairs G (t - s)).image unionCorePair)

theorem corePair_balanced_of_mem {G : Finset F} {t : ℕ}
    {c : Finset F × Finset F} (hc : c ∈ subsetCorePairs G t) :
    IsBalancedCore c := by
  obtain ⟨hcL, hcR, hcDisj, hcSum, hcNe⟩ := mem_subsetCorePairs_iff.mp hc
  obtain ⟨hcLsub, hcLcard⟩ := Finset.mem_powersetCard.mp hcL
  obtain ⟨hcRsub, hcRcard⟩ := Finset.mem_powersetCard.mp hcR
  have hcLne : c.1.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have ht0 : t = 0 := by simpa [h] using hcLcard.symm
    have hcRempty : c.2 = ∅ := Finset.card_eq_zero.mp (by omega)
    exact hcNe (h.trans hcRempty.symm)
  exact ⟨hcLne, hcLcard.trans hcRcard.symm, hcDisj, hcSum⟩

/-- Every composite core is represented by a union code of two smaller core pairs. -/
theorem compositeCorePairs_subset_splitEnvelope (G : Finset F) (t : ℕ) :
    compositeCorePairs G t ⊆ compositeSplitEnvelope G t := by
  classical
  intro c hccomp
  rw [compositeCorePairs, Finset.mem_filter] at hccomp
  obtain ⟨hcCore, hcNotPrim⟩ := hccomp
  have hcBal := corePair_balanced_of_mem hcCore
  obtain ⟨hcL, hcR, hcDisj, hcSum, hcNe⟩ := mem_subsetCorePairs_iff.mp hcCore
  obtain ⟨hcLsub, hcLcard⟩ := Finset.mem_powersetCard.mp hcL
  obtain ⟨hcRsub, hcRcard⟩ := Finset.mem_powersetCard.mp hcR
  rcases primitive_or_split c hcBal with hprim |
    ⟨d, e, hd, he, hdlt, helt, hdisjL, hdisjR, hreconL, hreconR⟩
  · exact (hcNotPrim hprim).elim
  · let s := d.1.card
    have hdmin : 2 ≤ s := balancedCore_two_le_left_card hd.1
    have hemin : 2 ≤ e.1.card := balancedCore_two_le_left_card he
    have hsum : s + e.1.card = t := by
      dsimp [s]
      rw [← hcLcard, ← Finset.card_union_of_disjoint hdisjL, hreconL]
    have hsmax : s ≤ t - 2 := by omega
    have hecard : e.1.card = t - s := by omega
    have hdLsub : d.1 ⊆ G := by
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
    have hdmem : d ∈ subsetCorePairs G s :=
      balancedCore_mem_subsetCorePairs hd.1 rfl hdLsub hdRsub
    have hemel : e ∈ subsetCorePairs G (t - s) :=
      balancedCore_mem_subsetCorePairs he hecard heLsub heRsub
    rw [compositeSplitEnvelope, Finset.mem_biUnion]
    refine ⟨s, Finset.mem_Icc.mpr ⟨hdmin, hsmax⟩, ?_⟩
    rw [Finset.mem_image]
    refine ⟨(d, e), Finset.mem_product.mpr ⟨hdmem, hemel⟩, ?_⟩
    exact Prod.ext hreconL hreconR

/-- **G153 composite capstone.** The nonprimitive census obeys the core-pair convolution bound. -/
theorem compositeCorePairs_card_le_convolution (G : Finset F) (t : ℕ) :
    (compositeCorePairs G t).card ≤
      ∑ s ∈ Finset.Icc 2 (t - 2),
        (subsetCorePairs G s).card * (subsetCorePairs G (t - s)).card := by
  calc
    (compositeCorePairs G t).card ≤ (compositeSplitEnvelope G t).card :=
      Finset.card_le_card (compositeCorePairs_subset_splitEnvelope G t)
    _ ≤ ∑ s ∈ Finset.Icc 2 (t - 2),
        (((subsetCorePairs G s ×ˢ subsetCorePairs G (t - s)).image unionCorePair).card) := by
      unfold compositeSplitEnvelope
      exact Finset.card_biUnion_le
    _ ≤ ∑ s ∈ Finset.Icc 2 (t - 2),
        (subsetCorePairs G s ×ˢ subsetCorePairs G (t - s)).card := by
      exact Finset.sum_le_sum fun _ _ => Finset.card_image_le
    _ = ∑ s ∈ Finset.Icc 2 (t - 2),
        (subsetCorePairs G s).card * (subsetCorePairs G (t - s)).card := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [Finset.card_product]

/-- Full census recursion: primitive mass plus the convolution envelope. -/
theorem subsetCorePairs_card_le_primitive_add_convolution (G : Finset F) (t : ℕ) :
    (subsetCorePairs G t).card ≤ (primitiveCorePairs G t).card +
      ∑ s ∈ Finset.Icc 2 (t - 2),
        (subsetCorePairs G s).card * (subsetCorePairs G (t - s)).card := by
  rw [subsetCorePairs_card_eq_primitive_add_composite]
  exact Nat.add_le_add_left (compositeCorePairs_card_le_convolution G t) _

#print axioms corePair_balanced_of_mem
#print axioms compositeCorePairs_subset_splitEnvelope
#print axioms compositeCorePairs_card_le_convolution
#print axioms subsetCorePairs_card_le_primitive_add_convolution

end ArkLib.ProximityGap.Frontier.G153AllDepthCompositeConvolution
