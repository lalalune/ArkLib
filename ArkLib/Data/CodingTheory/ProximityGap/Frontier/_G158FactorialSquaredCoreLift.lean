/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G157EvenPrimitiveMajorant

/-!
# G158: factorial-squared lift from set cores to ordered full-depth fibers

G143 compared each full-depth subset accident with one canonical ordered enumeration.  A set core
actually has `t!` independent enumerations on each side.  This file attaches two permutations to
the canonical enumeration and proves the resulting map into `depthFiber G t t` is injective.

Consequently

`#subsetCorePairs(G,t) * (t!)^2 ≤ depthFiber G t t`.

This strengthens G145's canonical one-copy comparison by the full factorial-squared multiplicity.
The proof is purely enumerative: permutations preserve coordinate membership, sums, and value bags;
the injectivity of the canonical enumeration recovers both permutations.

Issue #466.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G158FactorialSquaredCoreLift

open scoped BigOperators
open ArkLib.ProximityGap.Frontier.G87CorrectedPaddingDecoder
open ArkLib.ProximityGap.Frontier.G83MMaximalCommonCancellation
open ArkLib.ProximityGap.Frontier.G95CardinalityDeepCapNoGo
open ArkLib.ProximityGap.Frontier.G114DepthThreePopulationNormalForm
open ArkLib.ProximityGap.Frontier.G143DepthStratifiedSubsetAccidents
open ArkLib.ProximityGap.Frontier.G145LowerDepthMultiplicityEnvelope

variable {F : Type*} [AddCommGroup F] [Fintype F] [DecidableEq F]

/-- Full-depth subset accidents decorated with independent endpoint permutations. -/
def fullDepthPermutationCodes (G : Finset F) (t : ℕ) :
    Finset ((SubsetFamily G t × SubsetFamily G t) ×
      (Equiv.Perm (Fin t) × Equiv.Perm (Fin t))) :=
  subsetAccidentStratum G t t ×ˢ
    ((Finset.univ : Finset (Equiv.Perm (Fin t))) ×ˢ Finset.univ)

/-- Independently permute the two canonical endpoint enumerations. -/
noncomputable def orderedEnumerationCode {G : Finset F} {t : ℕ}
    (z : (SubsetFamily G t × SubsetFamily G t) ×
      (Equiv.Perm (Fin t) × Equiv.Perm (Fin t))) :
    (Fin t → F) × (Fin t → F) :=
  ((enumPair z.1).1 ∘ z.2.1, (enumPair z.1).2 ∘ z.2.2)

theorem valueBag_comp_perm {t : ℕ} (v : Fin t → F) (e : Equiv.Perm (Fin t)) :
    valueBag (v ∘ e) = valueBag v := by
  rw [valueBag_eq_map, valueBag_eq_map]
  exact valueBag_comp_equiv e v

/-- Every decorated enumeration remains in the full-depth ordered-word fiber. -/
theorem orderedEnumerationCode_maps {G : Finset F} {t : ℕ}
    {z : (SubsetFamily G t × SubsetFamily G t) ×
      (Equiv.Perm (Fin t) × Equiv.Perm (Fin t))}
    (hz : z ∈ fullDepthPermutationCodes G t) :
    orderedEnumerationCode z ∈ (energySet G t).filter (fun q => cancelDepth q = t) := by
  obtain ⟨hp, hperms⟩ := Finset.mem_product.mp hz
  have hb := enumPair_maps_fullDepth hp
  rw [Finset.mem_filter] at hb ⊢
  obtain ⟨hbEnergy, hbDepth⟩ := hb
  rw [energySet, Finset.mem_filter] at hbEnergy
  obtain ⟨hbProd, hbSum⟩ := hbEnergy
  obtain ⟨hbL, hbR⟩ := Finset.mem_product.mp hbProd
  refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩, ?_⟩
  · rw [Fintype.mem_piFinset] at hbL ⊢
    exact fun i => hbL (z.2.1 i)
  · rw [Fintype.mem_piFinset] at hbR ⊢
    exact fun i => hbR (z.2.2 i)
  · change (∑ i, (enumPair z.1).1 (z.2.1 i)) =
      ∑ i, (enumPair z.1).2 (z.2.2 i)
    rw [Equiv.sum_comp z.2.1, Equiv.sum_comp z.2.2]
    exact hbSum
  · have hdisj := (cancelDepth_eq_length_iff_disjoint _ _).mp hbDepth
    apply (cancelDepth_eq_length_iff_disjoint _ _).mpr
    rw [valueBag_comp_perm, valueBag_comp_perm]
    exact hdisj

/-- The decorated canonical-enumeration map is injective on its finite code domain. -/
theorem orderedEnumerationCode_injOn (G : Finset F) (t : ℕ) :
    Set.InjOn orderedEnumerationCode
      (↑(fullDepthPermutationCodes G t) : Set ((SubsetFamily G t × SubsetFamily G t) ×
        (Equiv.Perm (Fin t) × Equiv.Perm (Fin t)))) := by
  intro z hz w hw hcode
  change ((enumPair z.1).1 ∘ z.2.1, (enumPair z.1).2 ∘ z.2.2) =
    ((enumPair w.1).1 ∘ w.2.1, (enumPair w.1).2 ∘ w.2.2) at hcode
  have hL : (enumPair z.1).1 ∘ z.2.1 = (enumPair w.1).1 ∘ w.2.1 :=
    congrArg Prod.fst hcode
  have hR : (enumPair z.1).2 ∘ z.2.2 = (enumPair w.1).2 ∘ w.2.2 :=
    congrArg Prod.snd hcode
  have hbagL' : valueBag (enumPair z.1).1 = valueBag (enumPair w.1).1 := by
    calc
      valueBag (enumPair z.1).1 = valueBag ((enumPair z.1).1 ∘ z.2.1) :=
        (valueBag_comp_perm _ _).symm
      _ = valueBag ((enumPair w.1).1 ∘ w.2.1) := congrArg valueBag hL
      _ = valueBag (enumPair w.1).1 := valueBag_comp_perm _ _
  have hbagR' : valueBag (enumPair z.1).2 = valueBag (enumPair w.1).2 := by
    calc
      valueBag (enumPair z.1).2 = valueBag ((enumPair z.1).2 ∘ z.2.2) :=
        (valueBag_comp_perm _ _).symm
      _ = valueBag ((enumPair w.1).2 ∘ w.2.2) := congrArg valueBag hR
      _ = valueBag (enumPair w.1).2 := valueBag_comp_perm _ _
  have hbagL := congrArg Multiset.toFinset hbagL'
  have hbagR := congrArg Multiset.toFinset hbagR'
  have hp : z.1 = w.1 := by
    apply Prod.ext <;> apply Subtype.ext
    · simpa [enumPair, valueBag_enumSubset_toFinset] using hbagL
    · simpa [enumPair, valueBag_enumSubset_toFinset] using hbagR
  have hper : z.2 = w.2 := by
    rw [hp] at hL hR
    apply Prod.ext
    · apply Equiv.ext
      intro i
      exact enumSubset_injective w.1.1.1 (endpoint_card w.1.1) (congrFun hL i)
    · apply Equiv.ext
      intro i
      exact enumSubset_injective w.1.2.1 (endpoint_card w.1.2) (congrFun hR i)
  exact Prod.ext hp hper

theorem fullDepthPermutationCodes_card (G : Finset F) (t : ℕ) :
    (fullDepthPermutationCodes G t).card =
      (subsetAccidentStratum G t t).card * (t.factorial ^ 2) := by
  unfold fullDepthPermutationCodes
  simp [Finset.card_product, Fintype.card_perm, Fintype.card_fin, pow_two]

/-- Every G145 set core canonically gives a full-depth subset accident. -/
theorem corePairs_card_le_fullDepthStratum (G : Finset F) (t : ℕ) :
    (subsetCorePairs G t).card ≤ (subsetAccidentStratum G t t).card := by
  have heq : (subsetCorePairs G t).card = (subsetAccidentStratum G t t).card := by
    refine Finset.card_bij
      (fun c hc =>
        (⟨c.1, (mem_subsetCorePairs_iff.mp hc).1⟩,
          ⟨c.2, (mem_subsetCorePairs_iff.mp hc).2.1⟩)) ?_ ?_ ?_
    · intro c hc
      rw [mem_fullDepth_stratum_iff, mem_subsetAccidents_iff]
      obtain ⟨hc1, hc2, hd, hs, hne⟩ := mem_subsetCorePairs_iff.mp hc
      exact ⟨⟨hs, fun h => hne (congrArg Subtype.val h)⟩, hd⟩
    · intro c hc d hd h
      exact Prod.ext (congrArg Subtype.val (congrArg Prod.fst h))
        (congrArg Subtype.val (congrArg Prod.snd h))
    · intro b hb
      refine ⟨(b.1.1, b.2.1), ?_, ?_⟩
      · rw [mem_subsetCorePairs_iff]
        obtain ⟨hbacc, hbdisj⟩ := mem_fullDepth_stratum_iff.mp hb
        obtain ⟨hbsum, hbne⟩ := mem_subsetAccidents_iff.mp hbacc
        exact ⟨b.1.2, b.2.2, hbdisj, hbsum, fun h => hbne (Subtype.ext h)⟩
      · apply Prod.ext <;> apply Subtype.ext <;> rfl
  exact heq.le

/-- **G158 capstone.** Every set core contributes all `(t!)^2` distinct ordered enumerations to the
full-depth word fiber. -/
theorem corePairs_mul_factorial_sq_le_depthFiber (G : Finset F) (t : ℕ) :
    (subsetCorePairs G t).card * (t.factorial ^ 2) ≤ depthFiber G t t := by
  calc
    (subsetCorePairs G t).card * t.factorial ^ 2 ≤
        (subsetAccidentStratum G t t).card * t.factorial ^ 2 :=
      Nat.mul_le_mul_right _ (corePairs_card_le_fullDepthStratum G t)
    _ = (fullDepthPermutationCodes G t).card := (fullDepthPermutationCodes_card G t).symm
    _ ≤ depthFiber G t t := by
      unfold depthFiber
      exact Finset.card_le_card_of_injOn orderedEnumerationCode
        (fun _ hz => orderedEnumerationCode_maps hz)
        (orderedEnumerationCode_injOn G t)

#print axioms orderedEnumerationCode_maps
#print axioms orderedEnumerationCode_injOn
#print axioms fullDepthPermutationCodes_card
#print axioms corePairs_card_le_fullDepthStratum
#print axioms corePairs_mul_factorial_sq_le_depthFiber

end ArkLib.ProximityGap.Frontier.G158FactorialSquaredCoreLift
