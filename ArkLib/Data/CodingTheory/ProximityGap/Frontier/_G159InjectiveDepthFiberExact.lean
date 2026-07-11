/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G158FactorialSquaredCoreLift

/-!
# G159: exact injective sector of the full-depth fiber

G158 injects every balanced set core, with all two-sided orderings, into the full-depth word
fiber.  Here we identify the image exactly: it is the sector in which both endpoint words are
internally injective.  Thus the injective sector has cardinality

`#subsetCorePairs(G,t) * (t!)^2`.

The complement is precisely the repeated-coordinate defect.  Consequently any upper-bound route
through the ordered depth fiber need only control that defect beyond the exact set-core term.

Issue #466.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G159InjectiveDepthFiberExact

open scoped BigOperators
open ArkLib.ProximityGap.Frontier.G83MMaximalCommonCancellation
open ArkLib.ProximityGap.Frontier.G87CorrectedPaddingDecoder
open ArkLib.ProximityGap.Frontier.G95CardinalityDeepCapNoGo
open ArkLib.ProximityGap.Frontier.G114DepthThreePopulationNormalForm
open ArkLib.ProximityGap.Frontier.G143DepthStratifiedSubsetAccidents
open ArkLib.ProximityGap.Frontier.G145LowerDepthMultiplicityEnvelope
open ArkLib.ProximityGap.Frontier.G158FactorialSquaredCoreLift

variable {F : Type*} [AddCommGroup F] [Fintype F] [DecidableEq F]

/-- The full-depth energy sector whose two endpoint words have no internal repetitions. -/
def injectiveDepthFiber (G : Finset F) (t : ℕ) :
    Finset ((Fin t → F) × (Fin t → F)) :=
  ((energySet G t).filter fun q => cancelDepth q = t).filter fun q =>
    Function.Injective q.1 ∧ Function.Injective q.2 ∧ q.1 ≠ q.2

/-- The complementary full-depth sector: diagonal or with an internal endpoint repetition. -/
def repeatedDepthDefect (G : Finset F) (t : ℕ) :
    Finset ((Fin t → F) × (Fin t → F)) :=
  ((energySet G t).filter fun q => cancelDepth q = t).filter fun q =>
    ¬(Function.Injective q.1 ∧ Function.Injective q.2 ∧ q.1 ≠ q.2)

theorem mem_injectiveDepthFiber_iff {G : Finset F} {t : ℕ}
    {q : (Fin t → F) × (Fin t → F)} :
    q ∈ injectiveDepthFiber G t ↔
      q ∈ (energySet G t).filter (fun z => cancelDepth z = t) ∧
        Function.Injective q.1 ∧ Function.Injective q.2 ∧ q.1 ≠ q.2 := by
  simp [injectiveDepthFiber]

/-- The range finset of an injective length-`t` word has exactly `t` elements. -/
theorem card_image_univ_of_injective {t : ℕ} {v : Fin t → F}
    (hv : Function.Injective v) :
    (Finset.univ.image v).card = t := by
  rw [Finset.card_image_of_injective _ hv]
  simp

/-- An injective word is a permutation of the canonical enumeration of its range. -/
noncomputable def rangePermutation {t : ℕ} (v : Fin t → F)
    (hv : Function.Injective v) : Equiv.Perm (Fin t) :=
  Equiv.ofBijective
    (fun i => (Finset.univ.image v).equivFinOfCardEq
      (card_image_univ_of_injective hv) ⟨v i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩)
    (by
      constructor
      · intro i j hij
        apply hv
        exact congrArg Subtype.val
          (((Finset.univ.image v).equivFinOfCardEq
            (card_image_univ_of_injective hv)).injective hij)
      · intro j
        let y : ↥(Finset.univ.image v) :=
          ((Finset.univ.image v).equivFinOfCardEq
            (card_image_univ_of_injective hv)).symm j
        obtain ⟨i, -, hi⟩ := Finset.mem_image.mp y.2
        refine ⟨i, ?_⟩
        calc
          _ = (Finset.univ.image v).equivFinOfCardEq
              (card_image_univ_of_injective hv) y := by
            apply congrArg
            show (⟨v i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩ :
              ↥(Finset.univ.image v)) = y
            exact Subtype.ext hi
          _ = j := Equiv.apply_symm_apply _ j)

theorem enumSubset_comp_rangePermutation {t : ℕ} (v : Fin t → F)
    (hv : Function.Injective v) :
    enumSubset (Finset.univ.image v) (card_image_univ_of_injective hv) ∘
        rangePermutation v hv = v := by
  funext i
  change (((Finset.univ.image v).equivFinOfCardEq
    (card_image_univ_of_injective hv)).symm
      ((Finset.univ.image v).equivFinOfCardEq
        (card_image_univ_of_injective hv)
        ⟨v i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩)).1 = v i
  simp

/-- Recover the balanced set core underlying an injective full-depth word pair. -/
noncomputable def wordCore {t : ℕ} (q : (Fin t → F) × (Fin t → F)) :
    Finset F × Finset F :=
  (Finset.univ.image q.1, Finset.univ.image q.2)

theorem wordCore_mem_subsetCorePairs {G : Finset F} {t : ℕ}
    {q : (Fin t → F) × (Fin t → F)}
    (hq : q ∈ injectiveDepthFiber G t) :
    wordCore q ∈ subsetCorePairs G t := by
  rw [mem_injectiveDepthFiber_iff] at hq
  obtain ⟨hdepth, hinjL, hinjR, hneWords⟩ := hq
  rw [Finset.mem_filter] at hdepth
  obtain ⟨henergy, hcancel⟩ := hdepth
  rw [energySet, Finset.mem_filter] at henergy
  obtain ⟨hprod, hsums⟩ := henergy
  obtain ⟨hL, hR⟩ := Finset.mem_product.mp hprod
  rw [Fintype.mem_piFinset] at hL hR
  rw [mem_subsetCorePairs_iff]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [Finset.mem_powersetCard]
    refine ⟨?_, card_image_univ_of_injective hinjL⟩
    intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    exact hL i
  · rw [Finset.mem_powersetCard]
    refine ⟨?_, card_image_univ_of_injective hinjR⟩
    intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    exact hR i
  · rw [Finset.disjoint_left]
    intro x hxL hxR
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hxL
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hxR
    have hd := (cancelDepth_eq_length_iff_disjoint q.1 q.2).mp hcancel
    rw [Multiset.disjoint_iff_ne] at hd
    exact hd (q.1 i) (by simp [valueBag]) (q.2 j) (by simp [valueBag]) (hi.trans hj.symm)
  · simpa [wordCore, Finset.sum_image, hinjL, hinjR] using hsums
  · intro h
    have hcardR := card_image_univ_of_injective hinjR
    have hrangeDisj : Disjoint (Finset.univ.image q.1) (Finset.univ.image q.2) := by
      rw [Finset.disjoint_left]
      intro x hxL hxR
      obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hxL
      obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hxR
      have hd := (cancelDepth_eq_length_iff_disjoint q.1 q.2).mp hcancel
      rw [Multiset.disjoint_iff_ne] at hd
      exact hd (q.1 i) (by simp [valueBag]) (q.2 j) (by simp [valueBag])
        (hi.trans hj.symm)
    have hempty : (Finset.univ.image q.2).card = 0 := by
      have h' : Finset.univ.image q.1 = Finset.univ.image q.2 := by
        simpa [wordCore] using h
      have hd : Disjoint (Finset.univ.image q.2) (Finset.univ.image q.2) := by
        rw [h'] at hrangeDisj
        exact hrangeDisj
      exact Finset.card_eq_zero.mpr (disjoint_self.mp hd)
    have ht : t = 0 := by omega
    subst t
    exact hneWords (Subsingleton.elim _ _)

/-- Every injective full-depth word is produced by its recovered core and two range
permutations. -/
theorem exists_code_eq_of_mem_injectiveDepthFiber {G : Finset F} {t : ℕ}
    {q : (Fin t → F) × (Fin t → F)}
    (hq : q ∈ injectiveDepthFiber G t) :
    ∃ z ∈ fullDepthPermutationCodes G t, orderedEnumerationCode z = q := by
  rw [mem_injectiveDepthFiber_iff] at hq
  obtain ⟨hdepth, hinjL, hinjR, hneWords⟩ := hq
  let S : Finset F := Finset.univ.image q.1
  let T : Finset F := Finset.univ.image q.2
  have hcore : (S, T) ∈ subsetCorePairs G t := wordCore_mem_subsetCorePairs
    (show q ∈ injectiveDepthFiber G t from by
      rw [mem_injectiveDepthFiber_iff]
      exact ⟨hdepth, hinjL, hinjR, hneWords⟩)
  let p : SubsetFamily G t × SubsetFamily G t :=
    (⟨S, (mem_subsetCorePairs_iff.mp hcore).1⟩,
     ⟨T, (mem_subsetCorePairs_iff.mp hcore).2.1⟩)
  let z := (p, (rangePermutation q.1 hinjL, rangePermutation q.2 hinjR))
  refine ⟨z, ?_, ?_⟩
  · rw [fullDepthPermutationCodes, Finset.mem_product]
    refine ⟨?_, by simp⟩
    rw [mem_fullDepth_stratum_iff, mem_subsetAccidents_iff]
    obtain ⟨hS, hT, hdisj, hsum, hne⟩ := mem_subsetCorePairs_iff.mp hcore
    exact ⟨⟨hsum, fun hp => hne (congrArg Subtype.val hp)⟩, hdisj⟩
  · apply Prod.ext
    · exact enumSubset_comp_rangePermutation q.1 hinjL
    · exact enumSubset_comp_rangePermutation q.2 hinjR

theorem fullDepthStratum_card_eq_corePairs (G : Finset F) (t : ℕ) :
    (subsetAccidentStratum G t t).card = (subsetCorePairs G t).card := by
  refine Finset.card_bij (fun p hp => (p.1.1, p.2.1)) ?_ ?_ ?_
  · intro p hp
    rw [mem_subsetCorePairs_iff]
    obtain ⟨hpacc, hpdisj⟩ := mem_fullDepth_stratum_iff.mp hp
    obtain ⟨hpsum, hpne⟩ := mem_subsetAccidents_iff.mp hpacc
    exact ⟨p.1.2, p.2.2, hpdisj, hpsum, fun h => hpne (Subtype.ext h)⟩
  · intro p hp q hq heq
    exact Prod.ext (Subtype.ext (congrArg Prod.fst heq))
      (Subtype.ext (congrArg Prod.snd heq))
  · intro c hc
    refine ⟨(⟨c.1, (mem_subsetCorePairs_iff.mp hc).1⟩,
      ⟨c.2, (mem_subsetCorePairs_iff.mp hc).2.1⟩), ?_, rfl⟩
    rw [mem_fullDepth_stratum_iff, mem_subsetAccidents_iff]
    obtain ⟨hcS, hcT, hcdisj, hcsum, hcne⟩ := mem_subsetCorePairs_iff.mp hc
    exact ⟨⟨hcsum, fun h => hcne (congrArg Subtype.val h)⟩, hcdisj⟩

/-- **G159 capstone.** The injective full-depth sector is exactly the set-core census times all
two-sided orderings. -/
theorem injectiveDepthFiber_card (G : Finset F) (t : ℕ) :
    (injectiveDepthFiber G t).card =
      (subsetCorePairs G t).card * (t.factorial ^ 2) := by
  have hcodes : (fullDepthPermutationCodes G t).card =
      (injectiveDepthFiber G t).card := by
    apply Finset.card_bij (fun z hz => orderedEnumerationCode z)
    · intro z hz
      rw [mem_injectiveDepthFiber_iff]
      refine ⟨orderedEnumerationCode_maps hz, ?_, ?_, ?_⟩
      · exact (enumSubset_injective z.1.1.1 (endpoint_card z.1.1)).comp z.2.1.injective
      · exact (enumSubset_injective z.1.2.1 (endpoint_card z.1.2)).comp z.2.2.injective
      · intro heq
        have hbag := congrArg (fun v => (valueBag v).toFinset) heq
        have hp := (Finset.mem_product.mp hz).1
        have hpne := (mem_subsetAccidents_iff.mp
          (mem_fullDepth_stratum_iff.mp hp).1).2
        apply hpne
        apply Subtype.ext
        simpa [orderedEnumerationCode, valueBag_comp_perm, enumPair,
          valueBag_enumSubset_toFinset] using hbag
    · intro z hz w hw heq
      exact orderedEnumerationCode_injOn G t hz hw heq
    · intro q hq
      obtain ⟨z, hz, heq⟩ := exists_code_eq_of_mem_injectiveDepthFiber hq
      exact ⟨z, hz, heq⟩
  rw [← hcodes, fullDepthPermutationCodes_card, fullDepthStratum_card_eq_corePairs]

/-- The complete full-depth fiber splits exactly into its set-core sector and the
repeated-coordinate defect. -/
theorem depthFiber_eq_core_mul_factorial_sq_add_defect (G : Finset F) (t : ℕ) :
    depthFiber G t t =
      (subsetCorePairs G t).card * (t.factorial ^ 2) + (repeatedDepthDefect G t).card := by
  rw [depthFiber, ← injectiveDepthFiber_card]
  simpa [injectiveDepthFiber, repeatedDepthDefect] using
    (Finset.card_filter_add_card_filter_not
      (s := (energySet G t).filter fun q => cancelDepth q = t)
      (p := fun q => Function.Injective q.1 ∧ Function.Injective q.2 ∧ q.1 ≠ q.2)).symm

/-- An upper bound on the whole depth fiber is equivalent, with no loss, to the corresponding
bound on the repeated-coordinate defect after removing the exact set-core contribution. -/
theorem depthFiber_le_core_mul_factorial_sq_add_iff (G : Finset F) (t D : ℕ) :
    depthFiber G t t ≤ (subsetCorePairs G t).card * (t.factorial ^ 2) + D ↔
      (repeatedDepthDefect G t).card ≤ D := by
  rw [depthFiber_eq_core_mul_factorial_sq_add_defect]
  exact Nat.add_le_add_iff_left

#print axioms enumSubset_comp_rangePermutation
#print axioms wordCore_mem_subsetCorePairs
#print axioms exists_code_eq_of_mem_injectiveDepthFiber
#print axioms fullDepthStratum_card_eq_corePairs
#print axioms injectiveDepthFiber_card
#print axioms depthFiber_eq_core_mul_factorial_sq_add_defect
#print axioms depthFiber_le_core_mul_factorial_sq_add_iff

end ArkLib.ProximityGap.Frontier.G159InjectiveDepthFiberExact
