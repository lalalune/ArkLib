/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G164UniformOrbitDivisor

/-!
# G165: primitive census modulo four is supported on signed-swap packets

This file applies G163--G164 to the concrete finite primitive census.  Under ambient negation
closure, coordinatewise negation preserves balanced cores, proper subcores, primitivity, and
membership in `primitiveCorePairs`.  Above depth two and without support two-torsion, removing the
signed-swap fixed sector leaves an invariant union of exact four-element Klein orbits.

Consequently the generic primitive census is divisible by four, and the complete primitive census
has the same residue modulo four as the signed-swap sector reduced by G162 to minimal zero-sum
supports.

Issue #466.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G165PrimitiveModFourResidue

open scoped BigOperators
open ArkLib.ProximityGap.Frontier.G147ConnectedBalancedCoreRecursion
open ArkLib.ProximityGap.Frontier.G145LowerDepthMultiplicityEnvelope
open ArkLib.ProximityGap.Frontier.G152DepthFourCompositeCensus
open ArkLib.ProximityGap.Frontier.G156PrimitiveSwapParity
open ArkLib.ProximityGap.Frontier.G162SignedSwapMinimalZeroSum
open ArkLib.ProximityGap.Frontier.G163KleinFourPrimitiveOrbits
open ArkLib.ProximityGap.Frontier.G164UniformOrbitDivisor

variable {F : Type*} [AddCommGroup F] [Fintype F] [DecidableEq F]

theorem disjoint_negFinset {S T : Finset F} (h : Disjoint S T) :
    Disjoint (negFinset S) (negFinset T) := by
  rw [Finset.disjoint_left]
  intro x hxS hxT
  obtain ⟨s, hs, hxs⟩ := Finset.mem_image.mp hxS
  obtain ⟨t, ht, hxt⟩ := Finset.mem_image.mp hxT
  have hst : s = t := neg_injective (hxs.trans hxt.symm)
  exact (Finset.disjoint_left.mp h) hs (hst ▸ ht)

theorem balancedCore_negCore {c : Finset F × Finset F} (hc : IsBalancedCore c) :
    IsBalancedCore (negCore c) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := hc.1
    exact ⟨-x, Finset.mem_image.mpr ⟨x, hx, rfl⟩⟩
  · simpa [negCore, negFinset_card] using hc.2.1
  · exact disjoint_negFinset hc.2.2.1
  · rw [negCore, sum_negFinset, sum_negFinset, hc.2.2.2]

theorem properBalancedSubcore_negCore {c d : Finset F × Finset F}
    (hd : IsProperBalancedSubcore d c) :
    IsProperBalancedSubcore (negCore d) (negCore c) := by
  refine ⟨balancedCore_negCore hd.1, negFinset_mono hd.2.1,
    negFinset_mono hd.2.2.1, ?_⟩
  intro h
  apply hd.2.2.2
  have := congrArg negFinset h
  simpa [negCore, negFinset_negFinset] using this

theorem primitiveBalancedCore_negCore {c : Finset F × Finset F}
    (hc : IsPrimitiveBalancedCore c) : IsPrimitiveBalancedCore (negCore c) := by
  refine ⟨balancedCore_negCore hc.1, ?_⟩
  rintro ⟨d, hd⟩
  have hback := properBalancedSubcore_negCore hd
  rw [negCore_negCore] at hback
  exact hc.2 ⟨negCore d, hback⟩

theorem negFinset_mem_powersetCard {G S : Finset F} {t : ℕ}
    (hnegG : ∀ x ∈ G, -x ∈ G) (hS : S ∈ G.powersetCard t) :
    negFinset S ∈ G.powersetCard t := by
  rw [Finset.mem_powersetCard]
  refine ⟨?_, by rw [negFinset_card, (Finset.mem_powersetCard.mp hS).2]⟩
  intro x hx
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hx
  exact hnegG s ((Finset.mem_powersetCard.mp hS).1 hs)

/-- Ambient negation closure makes the finite primitive census invariant under `negCore`. -/
theorem negCore_mem_primitiveCorePairs
    (G : Finset F) {t : ℕ} (hnegG : ∀ x ∈ G, -x ∈ G)
    {c : Finset F × Finset F} (hc : c ∈ primitiveCorePairs G t) :
    negCore c ∈ primitiveCorePairs G t := by
  classical
  rw [primitiveCorePairs, Finset.mem_filter] at hc ⊢
  obtain ⟨hcCore, hcPrim⟩ := hc
  rw [mem_subsetCorePairs_iff] at hcCore ⊢
  obtain ⟨hcL, hcR, hcDisj, hcSum, hcNe⟩ := hcCore
  have hbalNeg := balancedCore_negCore hcPrim.1
  refine ⟨⟨negFinset_mem_powersetCard hnegG hcL,
    negFinset_mem_powersetCard hnegG hcR, hbalNeg.2.2.1, hbalNeg.2.2.2, ?_⟩,
    primitiveBalancedCore_negCore hcPrim⟩
  intro h
  apply hcNe
  have := congrArg negFinset h
  simpa [negCore, negFinset_negFinset] using this

noncomputable def signedFixedPrimitiveCorePairs (G : Finset F) (t : ℕ) :
    Finset (Finset F × Finset F) :=
  (primitiveCorePairs G t).filter fun c => signedSwapCore c = c

noncomputable def genericPrimitiveCorePairs (G : Finset F) (t : ℕ) :
    Finset (Finset F × Finset F) :=
  (primitiveCorePairs G t).filter fun c => signedSwapCore c ≠ c

theorem signedSwapCore_eq_iff (c : Finset F × Finset F) :
    signedSwapCore c = c ↔ c.2 = negFinset c.1 := by
  constructor
  · intro h
    exact (congrArg Prod.snd h).symm
  · intro h
    apply Prod.ext
    · change negFinset c.2 = c.1
      rw [h, negFinset_negFinset]
    · exact h.symm

theorem signedFixedPrimitiveCorePairs_eq_signedSwapPrimitiveCorePairs
    (G : Finset F) (t : ℕ) :
    signedFixedPrimitiveCorePairs G t = signedSwapPrimitiveCorePairs G t := by
  classical
  ext c
  simp [signedFixedPrimitiveCorePairs, signedSwapPrimitiveCorePairs, signedSwapCore_eq_iff]

theorem signedFixedPrimitiveCorePairs_card_le_minimalZeroSumSupports
    (htwo : ∀ z : F, z + z = 0 → z = 0) (G : Finset F) (t : ℕ) :
    (signedFixedPrimitiveCorePairs G t).card ≤ (minimalZeroSumSupports G t).card := by
  rw [signedFixedPrimitiveCorePairs_eq_signedSwapPrimitiveCorePairs]
  exact signedSwapPrimitiveCorePairs_card_le_minimalZeroSumSupports htwo G t

theorem signedSwap_ne_of_mem_kleinOrbit {c d : Finset F × Finset F}
    (hc : signedSwapCore c ≠ c) (hd : d ∈ kleinOrbit c) : signedSwapCore d ≠ d := by
  simp only [kleinOrbit, Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl
  · exact hc
  · intro h
    apply hc
    have := congrArg swapCore h
    simpa [signedSwapCore, negCore_swapCore] using this
  · intro h
    apply hc
    have := congrArg negCore h
    simpa [signedSwapCore, negCore_swapCore] using this
  · intro h
    apply hc
    have h' : c = signedSwapCore c := by simpa using h
    exact h'.symm

theorem kleinOrbit_subset_genericPrimitiveCorePairs
    (G : Finset F) {t : ℕ} (hnegG : ∀ x ∈ G, -x ∈ G)
    {c : Finset F × Finset F} (hc : c ∈ genericPrimitiveCorePairs G t) :
    kleinOrbit c ⊆ genericPrimitiveCorePairs G t := by
  classical
  rw [genericPrimitiveCorePairs, Finset.mem_filter] at hc
  obtain ⟨hcPrim, hcSigned⟩ := hc
  intro d hd
  rw [genericPrimitiveCorePairs, Finset.mem_filter]
  refine ⟨?_, signedSwap_ne_of_mem_kleinOrbit hcSigned hd⟩
  simp only [kleinOrbit, Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl
  · exact hcPrim
  · exact swapCore_mem_primitiveCorePairs hcPrim
  · exact negCore_mem_primitiveCorePairs G hnegG hcPrim
  · exact swapCore_mem_primitiveCorePairs
      (negCore_mem_primitiveCorePairs G hnegG hcPrim)

/-- **Generic mod-four theorem.** Above depth two, every nonsigned primitive packet belongs to a
free four-element orbit. -/
theorem four_dvd_genericPrimitiveCorePairs_card
    (G : Finset F) {t : ℕ} (ht : 2 < t)
    (hnegG : ∀ x ∈ G, -x ∈ G) (hfreeG : ∀ x ∈ G, -x ≠ x) :
    4 ∣ (genericPrimitiveCorePairs G t).card := by
  classical
  apply four_dvd_card_of_kleinOrbit_closed (genericPrimitiveCorePairs G t)
    (fun _ hc => kleinOrbit_subset_genericPrimitiveCorePairs G hnegG hc)
  intro c hc
  rw [genericPrimitiveCorePairs, Finset.mem_filter] at hc
  obtain ⟨hcPrimMem, hcSigned⟩ := hc
  rw [primitiveCorePairs, Finset.mem_filter] at hcPrimMem
  obtain ⟨hcCore, hcPrim⟩ := hcPrimMem
  have hcard : c.1.card = t :=
    (Finset.mem_powersetCard.mp (mem_subsetCorePairs_iff.mp hcCore).1).2
  apply primitive_kleinOrbit_card_eq_four hcPrim (by omega) ?_ hcSigned
  intro z hz
  rw [Finset.mem_union] at hz
  rcases hz with hz | hz
  · exact hfreeG z ((Finset.mem_powersetCard.mp
      (mem_subsetCorePairs_iff.mp hcCore).1).1 hz)
  · exact hfreeG z ((Finset.mem_powersetCard.mp
      (mem_subsetCorePairs_iff.mp hcCore).2.1).1 hz)

theorem primitiveCorePairs_card_eq_signed_add_generic (G : Finset F) (t : ℕ) :
    (primitiveCorePairs G t).card =
      (signedFixedPrimitiveCorePairs G t).card + (genericPrimitiveCorePairs G t).card := by
  classical
  have hpart := Finset.card_filter_add_card_filter_not
    (s := primitiveCorePairs G t) (p := fun c => signedSwapCore c = c)
  simpa [signedFixedPrimitiveCorePairs, genericPrimitiveCorePairs] using hpart.symm

/-- **G165 capstone.** The primitive census modulo four is supported entirely on the signed-swap
fixed sector. -/
theorem primitiveCorePairs_modEq_signedFixed
    (G : Finset F) {t : ℕ} (ht : 2 < t)
    (hnegG : ∀ x ∈ G, -x ∈ G) (hfreeG : ∀ x ∈ G, -x ≠ x) :
    Nat.ModEq 4 (primitiveCorePairs G t).card
      (signedFixedPrimitiveCorePairs G t).card := by
  rw [Nat.ModEq, primitiveCorePairs_card_eq_signed_add_generic, Nat.add_mod]
  rw [Nat.dvd_iff_mod_eq_zero.mp
    (four_dvd_genericPrimitiveCorePairs_card G ht hnegG hfreeG)]
  simp

#print axioms primitiveBalancedCore_negCore
#print axioms negCore_mem_primitiveCorePairs
#print axioms kleinOrbit_subset_genericPrimitiveCorePairs
#print axioms four_dvd_genericPrimitiveCorePairs_card
#print axioms primitiveCorePairs_modEq_signedFixed
#print axioms signedFixedPrimitiveCorePairs_card_le_minimalZeroSumSupports

end ArkLib.ProximityGap.Frontier.G165PrimitiveModFourResidue
