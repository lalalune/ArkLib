/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G165PrimitiveModFourResidue

/-!
# G166: the signed-swap primitive sector is empty at even depth

For a signed core `(S,-S)` in the no-two-torsion regime, balance forces `sum S = 0` (G162).  If
`|S| = 2k`, choose any `k`-subset `A` and put `B = S \ A`.  Then `|A|=|B|=k` and
`sum A = -sum B`, so `(A,-B)` is a balanced subcore.  At depth above two it is proper, contradicting
primitivity.

Thus the complete G165 signed residue sector vanishes at every even depth above two.  The whole
primitive census—not merely its generic part—is therefore divisible by four.

Issue #466.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G166EvenDepthSignedSectorEmpty

open scoped BigOperators
open ArkLib.ProximityGap.Frontier.G147ConnectedBalancedCoreRecursion
open ArkLib.ProximityGap.Frontier.G152DepthFourCompositeCensus
open ArkLib.ProximityGap.Frontier.G162SignedSwapMinimalZeroSum
open ArkLib.ProximityGap.Frontier.G163KleinFourPrimitiveOrbits
open ArkLib.ProximityGap.Frontier.G165PrimitiveModFourResidue

variable {F : Type*} [AddCommGroup F] [Fintype F] [DecidableEq F]

/-- An equal-half split of a zero-sum support produces a balanced mixed signed subcore. -/
theorem halfSplit_balanced {S A : Finset F} {k : ℕ}
    (hSsigned : IsBalancedCore (signedCore S))
    (hA : A ⊆ S) (hAcard : A.card = k) (hScard : S.card = 2 * k)
    (hSsum : (∑ x ∈ S, x) = 0) :
    IsBalancedCore (A, negFinset (S \ A)) := by
  have hBcard : (S \ A).card = k := by
    rw [Finset.card_sdiff_of_subset hA, hScard, hAcard]
    omega
  have hk : 0 < k := by
    by_contra hk0
    have : S.card = 0 := by omega
    exact hSsigned.1.ne_empty (Finset.card_eq_zero.mp this)
  refine ⟨Finset.card_pos.mp (hAcard ▸ hk), ?_, ?_, ?_⟩
  · rw [negFinset_card, hAcard, hBcard]
  · exact hSsigned.2.2.1.mono hA (negFinset_mono Finset.sdiff_subset)
  · rw [sum_negFinset]
    have hsum := Finset.sum_sdiff hA (f := fun x : F => x)
    have hz : (∑ x ∈ S \ A, x) + ∑ x ∈ A, x = 0 := hsum.trans hSsum
    exact eq_neg_of_add_eq_zero_right hz

/-- Every even signed balanced core above depth two has a proper balanced equal-half subcore. -/
theorem exists_proper_halfSplit_subcore
    (htwo : ∀ z : F, z + z = 0 → z = 0) {S : Finset F} {k : ℕ}
    (hbal : IsBalancedCore (signedCore S)) (hcard : S.card = 2 * k)
    (hdepth : 2 < S.card) : ∃ d, IsProperBalancedSubcore d (signedCore S) := by
  have hk : k ≤ S.card := by omega
  obtain ⟨A, hAS, hAcard⟩ := Finset.exists_subset_card_eq hk
  let d : Finset F × Finset F := (A, negFinset (S \ A))
  have hsum := sum_eq_zero_of_signedCore_balanced htwo hbal
  have hdBal : IsBalancedCore d := halfSplit_balanced hbal hAS hAcard hcard hsum
  refine ⟨d, hdBal, hAS, negFinset_mono Finset.sdiff_subset, ?_⟩
  intro hEq
  have hcards := congrArg Finset.card hEq
  change A.card = S.card at hcards
  rw [hAcard, hcard] at hcards
  have hkpos : 0 < k := by omega
  omega

/-- **Pointwise G166 capstone.** No signed-swap primitive packet has even depth above two. -/
theorem not_signedCore_primitive_of_even_depth
    (htwo : ∀ z : F, z + z = 0 → z = 0) {S : Finset F}
    (heven : Even S.card) (hdepth : 2 < S.card) :
    ¬IsPrimitiveBalancedCore (signedCore S) := by
  intro hprim
  obtain ⟨k, hk⟩ := heven
  have hcard : S.card = 2 * k := by omega
  exact hprim.2 (exists_proper_halfSplit_subcore htwo hprim.1 hcard hdepth)

/-- The finite signed-fixed primitive sector is empty at even depths above two. -/
theorem signedFixedPrimitiveCorePairs_eq_empty_of_even
    (htwo : ∀ z : F, z + z = 0 → z = 0) (G : Finset F) {t : ℕ}
    (heven : Even t) (ht : 2 < t) : signedFixedPrimitiveCorePairs G t = ∅ := by
  classical
  rw [Finset.eq_empty_iff_forall_notMem]
  intro c hc
  rw [signedFixedPrimitiveCorePairs, Finset.mem_filter] at hc
  obtain ⟨hcPrimMem, hcSigned⟩ := hc
  rw [primitiveCorePairs, Finset.mem_filter] at hcPrimMem
  obtain ⟨hcCore, hcPrim⟩ := hcPrimMem
  have hEq : c = signedCore c.1 := by
    apply Prod.ext
    · rfl
    · exact (signedSwapCore_eq_iff c).mp hcSigned
  rw [hEq] at hcPrim
  apply not_signedCore_primitive_of_even_depth htwo ?_ ?_ hcPrim
  · simpa [(Finset.mem_powersetCard.mp
      (ArkLib.ProximityGap.Frontier.G145LowerDepthMultiplicityEnvelope.mem_subsetCorePairs_iff.mp
        hcCore).1).2] using heven
  · have hcard := (Finset.mem_powersetCard.mp
      (ArkLib.ProximityGap.Frontier.G145LowerDepthMultiplicityEnvelope.mem_subsetCorePairs_iff.mp
        hcCore).1).2
    omega

/-- **G166 finite capstone.** At every even depth above two, the complete primitive census is
divisible by four. -/
theorem four_dvd_primitiveCorePairs_card_of_even
    (htwo : ∀ z : F, z + z = 0 → z = 0)
    (G : Finset F) {t : ℕ} (heven : Even t) (ht : 2 < t)
    (hnegG : ∀ x ∈ G, -x ∈ G) (hfreeG : ∀ x ∈ G, -x ≠ x) :
    4 ∣ (primitiveCorePairs G t).card := by
  have hgeneric := four_dvd_genericPrimitiveCorePairs_card G ht hnegG hfreeG
  rw [primitiveCorePairs_card_eq_signed_add_generic,
    signedFixedPrimitiveCorePairs_eq_empty_of_even htwo G heven ht]
  simpa using hgeneric

#print axioms halfSplit_balanced
#print axioms not_signedCore_primitive_of_even_depth
#print axioms signedFixedPrimitiveCorePairs_eq_empty_of_even
#print axioms four_dvd_primitiveCorePairs_card_of_even

end ArkLib.ProximityGap.Frontier.G166EvenDepthSignedSectorEmpty
