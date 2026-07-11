/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G156PrimitiveSwapParity

/-!
# G157: normalize primitive majorants to even values

G156 proves that every primitive core census is even.  This file turns that congruence into a
numerical improvement usable by G154.  Define `evenFloor N = N - (N mod 2)`, the largest even
natural at most `N`.  Whenever an even number is bounded by `N`, it is already bounded by
`evenFloor N`.

Consequently any raw primitive upper bound `P(t)` can be replaced, for free, by
`evenFloor (P(t))`.  The final theorem feeds this normalized sequence into G154's convolution
closure.  Future analytic/computational bounds therefore inherit the universal swap factor without
having to encode parity themselves.

Issue #466.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G157EvenPrimitiveMajorant

open ArkLib.ProximityGap.Frontier.G152DepthFourCompositeCensus
open ArkLib.ProximityGap.Frontier.G154PrimitiveMajorantClosure
open ArkLib.ProximityGap.Frontier.G156PrimitiveSwapParity

variable {F : Type*} [AddCommGroup F] [Fintype F] [DecidableEq F]

/-- Largest even natural number at most `N`. -/
def evenFloor (N : ℕ) : ℕ := N - N % 2

theorem evenFloor_le (N : ℕ) : evenFloor N ≤ N := Nat.sub_le _ _

theorem even_evenFloor (N : ℕ) : Even (evenFloor N) := by
  rw [even_iff_two_dvd, Nat.dvd_iff_mod_eq_zero]
  rcases Nat.mod_two_eq_zero_or_one N with h | h
  · simp [evenFloor, h]
  · simp [evenFloor, h]
    omega

/-- An even number below `N` is below the largest even number below `N`. -/
theorem le_evenFloor_of_even {n N : ℕ} (hn : Even n) (hle : n ≤ N) :
    n ≤ evenFloor N := by
  have hnmod : n % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp (even_iff_two_dvd.mp hn)
  rcases Nat.mod_two_eq_zero_or_one N with hN | hN
  · simp [evenFloor, hN]
    exact hle
  · simp [evenFloor, hN]
    have hnlt : n < N := by
      by_contra h
      have : n = N := by omega
      rw [this, hN] at hnmod
      omega
    omega

theorem primitiveCorePairs_card_even (G : Finset F) (t : ℕ) :
    Even (primitiveCorePairs G t).card := by
  have h := primitiveCorePairs_card_modTwo G t
  rw [ZMod.natCast_eq_zero_iff] at h
  exact even_iff_two_dvd.mpr h

/-- Every raw primitive majorant can be rounded down to its even floor. -/
theorem primitiveCorePairs_card_le_evenFloor
    (G : Finset F) (t P : ℕ) (hP : (primitiveCorePairs G t).card ≤ P) :
    (primitiveCorePairs G t).card ≤ evenFloor P :=
  le_evenFloor_of_even (primitiveCorePairs_card_even G t) hP

/-- **G157 capstone.** G154 may consume the parity-normalized primitive majorant without any extra
arithmetic hypothesis. -/
theorem corePairs_card_le_of_rawPrimitive_evenMajorant
    (G : Finset F) (P B : ℕ → ℕ)
    (hraw : ∀ t, (primitiveCorePairs G t).card ≤ P t)
    (hsuper : ∀ t, evenFloor (P t) +
      ∑ s ∈ Finset.Icc 2 (t - 2), B s * B (t - s) ≤ B t) :
    ∀ t, (ArkLib.ProximityGap.Frontier.G145LowerDepthMultiplicityEnvelope.subsetCorePairs
      G t).card ≤ B t := by
  exact corePairs_card_le_of_primitive_majorant G (fun t => evenFloor (P t)) B
    (fun t => primitiveCorePairs_card_le_evenFloor G t (P t) (hraw t)) hsuper

#print axioms even_evenFloor
#print axioms le_evenFloor_of_even
#print axioms primitiveCorePairs_card_even
#print axioms primitiveCorePairs_card_le_evenFloor
#print axioms corePairs_card_le_of_rawPrimitive_evenMajorant

end ArkLib.ProximityGap.Frontier.G157EvenPrimitiveMajorant
