/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G162SignedSwapMinimalZeroSum

/-!
# G163: exact four-element orbits for generic primitive packets

The commuting involutions endpoint-swap and coordinatewise negation generate a Klein-four orbit.
G161 eliminates negation-fixed primitive packets above depth two, while G162 isolates signed-swap
fixed packets as minimal zero-sum supports.  This file proves the remaining packets have exact
four-element orbits.

The result is pointwise and characteristic-free: once swap, negation, and signed swap each have no
fixed point, all four transforms are pairwise distinct.  The primitive specialization discharges
the swap and negation conditions, leaving precisely the G162 signed-swap residual.

Issue #466.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G163KleinFourPrimitiveOrbits

open ArkLib.ProximityGap.Frontier.G147ConnectedBalancedCoreRecursion
open ArkLib.ProximityGap.Frontier.G156PrimitiveSwapParity
open ArkLib.ProximityGap.Frontier.G161NegationStabilizerRigidity
open ArkLib.ProximityGap.Frontier.G162SignedSwapMinimalZeroSum

variable {F : Type*} [AddCommGroup F] [Fintype F] [DecidableEq F]

def negCore (c : Finset F × Finset F) : Finset F × Finset F :=
  (negFinset c.1, negFinset c.2)

def signedSwapCore (c : Finset F × Finset F) : Finset F × Finset F :=
  swapCore (negCore c)

def kleinOrbit (c : Finset F × Finset F) : Finset (Finset F × Finset F) :=
  {c, swapCore c, negCore c, signedSwapCore c}

theorem negFinset_negFinset (S : Finset F) : negFinset (negFinset S) = S := by
  ext x
  simp [negFinset]

@[simp] theorem negCore_negCore (c : Finset F × Finset F) : negCore (negCore c) = c := by
  simp [negCore, negFinset_negFinset]

theorem negCore_swapCore (c : Finset F × Finset F) :
    negCore (swapCore c) = swapCore (negCore c) := rfl

@[simp] theorem signedSwapCore_signedSwapCore (c : Finset F × Finset F) :
    signedSwapCore (signedSwapCore c) = c := by
  simp [signedSwapCore, negCore_swapCore]

theorem swapCore_signedSwapCore (c : Finset F × Finset F) :
    swapCore (signedSwapCore c) = negCore c := by
  simp [signedSwapCore]

theorem negCore_signedSwapCore (c : Finset F × Finset F) :
    negCore (signedSwapCore c) = swapCore c := by
  simp [signedSwapCore, negCore_swapCore]

/-- Three nontrivial fixed-point exclusions force all four Klein transforms to be distinct. -/
theorem kleinOrbit_card_eq_four_of_no_fixed
    (c : Finset F × Finset F)
    (hswap : swapCore c ≠ c) (hneg : negCore c ≠ c)
    (hsigned : signedSwapCore c ≠ c) : (kleinOrbit c).card = 4 := by
  have h_swap_neg : swapCore c ≠ negCore c := by
    intro h
    apply hsigned
    calc
      signedSwapCore c = swapCore (negCore c) := rfl
      _ = swapCore (swapCore c) := by rw [← h]
      _ = c := swapCore_swapCore c
  have h_swap_signed : swapCore c ≠ signedSwapCore c := by
    intro h
    apply hneg
    calc
      negCore c = swapCore (signedSwapCore c) := (swapCore_signedSwapCore c).symm
      _ = swapCore (swapCore c) := by rw [← h]
      _ = c := swapCore_swapCore c
  have h_neg_signed : negCore c ≠ signedSwapCore c := by
    intro h
    apply hswap
    calc
      swapCore c = negCore (signedSwapCore c) := (negCore_signedSwapCore c).symm
      _ = negCore (negCore c) := by rw [← h]
      _ = c := negCore_negCore c
  simp [kleinOrbit, hswap, hneg, hsigned, h_swap_neg, h_swap_signed, h_neg_signed,
    Ne.symm hswap, Ne.symm hneg, Ne.symm hsigned, Ne.symm h_swap_neg,
    Ne.symm h_swap_signed, Ne.symm h_neg_signed]

/-- **G163 capstone.** Above depth two, a primitive packet outside the signed-swap class has a
free four-element swap/negation orbit. -/
theorem primitive_kleinOrbit_card_eq_four {c : Finset F × Finset F}
    (hc : IsPrimitiveBalancedCore c) (hdepth : 2 < c.1.card)
    (hfree : ∀ z ∈ c.1 ∪ c.2, -z ≠ z)
    (hsigned : signedSwapCore c ≠ c) : (kleinOrbit c).card = 4 := by
  apply kleinOrbit_card_eq_four_of_no_fixed c
  · exact swapCore_ne_of_balanced hc.1
  · intro hneg
    apply not_primitive_negation_stable_of_two_lt hc hdepth hfree
    constructor
    · exact congrArg Prod.fst hneg
    · exact congrArg Prod.snd hneg
  · exact hsigned

/-- The only way a primitive orbit above depth two can fail to have size four is the signed-swap
fixed class isolated by G162. -/
theorem primitive_kleinOrbit_card_ne_four_iff_signed {c : Finset F × Finset F}
    (hc : IsPrimitiveBalancedCore c) (hdepth : 2 < c.1.card)
    (hfree : ∀ z ∈ c.1 ∪ c.2, -z ≠ z) :
    (kleinOrbit c).card ≠ 4 ↔ signedSwapCore c = c := by
  constructor
  · intro hcard
    by_contra hsigned
    exact hcard (primitive_kleinOrbit_card_eq_four hc hdepth hfree hsigned)
  · intro hsigned hcard
    have hmem : signedSwapCore c ∈ kleinOrbit c := by simp [kleinOrbit]
    rw [hsigned] at hmem
    have hsub : kleinOrbit c ⊆ {c, swapCore c, negCore c} := by
      intro z hz
      simp only [kleinOrbit, Finset.mem_insert, Finset.mem_singleton] at hz ⊢
      rcases hz with rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
      · exact Or.inl hsigned
    have hle := Finset.card_le_card hsub
    have hthree : ({c, swapCore c, negCore c} :
        Finset (Finset F × Finset F)).card ≤ 3 := by
      have htwo := Finset.card_insert_le (swapCore c)
        ({negCore c} : Finset (Finset F × Finset F))
      calc
        _ ≤ ({swapCore c, negCore c} : Finset (Finset F × Finset F)).card + 1 :=
          Finset.card_insert_le _ _
        _ ≤ ({negCore c} : Finset (Finset F × Finset F)).card + 1 + 1 := by
          omega
        _ ≤ 3 := by simp
    rw [hcard] at hle
    omega

#print axioms kleinOrbit_card_eq_four_of_no_fixed
#print axioms primitive_kleinOrbit_card_eq_four
#print axioms primitive_kleinOrbit_card_ne_four_iff_signed

end ArkLib.ProximityGap.Frontier.G163KleinFourPrimitiveOrbits
