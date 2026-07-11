/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G155PrimitiveAmbientEntropyGap

/-!
# G156: primitive core-pair swap parity

The left/right coordinate swap preserves balanced cores, proper balanced subcores, and primitive
cores.  On a balanced core it has no fixed point: equality with its swap would identify the two
nonempty disjoint supports.

Therefore swap is a fixed-point-free involution on every finite `primitiveCorePairs G t` census.
Using `Finset.sum_ninvolution` with the constant one function in `ZMod 2` proves that the primitive
census vanishes modulo two.

This is the first unconditional congruence on the primitive sequence isolated by G154.  Stronger
production divisibilities require the ANT46 projective-orbit classification, but parity is already
available at every depth and over every additive group.

Issue #466.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G156PrimitiveSwapParity

open ArkLib.ProximityGap.Frontier.G145LowerDepthMultiplicityEnvelope
open ArkLib.ProximityGap.Frontier.G147ConnectedBalancedCoreRecursion
open ArkLib.ProximityGap.Frontier.G152DepthFourCompositeCensus
open ArkLib.ProximityGap.Frontier.G153AllDepthCompositeConvolution

variable {F : Type*} [AddCommGroup F] [Fintype F] [DecidableEq F]

/-- Exchange the positive and negative sides of a core. -/
def swapCore (c : Finset F × Finset F) : Finset F × Finset F := (c.2, c.1)

@[simp] theorem swapCore_swapCore (c : Finset F × Finset F) :
    swapCore (swapCore c) = c := rfl

theorem balancedCore_swap {c : Finset F × Finset F} (hc : IsBalancedCore c) :
    IsBalancedCore (swapCore c) := by
  have hright : c.2.Nonempty := by
    apply Finset.card_pos.mp
    rw [← hc.2.1]
    exact Finset.card_pos.mpr hc.1
  exact ⟨hright, hc.2.1.symm, hc.2.2.1.symm, hc.2.2.2.symm⟩

theorem properBalancedSubcore_swap {c d : Finset F × Finset F}
    (hc : IsBalancedCore c) (hd : IsProperBalancedSubcore d c) :
    IsProperBalancedSubcore (swapCore d) (swapCore c) := by
  exact ⟨balancedCore_swap hd.1, hd.2.2.1, hd.2.1, properSubcore_right_ne hc hd⟩

theorem primitiveBalancedCore_swap {c : Finset F × Finset F}
    (hc : IsPrimitiveBalancedCore c) : IsPrimitiveBalancedCore (swapCore c) := by
  refine ⟨balancedCore_swap hc.1, ?_⟩
  rintro ⟨d, hd⟩
  have hback : IsProperBalancedSubcore (swapCore d) c := by
    simpa using properBalancedSubcore_swap (balancedCore_swap hc.1) hd
  exact hc.2 ⟨swapCore d, hback⟩

theorem swapCore_ne_of_balanced {c : Finset F × Finset F} (hc : IsBalancedCore c) :
    swapCore c ≠ c := by
  intro h
  apply balancedCore_left_ne_right hc
  exact (congrArg Prod.fst h).symm

theorem swapCore_mem_primitiveCorePairs {G : Finset F} {t : ℕ}
    {c : Finset F × Finset F} (hc : c ∈ primitiveCorePairs G t) :
    swapCore c ∈ primitiveCorePairs G t := by
  classical
  obtain ⟨hcCore, hcPrim⟩ := Finset.mem_filter.mp hc
  obtain ⟨hcL, hcR, hcDisj, hcSum, hcNe⟩ := mem_subsetCorePairs_iff.mp hcCore
  rw [primitiveCorePairs, Finset.mem_filter, mem_subsetCorePairs_iff]
  exact ⟨⟨hcR, hcL, hcDisj.symm, hcSum.symm, fun h => hcNe h.symm⟩,
    primitiveBalancedCore_swap hcPrim⟩

/-- **G156 capstone.** The primitive census is zero modulo two. -/
theorem primitiveCorePairs_card_modTwo (G : Finset F) (t : ℕ) :
    ((primitiveCorePairs G t).card : ZMod 2) = 0 := by
  classical
  have hsum := Finset.sum_involution
    (s := primitiveCorePairs G t)
    (f := fun _ : Finset F × Finset F => (1 : ZMod 2))
    (fun c _ => swapCore c)
    (fun _ _ => by
      change (1 : ZMod 2) + 1 = 0
      decide)
    (fun c hc _ => swapCore_ne_of_balanced (Finset.mem_filter.mp hc).2.1)
    (fun c hc => swapCore_mem_primitiveCorePairs hc)
    (fun c hc => swapCore_swapCore c)
  simpa using hsum

#print axioms balancedCore_swap
#print axioms properBalancedSubcore_swap
#print axioms primitiveBalancedCore_swap
#print axioms swapCore_ne_of_balanced
#print axioms swapCore_mem_primitiveCorePairs
#print axioms primitiveCorePairs_card_modTwo

end ArkLib.ProximityGap.Frontier.G156PrimitiveSwapParity
