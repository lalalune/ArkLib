/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G202EnvelopeExponentOverhead

/-!
# G203: scalar-twisted generators for two-coset Stepanov

To treat distinct relations `x^t=α` and `(x-c)^t=β` without enlarging `t`, rescale each
G103F generator indexed by `(a,b,b')` by `α⁻ᵇ β⁻ᵇʹ`.  These are nonzero scalar
multiples, so linear independence and degree bounds are unchanged.  At a two-coset collision
point the formerly problematic factor becomes exactly

`α⁻ᵇβ⁻ᵇʹ x^{tb}(x-c)^{tb'} = 1`.

This is the algebraic core needed to port G103F's Hasse-condition argument to two distinct
multiplicative cosets while retaining the original subgroup exponent.

Issue #466.
-/

set_option autoImplicit false

open Polynomial

namespace ArkLib.ProximityGap.Frontier.G203TwoCosetTwistedGenerators

open ArkLib.ProximityGap.Frontier.G103FSubgroupCollisionBound

variable {p : ℕ} [Fact p.Prime] [NeZero p]

noncomputable def twistUnit {D B : ℕ} (α β : ZMod p) (hα : α ≠ 0) (hβ : β ≠ 0)
    (i : Fin D × Fin B × Fin B) : (ZMod p)ˣ :=
  (Units.mk0 α hα)⁻¹ ^ (i.2.1 : ℕ) * (Units.mk0 β hβ)⁻¹ ^ (i.2.2 : ℕ)

noncomputable def twistedGen {D B : ℕ} (t : ℕ) (c α β : ZMod p)
    (hα : α ≠ 0) (hβ : β ≠ 0) (i : Fin D × Fin B × Fin B) : (ZMod p)[X] :=
  (twistUnit α β hα hβ i : ZMod p) • gen t c i

/-- **Twisting preserves the Shkredov--Vyugin generator independence.** -/
theorem twistedGen_linearIndependent {D B : ℕ} (t : ℕ) (hD : 1 ≤ D) (hB : 1 ≤ B)
    (hDB : D * B ≤ t) (hp : t * B ≤ p) {c α β : ZMod p} (hc : c ≠ 0)
    (hα : α ≠ 0) (hβ : β ≠ 0) :
    LinearIndependent (ZMod p)
      (twistedGen t c α β hα hβ : (Fin D × Fin B × Fin B) → (ZMod p)[X]) := by
  have hli := gen_linearIndependent t hD hB hDB hp hc
  change LinearIndependent (ZMod p)
    (fun i : Fin D × Fin B × Fin B => twistUnit α β hα hβ i • gen t c i)
  exact hli.units_smul (twistUnit α β hα hβ)

theorem twistedGen_natDegree_le {D B : ℕ} (hD : 1 ≤ D) (hB : 1 ≤ B)
    (t : ℕ) (c α β : ZMod p) (hα : α ≠ 0) (hβ : β ≠ 0)
    (i : Fin D × Fin B × Fin B) :
    (twistedGen t c α β hα hβ i).natDegree ≤
      D - 1 + t * (B - 1) + t * (B - 1) := by
  unfold twistedGen
  exact (natDegree_smul_le _ _).trans (gen_natDegree_le hD hB t c i)

/-- The G103F degeneracy identity survives twisting, with the same scalar multiplying its
condition polynomial. -/
theorem twisted_key_identity {D B : ℕ} (t : ℕ) (c α β : ZMod p)
    (hα : α ≠ 0) (hβ : β ≠ 0) (n : ℕ) (i : Fin D × Fin B × Fin B) :
    X ^ n * (X - C c) ^ n * hasseDeriv n (twistedGen t c α β hα hβ i) =
      C (twistUnit α β hα hβ i : ZMod p) *
        (X ^ (t * (i.2.1 : ℕ)) * (X - C c) ^ (t * (i.2.2 : ℕ)) *
          condPoly t c n i) := by
  unfold twistedGen
  rw [map_smul, smul_eq_C_mul]
  calc
    _ = C (twistUnit α β hα hβ i : ZMod p) *
        (X ^ n * (X - C c) ^ n * hasseDeriv n (gen t c i)) := by ring
    _ = C (twistUnit α β hα hβ i : ZMod p) *
        (X ^ (t * (i.2.1 : ℕ)) * (X - C c) ^ (t * (i.2.2 : ℕ)) *
          condPoly t c n i) := by rw [key_identity]

/-- **The twisted relation factor evaluates to one on distinct cosets.** -/
theorem twistUnit_mul_relation_powers_eq_one {D B : ℕ} (t : ℕ)
    {c α β x : ZMod p} (hα : α ≠ 0) (hβ : β ≠ 0)
    (hx : x ^ t = α) (hxc : (x - c) ^ t = β) (i : Fin D × Fin B × Fin B) :
    (twistUnit α β hα hβ i : ZMod p) *
        (x ^ (t * (i.2.1 : ℕ)) * (x - c) ^ (t * (i.2.2 : ℕ))) = 1 := by
  rw [pow_mul, pow_mul, hx, hxc]
  unfold twistUnit
  change α⁻¹ ^ (i.2.1 : ℕ) * β⁻¹ ^ (i.2.2 : ℕ) *
    (α ^ (i.2.1 : ℕ) * β ^ (i.2.2 : ℕ)) = 1
  calc
    α⁻¹ ^ (i.2.1 : ℕ) * β⁻¹ ^ (i.2.2 : ℕ) *
        (α ^ (i.2.1 : ℕ) * β ^ (i.2.2 : ℕ)) =
      (α⁻¹ * α) ^ (i.2.1 : ℕ) * (β⁻¹ * β) ^ (i.2.2 : ℕ) := by ring
    _ = 1 := by rw [inv_mul_cancel₀ hα, inv_mul_cancel₀ hβ]; simp

#print axioms twistedGen_linearIndependent
#print axioms twistedGen_natDegree_le
#print axioms twisted_key_identity
#print axioms twistUnit_mul_relation_powers_eq_one

end ArkLib.ProximityGap.Frontier.G203TwoCosetTwistedGenerators
