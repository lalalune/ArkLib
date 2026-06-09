
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Finset.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.Field.Basic

open Polynomial
open Finset

section NormTorus

variable {F : Type*} [Field F]
variable (q : ℕ)
variable (K : Set F)
variable (v : F)


lemma c_sq_eq_inv_v_pow (c : F) (hcK : c ∈ K) (hv_not_zero : v ≠ 0)
  (hK : ∀ x ∈ K, x^q = x)
  (h_torus : (c * v)^(q+1) = 1) : c^2 = (v^(q+1))⁻¹ := by
  have h1 : (c * v)^(q+1) = c^(q+1) * v^(q+1) := mul_pow c v (q+1)
  have h2 : c^(q+1) = c^q * c := by rw [pow_add, pow_one]
  have h3 : c^q = c := hK c hcK
  rw [h1, h2, h3] at h_torus
  have h4 : c * c * v^(q+1) = 1 := h_torus
  have h5 : c^2 * v^(q+1) = 1 := by
    calc c^2 * v^(q+1) = (c * c) * v^(q+1) := by rw [sq]
         _ = 1 := h4
  calc c^2 = c^2 * (v^(q+1) * (v^(q+1))⁻¹) := by
          have hv_pow_ne_zero : v^(q+1) ≠ 0 := pow_ne_zero _ hv_not_zero
          rw [mul_inv_cancel₀ hv_pow_ne_zero, mul_one]
       _ = (c^2 * v^(q+1)) * (v^(q+1))⁻¹ := by rw [← mul_assoc]
       _ = 1 * (v^(q+1))⁻¹ := by rw [h5]
       _ = (v^(q+1))⁻¹ := one_mul _

end NormTorus
