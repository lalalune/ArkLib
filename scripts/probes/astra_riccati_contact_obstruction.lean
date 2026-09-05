/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import scripts.probes.astra_mca_polynomial_basis

/-!
# The derivative term cannot survive Riccati contact at the production profile

The hypotheses are the pure-R and pure-z coefficient conditions extracted
from the existing contact substitution. They force the derivative coefficient
to have too many roots, counted with multiplicity, at every positive contact
order. This excludes this interpolation shape; it is not a prize lower bound.
-/

set_option autoImplicit false

namespace AstraRiccatiContactObstruction

open Polynomial

variable {F : Type*} [Field F]

/-- Collect the exact local terms after the first-order contact substitution. -/
theorem riccati_contact_expansion {R : Type*} [CommRing R]
    (a b c d v t r z : R) :
    a + b * (v + t * r + z) + c * (v + t * r + z) ^ 2 + d * r =
      (a + b * v + c * v ^ 2) + r * (d + t * (b + 2 * v * c)) +
      r ^ 2 * t ^ 2 * c + z * (b + 2 * v * c) + 2 * r * z * t * c + z ^ 2 * c := by
  ring

/-- The two local coefficient conditions force a large power to divide D. -/
theorem local_derivative_divisibility (T D E : F[X]) (m : ℕ) (hm : 0 < m)
    (hR : T ^ m ∣ D + T * E) (hZ : T ^ (m - 2) ∣ E) :
    T ^ (max 1 (m - 1)) ∣ D := by
  by_cases hm1 : m = 1
  · subst m
    simp only [Nat.sub_self, pow_one] at *
    have hTE : T ∣ T * E := dvd_mul_right T E
    simpa using dvd_sub hR hTE
  · have hm2 : 2 ≤ m := by omega
    rw [max_eq_right (by omega : 1 ≤ m - 1)]
    have hpow : T ^ (m - 1) ∣ T ^ m := pow_dvd_pow T (by omega)
    have hTE : T ^ (m - 1) ∣ T * E := by
      obtain ⟨e, he⟩ := hZ
      refine ⟨e, ?_⟩
      rw [he]
      have hexp : m - 1 = (m - 2) + 1 := by omega
      rw [hexp, pow_succ]
      ring
    simpa using dvd_sub (hpow.trans hR) hTE

/-- Distinct nodes make the local powers coprime, so their product divides D. -/
theorem global_derivative_divisibility (S : Finset F) (D : F[X]) (E : F → F[X])
    (m : ℕ) (hm : 0 < m)
    (hR : ∀ x ∈ S, (X - C x) ^ m ∣ D + (X - C x) * E x)
    (hZ : ∀ x ∈ S, (X - C x) ^ (m - 2) ∣ E x) :
    (∏ x ∈ S, (X - C x) ^ (max 1 (m - 1))) ∣ D := by
  classical
  apply Finset.prod_dvd_of_coprime
  · intro x _ y _ hxy
    exact (Polynomial.isCoprime_X_sub_C_of_isUnit_sub
      (sub_ne_zero.mpr hxy).isUnit).pow
  · intro x hx
    exact local_derivative_divisibility (X - C x) D (E x) m hm (hR x hx) (hZ x hx)

/-- The forced divisor has its exact cardinality-times-multiplicity degree. -/
theorem forced_divisor_degree (S : Finset F) (q : ℕ) :
    (∏ x ∈ S, (X - C x) ^ q).natDegree = S.card * q := by
  classical
  rw [Polynomial.natDegree_prod_of_monic S _ fun x _ => (monic_X_sub_C x).pow q]
  simp [Polynomial.natDegree_pow]

/-- An exact production arithmetic gap, valid at every positive multiplicity. -/
theorem production_degree_gap (m : ℕ) (hm : 0 < m) :
    m * 715827883 - 536870911 < 1073741823 * max 1 (m - 1) := by
  by_cases hm1 : m = 1
  · subst m
    norm_num
  · have hm2 : 2 ≤ m := by omega
    rw [max_eq_right (by omega : 1 ≤ m - 1)]
    omega

/-- The Riccati derivative coefficient is zero for the production contact profile. -/
theorem production_derivative_zero (S : Finset F) (hS : S.card = 1073741823)
    (D : F[X]) (E : F → F[X]) (m : ℕ) (hm : 0 < m)
    (hdegree : D.natDegree + 536870910 < m * 715827883)
    (hR : ∀ x ∈ S, (X - C x) ^ m ∣ D + (X - C x) * E x)
    (hZ : ∀ x ∈ S, (X - C x) ^ (m - 2) ∣ E x) : D = 0 := by
  classical
  by_contra hD
  have hdiv := global_derivative_divisibility S D E m hm hR hZ
  have hle := Polynomial.natDegree_le_of_dvd hdiv hD
  rw [forced_divisor_degree, hS] at hle
  have hgap := production_degree_gap m hm
  omega

/-- A quadratic polynomial over F[X] cannot vanish at three distinct polynomials. -/
theorem quadratic_coefficients_zero_of_three (A B C f₀ f₁ f₂ : F[X])
    (h01 : f₀ ≠ f₁) (h02 : f₀ ≠ f₂) (h12 : f₁ ≠ f₂)
    (h0 : A + B * f₀ + C * f₀ ^ 2 = 0)
    (h1 : A + B * f₁ + C * f₁ ^ 2 = 0)
    (h2 : A + B * f₂ + C * f₂ ^ 2 = 0) : A = 0 ∧ B = 0 ∧ C = 0 := by
  have hB1 : B + C * (f₀ + f₁) = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_left (sub_ne_zero.mpr h01)
    calc
      (f₀ - f₁) * (B + C * (f₀ + f₁)) =
          (A + B * f₀ + C * f₀ ^ 2) - (A + B * f₁ + C * f₁ ^ 2) := by ring
      _ = 0 := by rw [h0, h1]; ring
  have hB2 : B + C * (f₀ + f₂) = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_left (sub_ne_zero.mpr h02)
    calc
      (f₀ - f₂) * (B + C * (f₀ + f₂)) =
          (A + B * f₀ + C * f₀ ^ 2) - (A + B * f₂ + C * f₂ ^ 2) := by ring
      _ = 0 := by rw [h0, h2]; ring
  have hC : C = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_right (sub_ne_zero.mpr h12)
    calc
      C * (f₁ - f₂) = (B + C * (f₀ + f₁)) - (B + C * (f₀ + f₂)) := by ring
      _ = 0 := by rw [hB1, hB2]; ring
  have hB : B = 0 := by simpa [hC] using hB1
  have hA : A = 0 := by simpa [hB, hC] using h0
  exact ⟨hA, hB, hC⟩

/-- A production contact source of Riccati shape with three solutions is zero. -/
theorem production_riccati_zero_of_three (S : Finset F) (hS : S.card = 1073741823)
    (a₀ a₁ a₂ d₁ f₀ f₁ f₂ : F[X]) (v : F → F) (m : ℕ) (hm : 0 < m)
    (hdegree : d₁.natDegree + 536870910 < m * 715827883)
    (hR : ∀ x ∈ S, (X - C x) ^ m ∣
      d₁ + (X - C x) * (a₁ + C (2 * v x) * a₂))
    (hZ : ∀ x ∈ S, (X - C x) ^ (m - 2) ∣ a₁ + C (2 * v x) * a₂)
    (h01 : f₀ ≠ f₁) (h02 : f₀ ≠ f₂) (h12 : f₁ ≠ f₂)
    (h0 : a₀ + a₁ * f₀ + a₂ * f₀ ^ 2 + d₁ * derivative f₀ = 0)
    (h1 : a₀ + a₁ * f₁ + a₂ * f₁ ^ 2 + d₁ * derivative f₁ = 0)
    (h2 : a₀ + a₁ * f₂ + a₂ * f₂ ^ 2 + d₁ * derivative f₂ = 0) :
    a₀ = 0 ∧ a₁ = 0 ∧ a₂ = 0 ∧ d₁ = 0 := by
  have hd := production_derivative_zero S hS d₁
    (fun x => a₁ + C (2 * v x) * a₂) m hm hdegree hR hZ
  obtain ⟨ha, hb, hc⟩ := quadratic_coefficients_zero_of_three a₀ a₁ a₂ f₀ f₁ f₂
    h01 h02 h12 (by simpa [hd] using h0) (by simpa [hd] using h1)
    (by simpa [hd] using h2)
  exact ⟨ha, hb, hc, hd⟩

#print axioms riccati_contact_expansion
#print axioms local_derivative_divisibility
#print axioms global_derivative_divisibility
#print axioms forced_divisor_degree
#print axioms production_degree_gap
#print axioms production_derivative_zero
#print axioms quadratic_coefficients_zero_of_three
#print axioms production_riccati_zero_of_three

end AstraRiccatiContactObstruction
