/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import scripts.probes.astra_mca_polynomial_basis

/-!
# Completeness of the pair-region polynomial basis

Cramer's rule and the exact determinant locator show that every polynomial
pair with these prescribed agreements belongs to the constructed module.
The degree estimate distinguishes the two-deletion and four-deletion cases.
It does not prove distinctness of the two-generator cancellation directions.
-/

set_option autoImplicit false

namespace AstraMcaPairBasisComplete

open Polynomial AstraMcaPolynomialBasis

variable {F : Type*} [Field F] [DecidableEq F]

/-- The exact locator determinant of a pair-region basis is nonzero. -/
theorem basis_determinant_ne_zero {A B S : Finset F} {D : ℕ}
    (basis : PairRegionBasis A B S D) :
    basis.f₀ * basis.g₁ - basis.f₁ * basis.g₀ ≠ 0 := by
  rw [basis.determinant]
  exact mul_ne_zero (C_ne_zero.mpr basis.scale_ne_zero)
    (Polynomial.monic_prod_X_sub_C id (A ∪ B ∪ S)).ne_zero

/-- The two Cramer numerators vanish on the entire pair-region domain. -/
theorem cramer_numerators_vanish {A B S : Finset F} {D : ℕ}
    (basis : PairRegionBasis A B S D) (p q : F[X])
    (hp : ∀ x ∈ A, p.eval x = 0) (hq : ∀ x ∈ B, q.eval x = 0)
    (hpq : ∀ x ∈ S, p.eval x = q.eval x) :
    ∀ x ∈ A ∪ B ∪ S,
      (p * basis.g₁ - q * basis.f₁).eval x = 0 ∧
      (q * basis.f₀ - p * basis.g₀).eval x = 0 := by
  intro x hx
  rcases Finset.mem_union.mp hx with hx | hx
  · rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨h0, h1⟩ := basis.f_roots x hx
      simp [hp x hx, h0, h1]
    · obtain ⟨h0, h1⟩ := basis.g_roots x hx
      simp [hq x hx, h0, h1]
  · obtain ⟨h0, h1⟩ := basis.agrees x hx
    simp [hpq x hx, h0, h1]

/-- Cramer numerators have the sum of the candidate and basis degree bounds. -/
theorem cramer_numerator_degree {A B S : Finset F} {D T : ℕ}
    (basis : PairRegionBasis A B S D) (p q : F[X])
    (hp : p.natDegree ≤ T) (hq : q.natDegree ≤ T) :
    (p * basis.g₁ - q * basis.f₁).natDegree ≤ T + D ∧
    (q * basis.f₀ - p * basis.g₀).natDegree ≤ T + D := by
  constructor
  · apply (Polynomial.natDegree_sub_le _ _).trans
    exact max_le (Polynomial.natDegree_mul_le.trans (Nat.add_le_add hp basis.degree_g₁))
      (Polynomial.natDegree_mul_le.trans (Nat.add_le_add hq basis.degree_f₁))
  · apply (Polynomial.natDegree_sub_le _ _).trans
    exact max_le (Polynomial.natDegree_mul_le.trans (Nat.add_le_add hq basis.degree_f₀))
      (Polynomial.natDegree_mul_le.trans (Nat.add_le_add hp basis.degree_g₀))

/-- Dividing a vanishing numerator by the scaled locator preserves its degree bound. -/
theorem coefficient_from_locator (Ω : Finset F) (N : F[X]) (c : F) (hc : c ≠ 0)
    (T : ℕ) (hN : N.natDegree ≤ T) (hroots : ∀ x ∈ Ω, N.eval x = 0) :
    ∃ u : F[X], (C c * ∏ x ∈ Ω, (X - C x)) * u = N ∧
      u.natDegree ≤ T - Ω.card := by
  obtain ⟨w, hw, hd⟩ := cofactor_of_agreement N 0 Ω T
    (by simpa using hroots) hN (by simp)
  have heq : N = (∏ x ∈ Ω, (X - C x)) * w := by simpa using hw
  refine ⟨C c⁻¹ * w, ?_, (Polynomial.natDegree_C_mul_le _ _).trans hd⟩
  calc
    _ = (C c * C c⁻¹) * ((∏ x ∈ Ω, (X - C x)) * w) := by ring
    _ = N := by rw [← map_mul, mul_inv_cancel₀ hc, map_one, one_mul, ← heq]

/-- Every allowed pair is a polynomial combination of the two basis columns,
with a bound on the degrees of both coefficients. -/
theorem pair_basis_complete {A B S : Finset F} {D T : ℕ}
    (basis : PairRegionBasis A B S D) (p q : F[X])
    (hpA : ∀ x ∈ A, p.eval x = 0) (hqB : ∀ x ∈ B, q.eval x = 0)
    (hpqS : ∀ x ∈ S, p.eval x = q.eval x)
    (hp : p.natDegree ≤ T) (hq : q.natDegree ≤ T) :
    ∃ u v : F[X], p = u * basis.f₀ + v * basis.f₁ ∧
      q = u * basis.g₀ + v * basis.g₁ ∧
      u.natDegree ≤ T + D - (A ∪ B ∪ S).card ∧
      v.natDegree ≤ T + D - (A ∪ B ∪ S).card := by
  have hroots := cramer_numerators_vanish basis p q hpA hqB hpqS
  obtain ⟨hd0, hd1⟩ := cramer_numerator_degree basis p q hp hq
  obtain ⟨u, hu, hdu⟩ := coefficient_from_locator (A ∪ B ∪ S)
    (p * basis.g₁ - q * basis.f₁) basis.scale basis.scale_ne_zero (T + D) hd0
    (fun x hx => (hroots x hx).1)
  obtain ⟨v, hv, hdv⟩ := coefficient_from_locator (A ∪ B ∪ S)
    (q * basis.f₀ - p * basis.g₀) basis.scale basis.scale_ne_zero (T + D) hd1
    (fun x hx => (hroots x hx).2)
  rw [← basis.determinant] at hu hv
  have hdet := basis_determinant_ne_zero basis
  refine ⟨u, v, ?_, ?_, hdu, hdv⟩
  · apply mul_left_cancel₀ hdet
    calc
      _ = (p * basis.g₁ - q * basis.f₁) * basis.f₀ +
          (q * basis.f₀ - p * basis.g₀) * basis.f₁ := by ring
      _ = _ := by rw [← hu, ← hv]; ring
  · apply mul_left_cancel₀ hdet
    calc
      _ = (p * basis.g₁ - q * basis.f₁) * basis.g₀ +
          (q * basis.f₀ - p * basis.g₀) * basis.g₁ := by ring
      _ = _ := by rw [← hu, ← hv]; ring

/-- The polynomial coefficient pair in the representation is unique. -/
theorem pair_basis_coefficients_unique {A B S : Finset F} {D : ℕ}
    (basis : PairRegionBasis A B S D) (u v u' v' : F[X])
    (hf : u * basis.f₀ + v * basis.f₁ = u' * basis.f₀ + v' * basis.f₁)
    (hg : u * basis.g₀ + v * basis.g₁ = u' * basis.g₀ + v' * basis.g₁) :
    u = u' ∧ v = v' := by
  have hdet := basis_determinant_ne_zero basis
  constructor
  · apply mul_left_cancel₀ hdet
    calc
      _ = (u * basis.f₀ + v * basis.f₁) * basis.g₁ -
          (u * basis.g₀ + v * basis.g₁) * basis.f₁ := by ring
      _ = _ := by rw [hf, hg]; ring
  · apply mul_left_cancel₀ hdet
    calc
      _ = (u * basis.g₀ + v * basis.g₁) * basis.f₀ -
          (u * basis.f₀ + v * basis.f₁) * basis.g₀ := by ring
      _ = _ := by rw [hf, hg]; ring

/-- When the numerator degree cannot exceed the locator degree, coefficients
are constants: there are no further independent polynomial generators. -/
theorem pair_basis_constant_span {A B S : Finset F} {D T : ℕ}
    (basis : PairRegionBasis A B S D) (p q : F[X])
    (hpA : ∀ x ∈ A, p.eval x = 0) (hqB : ∀ x ∈ B, q.eval x = 0)
    (hpqS : ∀ x ∈ S, p.eval x = q.eval x)
    (hp : p.natDegree ≤ T) (hq : q.natDegree ≤ T)
    (hbudget : T + D ≤ (A ∪ B ∪ S).card) :
    ∃ u v : F, p = C u * basis.f₀ + C v * basis.f₁ ∧
      q = C u * basis.g₀ + C v * basis.g₁ := by
  obtain ⟨u, v, hpu, hqu, hu, hv⟩ := pair_basis_complete basis p q hpA hqB hpqS hp hq
  have hu0 : u.natDegree = 0 := by omega
  have hv0 : v.natDegree = 0 := by omega
  rw [Polynomial.eq_C_of_natDegree_eq_zero hu0,
    Polynomial.eq_C_of_natDegree_eq_zero hv0] at hpu hqu
  exact ⟨u.coeff 0, v.coeff 0, hpu, hqu⟩

/-- At the two-deletion production sizes, the full allowed pair space is the
constant span of the two columns. This assumes no collision-count theorem. -/
theorem production_two_deletion_constant_span {A B S : Finset F}
    (basis : PairRegionBasis A B S 536870911)
    (hAB : Disjoint A B) (hAS : Disjoint A S) (hBS : Disjoint B S)
    (hA : A.card = 357913940) (hB : B.card = 357913940) (hS : S.card = 357913942)
    (p q : F[X]) (hpA : ∀ x ∈ A, p.eval x = 0) (hqB : ∀ x ∈ B, q.eval x = 0)
    (hpqS : ∀ x ∈ S, p.eval x = q.eval x)
    (hp : p.natDegree ≤ 536870911) (hq : q.natDegree ≤ 536870911) :
    ∃ u v : F, p = C u * basis.f₀ + C v * basis.f₁ ∧
      q = C u * basis.g₀ + C v * basis.g₁ := by
  apply pair_basis_constant_span basis p q hpA hqB hpqS hp hq
  rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hAS, hBS⟩),
    Finset.card_union_of_disjoint hAB, hA, hB, hS]

/-- At the four-deletion production sizes, degree-one coefficient polynomials
already span all allowed pairs, explaining the four-generator construction. -/
theorem production_four_deletion_linear_span {A B S : Finset F}
    (basis : PairRegionBasis A B S 536870910)
    (hAB : Disjoint A B) (hAS : Disjoint A S) (hBS : Disjoint B S)
    (hA : A.card = 357913939) (hB : B.card = 357913939) (hS : S.card = 357913942)
    (p q : F[X]) (hpA : ∀ x ∈ A, p.eval x = 0) (hqB : ∀ x ∈ B, q.eval x = 0)
    (hpqS : ∀ x ∈ S, p.eval x = q.eval x)
    (hp : p.natDegree ≤ 536870911) (hq : q.natDegree ≤ 536870911) :
    ∃ u v : F[X], p = u * basis.f₀ + v * basis.f₁ ∧
      q = u * basis.g₀ + v * basis.g₁ ∧ u.natDegree ≤ 1 ∧ v.natDegree ≤ 1 := by
  have hcard : (A ∪ B ∪ S).card = 1073741820 := by
    rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hAS, hBS⟩),
      Finset.card_union_of_disjoint hAB, hA, hB, hS]
  obtain ⟨u, v, hp, hq, hu, hv⟩ := pair_basis_complete basis p q hpA hqB hpqS hp hq
  rw [hcard] at hu hv
  exact ⟨u, v, hp, hq, hu, hv⟩

/-- Any two degree-bounded bases for these regions differ by an invertible
constant matrix when twice the degree bound does not exceed the locator degree. -/
theorem constant_change_between_bases {A B S : Finset F} {D : ℕ}
    (basis other : PairRegionBasis A B S D) (hbudget : D + D ≤ (A ∪ B ∪ S).card) :
    ∃ a b c d : F,
      other.f₀ = C a * basis.f₀ + C b * basis.f₁ ∧
      other.g₀ = C a * basis.g₀ + C b * basis.g₁ ∧
      other.f₁ = C c * basis.f₀ + C d * basis.f₁ ∧
      other.g₁ = C c * basis.g₀ + C d * basis.g₁ ∧ a * d - b * c ≠ 0 := by
  obtain ⟨a, b, hf0, hg0⟩ := pair_basis_constant_span basis other.f₀ other.g₀
    (fun x hx => (other.f_roots x hx).1) (fun x hx => (other.g_roots x hx).1)
    (fun x hx => (other.agrees x hx).1) other.degree_f₀ other.degree_g₀ hbudget
  obtain ⟨c, d, hf1, hg1⟩ := pair_basis_constant_span basis other.f₁ other.g₁
    (fun x hx => (other.f_roots x hx).2) (fun x hx => (other.g_roots x hx).2)
    (fun x hx => (other.agrees x hx).2) other.degree_f₁ other.degree_g₁ hbudget
  refine ⟨a, b, c, d, hf0, hg0, hf1, hg1, ?_⟩
  have heq : other.f₀ * other.g₁ - other.f₁ * other.g₀ =
      C (a * d - b * c) * (basis.f₀ * basis.g₁ - basis.f₁ * basis.g₀) := by
    rw [hf0, hg0, hf1, hg1]
    simp only [map_sub, map_mul]
    ring
  intro hz
  apply basis_determinant_ne_zero other
  rw [heq, hz, map_zero, zero_mul]

omit [DecidableEq F] in
/-- An invertible constant basis change preserves all projective collisions. -/
theorem projective_collisions_preserved (a b c d r₀ r₁ s₀ s₁ : F)
    (hdet : a * d - b * c ≠ 0) :
    (a * r₀ + b * r₁) * (c * s₀ + d * s₁) -
      (c * r₀ + d * r₁) * (a * s₀ + b * s₁) = 0 ↔ r₀ * s₁ - r₁ * s₀ = 0 := by
  rw [change_basis_determinant, mul_eq_zero]
  simp only [hdet, false_or]

/-- Three cores in this pair-region construction satisfy an exact incidence budget. -/
theorem three_core_budget (a b s i n t : ℕ) (hcover : a + b + s + i = n)
    (h0 : t ≤ a + b + i) (h1 : t ≤ a + s) (h2 : t ≤ b + s) :
    3 * t + i ≤ 2 * n := by omega

/-- At the sharper production radius, three cores that each need just one
extra agreement permit at most two private coordinates. -/
theorem production_sharp_core_budget (a b s i : ℕ)
    (hcover : a + b + s + i = 1073741824)
    (h0 : 715827882 ≤ a + b + i) (h1 : 715827882 ≤ a + s)
    (h2 : 715827882 ≤ b + s) : i ≤ 2 := by
  have h := three_core_budget a b s i 1073741824 715827882 hcover h0 h1 h2
  omega

#print axioms basis_determinant_ne_zero
#print axioms cramer_numerators_vanish
#print axioms cramer_numerator_degree
#print axioms coefficient_from_locator
#print axioms pair_basis_complete
#print axioms pair_basis_coefficients_unique
#print axioms pair_basis_constant_span
#print axioms production_two_deletion_constant_span
#print axioms production_four_deletion_linear_span
#print axioms constant_change_between_bases
#print axioms projective_collisions_preserved
#print axioms three_core_budget
#print axioms production_sharp_core_budget

end AstraMcaPairBasisComplete
