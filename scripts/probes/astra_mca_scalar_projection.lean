/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import scripts.probes.astra_mca_evaluations

/-!
# Scalar projection of projectively distinct four-coordinate rows

Two univariate root-avoidance steps produce nonzero denominators and
distinct ratios. The field bound uses ordered pairs; no enumeration is used.
-/

set_option autoImplicit false

noncomputable section

namespace AstraMcaScalarProjection

open Polynomial AstraMcaEvaluations
open scoped BigOperators

variable {F : Type*} [Field F]

/-- A coefficient vector on the degree-three moment curve. -/
def momentVector (t : F) : Fin 4 → F := fun i => t ^ (i : ℕ)

/-- Restriction of a row functional to the moment curve. -/
def rowPolynomial (r : Fin 4 → F) : F[X] :=
  C (r 0) * X ^ 0 + C (r 1) * X ^ 1 + C (r 2) * X ^ 2 + C (r 3) * X ^ 3

theorem row_polynomial_degree (r : Fin 4 → F) : (rowPolynomial r).natDegree ≤ 3 := by
  unfold rowPolynomial
  apply natDegree_add_le_of_degree_le
  · apply natDegree_add_le_of_degree_le
    · apply natDegree_add_le_of_degree_le
      · exact (natDegree_C_mul_X_pow_le _ 0).trans (by decide)
      · exact (natDegree_C_mul_X_pow_le _ 1).trans (by decide)
    · exact (natDegree_C_mul_X_pow_le _ 2).trans (by decide)
  · exact natDegree_C_mul_X_pow_le _ 3

theorem row_polynomial_ne_zero (r : Fin 4 → F) (hr : r ≠ 0) : rowPolynomial r ≠ 0 := by
  intro h
  apply hr
  funext i
  have hc := congrArg (fun p : F[X] => p.coeff (i : ℕ)) h
  fin_cases i <;> simpa [rowPolynomial, coeff_C_mul_X_pow] using hc

theorem row_polynomial_eval (r : Fin 4 → F) (t : F) :
    (rowPolynomial r).eval t = rowDot r (momentVector t) := by
  simp [rowPolynomial, rowDot, momentVector]
  ring

/-- A family of nonzero polynomials with total degree below the field size has a common nonroot. -/
theorem exists_common_nonroot {J : Type*} [Fintype J] [Fintype F]
    (p : J → F[X]) (hp : ∀ j, p j ≠ 0) (d : ℕ)
    (hd : ∀ j, (p j).natDegree ≤ d) (hcard : d * Fintype.card J < Fintype.card F) :
    ∃ t : F, ∀ j, (p j).eval t ≠ 0 := by
  classical
  let product : F[X] := ∏ j, p j
  have hproduct : product ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun j _ => hp j)
  have hdegree : product.natDegree < Fintype.card F := by
    calc
      _ ≤ ∑ j, (p j).natDegree := natDegree_prod_le _ _
      _ ≤ ∑ _j : J, d := Finset.sum_le_sum (fun j _ => hd j)
      _ = d * Fintype.card J := by simp [Nat.mul_comm]
      _ < Fintype.card F := hcard
  have hex : ∃ t : F, product.eval t ≠ 0 := by
    by_contra! h
    exact hproduct (eq_zero_of_natDegree_lt_card_of_eval_eq_zero product
      Function.injective_id h hdegree)
  obtain ⟨t, ht⟩ := hex
  refine ⟨t, ?_⟩
  have hn : (∏ j, (p j).eval t) ≠ 0 := by simpa only [product, eval_prod] using ht
  exact fun j => Finset.prod_ne_zero_iff.mp hn j (Finset.mem_univ j)

/-- Moment-curve vectors suffice to avoid fewer than |F|/3 nonzero row functionals. -/
theorem exists_nonzero_denominators {J : Type*} [Fintype J] [Fintype F]
    (r : J → Fin 4 → F) (hr : ∀ j, r j ≠ 0)
    (hcard : 3 * Fintype.card J < Fintype.card F) :
    ∃ v : Fin 4 → F, ∀ j, rowDot (r j) v ≠ 0 := by
  obtain ⟨t, ht⟩ := exists_common_nonroot (fun j => rowPolynomial (r j))
    (fun j => row_polynomial_ne_zero _ (hr j)) 3 (fun j => row_polynomial_degree _) hcard
  exact ⟨momentVector t, fun j => by simpa only [row_polynomial_eval] using ht j⟩

/-- Ordered pairs of distinct row indices. -/
abbrev OffDiag (J : Type*) := {pair : J × J // pair.1 ≠ pair.2}

/-- Projective distinctness gives two coefficient vectors with finite, distinct row ratios. -/
theorem exists_injective_ratios {J : Type*} [Fintype J] [DecidableEq J] [Fintype F]
    (r : J → Fin 4 → F) (hr : ∀ j, r j ≠ 0)
    (hproj : ∀ i j, ∀ c : F, r i = c • r j → i = j)
    (hdenom : 3 * Fintype.card J < Fintype.card F)
    (hpairs : 3 * Fintype.card (OffDiag J) < Fintype.card F) :
    ∃ u0 u1 : Fin 4 → F, (∀ j, rowDot (r j) u1 ≠ 0) ∧
      Function.Injective (fun j => -rowDot (r j) u0 / rowDot (r j) u1) := by
  classical
  obtain ⟨u1, hu1⟩ := exists_nonzero_denominators r hr hdenom
  let cross : OffDiag J → Fin 4 → F := fun pair =>
    rowDot (r pair.val.2) u1 • r pair.val.1 - rowDot (r pair.val.1) u1 • r pair.val.2
  have hcross : ∀ pair, cross pair ≠ 0 := by
    intro pair hz
    apply pair.property
    apply hproj pair.val.1 pair.val.2 (rowDot (r pair.val.1) u1 / rowDot (r pair.val.2) u1)
    funext k
    have hk := congrFun hz k
    simp only [cross, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hk
    simp only [Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div]
    apply (eq_div_iff (hu1 pair.val.2)).mpr
    calc
      _ = rowDot (r pair.val.2) u1 * r pair.val.1 k := mul_comm _ _
      _ = _ := sub_eq_zero.mp hk
  obtain ⟨u0, hu0⟩ := exists_nonzero_denominators cross hcross hpairs
  refine ⟨u0, u1, hu1, ?_⟩
  intro i j hij
  by_contra hne
  let pair : OffDiag J := ⟨(i, j), hne⟩
  apply hu0 pair
  have heq := (div_eq_div_iff (hu1 i) (hu1 j)).mp hij
  have hzero : rowDot (r j) u1 * rowDot (r i) u0 -
      rowDot (r i) u1 * rowDot (r j) u0 = 0 := by
    calc
      _ = -( (-rowDot (r i) u0) * rowDot (r j) u1 -
        (-rowDot (r j) u0) * rowDot (r i) u1) := by ring
      _ = 0 := by rw [heq, sub_self, neg_zero]
  change rowDot (rowDot (r j) u1 • r i - rowDot (r i) u1 • r j) u0 = 0
  calc
    _ = rowDot (r j) u1 * rowDot (r i) u0 -
        rowDot (r i) u1 * rowDot (r j) u0 := by
      simp only [rowDot, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    _ = 0 := hzero

end AstraMcaScalarProjection

#print axioms AstraMcaScalarProjection.row_polynomial_degree
#print axioms AstraMcaScalarProjection.row_polynomial_ne_zero
#print axioms AstraMcaScalarProjection.row_polynomial_eval
#print axioms AstraMcaScalarProjection.exists_common_nonroot
#print axioms AstraMcaScalarProjection.exists_nonzero_denominators
#print axioms AstraMcaScalarProjection.exists_injective_ratios
