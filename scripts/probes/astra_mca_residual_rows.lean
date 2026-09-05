/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import scripts.probes.astra_mca_polynomial_basis
import Mathlib.Tactic.FinCases

/-!
# Residual rows for the four-generator MCA construction

The four coefficients of a residual have the form (b,c,x*b,x*c).
This file connects those rows to the constructed pair-region basis.
It does not assert the MCA event or its probability.
-/

set_option autoImplicit false

namespace AstraMcaResidualRows

open Polynomial AstraMcaPolynomialBasis
open scoped BigOperators

variable {F : Type*} [Field F] [DecidableEq F]

/-- Multiplication by X adds the coordinate to the two-generator residual row. -/
def rowLift (x : F) (r : F × F) : Fin 4 → F := fun k =>
  if k = 0 then r.1 else if k = 1 then r.2 else if k = 2 then x * r.1 else x * r.2

omit [DecidableEq F] in
/-- A nonzero base row stays nonzero after adding its X multiples. -/
theorem row_lift_ne_zero (x : F) (r : F × F) (hr : r.1 ≠ 0 ∨ r.2 ≠ 0) :
    rowLift x r ≠ 0 := by
  intro h
  have h0 := congrFun h (0 : Fin 4)
  have h1 := congrFun h (1 : Fin 4)
  simp [rowLift] at h0 h1
  rcases hr with hr | hr
  · exact hr h0
  · exact hr h1

omit [DecidableEq F] in
/-- Proportional nonzero lifted rows must have the same evaluation coordinate. -/
theorem row_lift_same_coordinate (x y c : F) (r s : F × F)
    (hr : r.1 ≠ 0 ∨ r.2 ≠ 0) (h : rowLift x r = c • rowLift y s) : x = y := by
  have h0 := congrFun h (0 : Fin 4)
  have h1 := congrFun h (1 : Fin 4)
  have h2 := congrFun h (2 : Fin 4)
  have h3 := congrFun h (3 : Fin 4)
  simp [rowLift, Pi.smul_apply, smul_eq_mul] at h0 h1 h2 h3
  rcases hr with hr | hr
  · apply mul_right_cancel₀ hr
    calc
      x * r.1 = c * (y * s.1) := h2
      _ = y * (c * s.1) := by ring
      _ = y * r.1 := by rw [← h0]
  · apply mul_right_cancel₀ hr
    calc
      x * r.2 = c * (y * s.2) := h3
      _ = y * (c * s.2) := by ring
      _ = y * r.2 := by rw [← h1]

/-- The determinant evaluates to a nonzero value off the remaining pair regions. -/
theorem determinant_nonzero_off_domain {A B S : Finset F} {D : ℕ}
    (basis : PairRegionBasis A B S D) (x : F) (hx : x ∉ A ∪ B ∪ S) :
    (basis.f₀ * basis.g₁ - basis.f₁ * basis.g₀).eval x ≠ 0 := by
  rw [basis.determinant, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod]
  apply mul_ne_zero basis.scale_ne_zero
  apply Finset.prod_ne_zero_iff.mpr
  intro y hy
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  exact sub_ne_zero.mpr (fun h => hx (h.symm ▸ hy))

/-- The two basis triples never have all four nonconstant components vanish at one point. -/
theorem basis_values_not_all_zero {A B S : Finset F} {D : ℕ}
    (basis : PairRegionBasis A B S D) (x : F) :
    ¬ (basis.f₀.eval x = 0 ∧ basis.f₁.eval x = 0 ∧
      basis.g₀.eval x = 0 ∧ basis.g₁.eval x = 0) := by
  rintro ⟨hf₀, hf₁, hg₀, hg₁⟩
  by_cases hx : x ∈ A ∪ B ∪ S
  · have hsimple : (basis.f₀ * basis.g₁ - basis.f₁ * basis.g₀).derivative.eval x ≠ 0 := by
      rw [basis.determinant]
      exact simple_locator_derivative _ _ x basis.scale_ne_zero hx
    apply hsimple
    simp [Polynomial.derivative_sub, Polynomial.derivative_mul, hf₀, hf₁, hg₀, hg₁]
  · have hdet := determinant_nonzero_off_domain basis x hx
    apply hdet
    simp [hf₀, hf₁, hg₀, hg₁]

/-- Absent-core slots: owner 0 on S, owner 1 on B or I, and owner 2 on A or I. -/
def slotSet (A B S I : Finset F) : Finset (Fin 3 × F) :=
  ({0} : Finset (Fin 3)) ×ˢ S ∪
    ({1} : Finset (Fin 3)) ×ˢ (B ∪ I) ∪
    ({2} : Finset (Fin 3)) ×ˢ (A ∪ I)

/-- The two-generator residual for an owner at a point. -/
def baseRow {A B S : Finset F} {D : ℕ} (basis : PairRegionBasis A B S D)
    (k : Fin 3) (x : F) : F × F :=
  if k = 0 then (basis.f₀.eval x, basis.f₁.eval x)
  else if k = 1 then (-basis.f₀.eval x, -basis.f₁.eval x)
  else (-basis.g₀.eval x, -basis.g₁.eval x)

/-- The four-generator residual row at a slot. -/
def slotRow {A B S : Finset F} {D : ℕ} (basis : PairRegionBasis A B S D)
    (j : Fin 3 × F) : Fin 4 → F := rowLift j.2 (baseRow basis j.1 j.2)

omit [Field F] [DecidableEq F] in
private theorem tagged_disjoint (k l : Fin 3) (U V : Finset F) (hkl : k ≠ l) :
    Disjoint (({k} : Finset (Fin 3)) ×ˢ U) (({l} : Finset (Fin 3)) ×ˢ V) :=
  Finset.disjoint_left.mpr (fun _ hx hy => hkl
    ((Finset.mem_singleton.mp (Finset.mem_product.mp hx).1).symm.trans
      (Finset.mem_singleton.mp (Finset.mem_product.mp hy).1)))

omit [Field F] in
/-- There is one absent slot per pair point and two per private point. -/
theorem slot_count (A B S I : Finset F) (hI : Disjoint (A ∪ B ∪ S) I) :
    (slotSet A B S I).card = A.card + B.card + S.card + 2 * I.card := by
  have hAI : Disjoint A I := hI.mono_left (by
    intro x hx
    exact Finset.mem_union_left S (Finset.mem_union_left B hx))
  have hBI : Disjoint B I := hI.mono_left (by
    intro x hx
    exact Finset.mem_union_left S (Finset.mem_union_right A hx))
  have h01 := tagged_disjoint 0 1 S (B ∪ I) (by decide)
  have h02 := tagged_disjoint 0 2 S (A ∪ I) (by decide)
  have h12 := tagged_disjoint 1 2 (B ∪ I) (A ∪ I) (by decide)
  rw [slotSet, Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨h02, h12⟩),
    Finset.card_union_of_disjoint h01]
  simp only [Finset.card_product, Finset.card_singleton, one_mul,
    Finset.card_union_of_disjoint hAI, Finset.card_union_of_disjoint hBI]
  omega

/-- Every absent-core slot has a nonzero two-generator residual. -/
theorem base_row_nonzero {A B S I : Finset F} {D : ℕ}
    (basis : PairRegionBasis A B S D) (hI : Disjoint (A ∪ B ∪ S) I)
    (k : Fin 3) (x : F) (hx : (k, x) ∈ slotSet A B S I) :
    (baseRow basis k x).1 ≠ 0 ∨ (baseRow basis k x).2 ≠ 0 := by
  by_contra hz
  simp only [not_or, not_not] at hz
  simp only [slotSet, Finset.mem_union, Finset.mem_product, Finset.mem_singleton] at hx
  rcases hx with (⟨rfl, hx⟩ | ⟨rfl, hx⟩) | ⟨rfl, hx⟩
  · have hf : basis.f₀.eval x = 0 ∧ basis.f₁.eval x = 0 := by simpa [baseRow] using hz
    obtain ⟨hfg₀, hfg₁⟩ := basis.agrees x hx
    exact basis_values_not_all_zero basis x
      ⟨hf.1, hf.2, hfg₀.symm.trans hf.1, hfg₁.symm.trans hf.2⟩
  · have hf : basis.f₀.eval x = 0 ∧ basis.f₁.eval x = 0 := by simpa [baseRow] using hz
    rcases hx with hx | hx
    · obtain ⟨hg₀, hg₁⟩ := basis.g_roots x hx
      exact basis_values_not_all_zero basis x ⟨hf.1, hf.2, hg₀, hg₁⟩
    · have hdet := determinant_nonzero_off_domain basis x (fun h => Finset.disjoint_left.mp hI h hx)
      apply hdet
      simp [hf.1, hf.2]
  · have hg : basis.g₀.eval x = 0 ∧ basis.g₁.eval x = 0 := by simpa [baseRow] using hz
    rcases hx with hx | hx
    · obtain ⟨hf₀, hf₁⟩ := basis.f_roots x hx
      exact basis_values_not_all_zero basis x ⟨hf₀, hf₁, hg.1, hg.2⟩
    · have hdet := determinant_nonzero_off_domain basis x (fun h => Finset.disjoint_left.mp hI h hx)
      apply hdet
      simp [hg.1, hg.2]

/-- The lifted four-generator residual is nonzero at every absent-core slot. -/
theorem slot_row_nonzero {A B S I : Finset F} {D : ℕ}
    (basis : PairRegionBasis A B S D) (hI : Disjoint (A ∪ B ∪ S) I)
    (j : Fin 3 × F) (hj : j ∈ slotSet A B S I) : slotRow basis j ≠ 0 :=
  row_lift_ne_zero _ _ (base_row_nonzero basis hI j.1 j.2 hj)

omit [DecidableEq F] in
/-- Proportional lifted rows force the determinant of their base pairs to vanish. -/
theorem row_lift_determinant_zero (x y c : F) (r s : F × F)
    (h : rowLift x r = c • rowLift y s) : r.1 * s.2 - r.2 * s.1 = 0 := by
  have h0 := congrFun h (0 : Fin 4)
  have h1 := congrFun h (1 : Fin 4)
  simp [rowLift, Pi.smul_apply, smul_eq_mul] at h0 h1
  rw [h0, h1]
  ring

/-- All absent-core slots give projectively distinct four-generator residual rows. -/
theorem slot_rows_projectively_distinct {A B S I : Finset F} {D : ℕ}
    (basis : PairRegionBasis A B S D)
    (hAB : Disjoint A B) (hAS : Disjoint A S) (hBS : Disjoint B S)
    (hI : Disjoint (A ∪ B ∪ S) I)
    (j k : Fin 3 × F) (hj : j ∈ slotSet A B S I) (hk : k ∈ slotSet A B S I)
    (c : F) (h : slotRow basis j = c • slotRow basis k) : j = k := by
  obtain ⟨a, x⟩ := j
  obtain ⟨b, y⟩ := k
  have hxy := row_lift_same_coordinate x y c _ _ (base_row_nonzero basis hI a x hj) h
  subst y
  have hSI : Disjoint S I := hI.mono_left (by
    intro z hz
    exact Finset.mem_union_right (A ∪ B) hz)
  have hSBI : Disjoint S (B ∪ I) := Finset.disjoint_union_right.mpr ⟨hBS.symm, hSI⟩
  have hSAI : Disjoint S (A ∪ I) := Finset.disjoint_union_right.mpr ⟨hAS.symm, hSI⟩
  have hoverlap (hxB : x ∈ B ∪ I) (hxA : x ∈ A ∪ I) : x ∈ I := by
    rcases Finset.mem_union.mp hxB with hxB | hxI
    · rcases Finset.mem_union.mp hxA with hxA | hxI
      · exact False.elim (Finset.disjoint_left.mp hAB hxA hxB)
      · exact hxI
    · exact hxI
  fin_cases a <;> fin_cases b <;> simp [slotSet] at hj hk
  · rfl
  · exact False.elim (Finset.disjoint_left.mp hSBI hj (Finset.mem_union.mpr hk))
  · exact False.elim (Finset.disjoint_left.mp hSAI hj (Finset.mem_union.mpr hk))
  · exact False.elim (Finset.disjoint_left.mp hSBI hk (Finset.mem_union.mpr hj))
  · rfl
  · have hxI := hoverlap (Finset.mem_union.mpr hj) (Finset.mem_union.mpr hk)
    have hdet := determinant_nonzero_off_domain basis x (fun hx => Finset.disjoint_left.mp hI hx hxI)
    have hz := row_lift_determinant_zero x x c (baseRow basis 1 x) (baseRow basis 2 x) h
    apply False.elim
    apply hdet
    simpa [baseRow, Polynomial.eval_sub, Polynomial.eval_mul] using hz
  · exact False.elim (Finset.disjoint_left.mp hSAI hk (Finset.mem_union.mpr hj))
  · have hxI := hoverlap (Finset.mem_union.mpr hk) (Finset.mem_union.mpr hj)
    have hdet := determinant_nonzero_off_domain basis x (fun hx => Finset.disjoint_left.mp hI hx hxI)
    have hz := row_lift_determinant_zero x x c (baseRow basis 2 x) (baseRow basis 1 x) h
    have hrev : basis.g₀.eval x * basis.f₁.eval x - basis.g₁.eval x * basis.f₀.eval x = 0 := by
      simpa [baseRow] using hz
    apply False.elim
    apply hdet
    simp only [Polynomial.eval_sub, Polynomial.eval_mul]
    calc
      _ = -(basis.g₀.eval x * basis.f₁.eval x - basis.g₁.eval x * basis.f₀.eval x) := by ring
      _ = 0 := by rw [hrev, neg_zero]
  · rfl

end AstraMcaResidualRows

#print axioms AstraMcaResidualRows.row_lift_ne_zero
#print axioms AstraMcaResidualRows.row_lift_same_coordinate
#print axioms AstraMcaResidualRows.determinant_nonzero_off_domain
#print axioms AstraMcaResidualRows.basis_values_not_all_zero
#print axioms AstraMcaResidualRows.slot_count
#print axioms AstraMcaResidualRows.base_row_nonzero
#print axioms AstraMcaResidualRows.slot_row_nonzero
#print axioms AstraMcaResidualRows.row_lift_determinant_zero
#print axioms AstraMcaResidualRows.slot_rows_projectively_distinct
