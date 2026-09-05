/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic.Ring

/-!
# Polynomial algebra for the four-deletion MCA construction

The initial determinant identity, constant changes of basis, cofactor
independence, fixed-anchor selection, and preservation of roots, relations
and determinants under two selected point deletions are formalized here.
See docs/kb/astra_mca_polynomial_basis-2026-09-05.md for their place in the
construction and the remaining assembly. No threshold theorem or complete
production construction is asserted by this file.
-/

set_option autoImplicit false

namespace AstraMcaPolynomialBasis

open Polynomial

section RingIdentities

variable {R : Type*} [CommRing R]

/-- The initial two-generator determinant is independent of the interpolant h. -/
theorem initial_determinant (t h i j : R)
    (hi : i * i = -1) (hj : j * (1 - i) = 1) :
    ((t - 1) * (j * (t - i) + (1 + i) * h)) * (2 * (t - i) * (t + i)) -
      ((t - 1) * (1 + i) * (t + i)) * (-(t - i) * (j * (1 - t) - 2 * h)) =
        t ^ 4 - 1 := by
  have factor : (1 + i) * (1 - t) + 2 * (t - i) = (1 - i) * (1 + t) := by ring
  calc
    _ = (t - 1) * (t - i) * (t + i) * j *
        ((1 + i) * (1 - t) + 2 * (t - i)) := by ring
    _ = (t - 1) * (t - i) * (t + i) * (j * (1 - i)) * (1 + t) := by
      rw [factor]
      ring
    _ = (t - 1) * (t - i) * (t + i) * (1 + t) := by rw [hj, mul_one]
    _ = (t * t - 1) * (t * t - i * i) := by ring
    _ = (t * t - 1) * (t * t + 1) := by rw [hi]; ring
    _ = t ^ 4 - 1 := by ring

/-- A constant change of two columns multiplies their determinant by its determinant. -/
theorem change_basis_determinant (f₀ f₁ g₀ g₁ a b c d : R) :
    (a * f₀ + b * f₁) * (c * g₀ + d * g₁) -
      (c * f₀ + d * f₁) * (a * g₀ + b * g₁) =
        (a * d - b * c) * (f₀ * g₁ - f₁ * g₀) := by ring

/-- Exact division of the two columns divides their determinant by the two factors. -/
theorem divided_determinant (f₀ f₁ g₀ g₁ a b c d x y u₀ u₁ v₀ v₁ : R)
    (hf₀ : a * f₀ + b * f₁ = x * u₀)
    (hg₀ : a * g₀ + b * g₁ = x * v₀)
    (hf₁ : c * f₀ + d * f₁ = y * u₁)
    (hg₁ : c * g₀ + d * g₁ = y * v₁) :
    x * y * (u₀ * v₁ - u₁ * v₀) =
      (a * d - b * c) * (f₀ * g₁ - f₁ * g₀) := by
  calc
    _ = (x * u₀) * (y * v₁) - (y * u₁) * (x * v₀) := by ring
    _ = (a * f₀ + b * f₁) * (c * g₀ + d * g₁) -
        (c * f₀ + d * f₁) * (a * g₀ + b * g₁) := by rw [hf₀, hg₁, hf₁, hg₀]
    _ = _ := change_basis_determinant f₀ f₁ g₀ g₁ a b c d

end RingIdentities

section PolynomialAnchors

variable {F : Type*} [Field F] [DecidableEq F]

/-- Independence of two polynomials under constant scalar combinations. -/
def IndependentPair (w₀ w₁ : F[X]) : Prop :=
  ∀ a b : F, a • w₀ + b • w₁ = 0 → a = 0 ∧ b = 0

/-- The determinant and root-count conditions force independence of the difference cofactors. -/
theorem cofactor_pair_independent (f₀ f₁ g₀ g₁ w₀ w₁ L : F[X])
    (A B : Finset F)
    (hf₀ : ∀ x ∈ A, f₀.eval x = 0) (hf₁ : ∀ x ∈ A, f₁.eval x = 0)
    (hg₀ : ∀ x ∈ B, g₀.eval x = 0) (hg₁ : ∀ x ∈ B, g₁.eval x = 0)
    (hrel₀ : f₀ = g₀ + L * w₀) (hrel₁ : f₁ = g₁ + L * w₁)
    (hdegree : max f₀.natDegree f₁.natDegree < (A ∪ B).card)
    (hdet : f₀ * g₁ - f₁ * g₀ ≠ 0) : IndependentPair w₀ w₁ := by
  classical
  intro a b hab
  let p : F[X] := a • f₀ + b • f₁
  let q : F[X] := a • g₀ + b • g₁
  have hpq : p = q := by
    calc
      p = q + L * (a • w₀ + b • w₁) := by
        simp only [p, q, Polynomial.smul_eq_C_mul]
        rw [hrel₀, hrel₁]
        ring
      _ = q := by rw [hab, mul_zero, add_zero]
  have hpdegree : p.natDegree < (A ∪ B).card := by
    apply lt_of_le_of_lt (Polynomial.natDegree_add_le _ _)
    apply lt_of_le_of_lt (max_le_max
      (Polynomial.natDegree_smul_le a f₀) (Polynomial.natDegree_smul_le b f₁))
    exact hdegree
  have hpzero : p = 0 := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' p (A ∪ B)
    (fun x hx => by
      rcases Finset.mem_union.mp hx with hx | hx
      · simp [p, hf₀ x hx, hf₁ x hx]
      · rw [hpq]
        simp [q, hg₀ x hx, hg₁ x hx]) hpdegree
  have hqzero : q = 0 := hpq.symm.trans hpzero
  have ha : C a * (f₀ * g₁ - f₁ * g₀) = 0 := by
    calc
      _ = p * g₁ - f₁ * q := by simp only [p, q, Polynomial.smul_eq_C_mul]; ring
      _ = 0 := by rw [hpzero, hqzero]; ring
  have hb : C b * (f₀ * g₁ - f₁ * g₀) = 0 := by
    calc
      _ = f₀ * q - p * g₀ := by simp only [p, q, Polynomial.smul_eq_C_mul]; ring
      _ = 0 := by rw [hpzero, hqzero]; ring
  constructor
  · exact Polynomial.C_eq_zero.mp ((mul_eq_zero.mp ha).resolve_right hdet)
  · exact Polynomial.C_eq_zero.mp ((mul_eq_zero.mp hb).resolve_right hdet)

/-- Every fixed nonzero evaluation row has a projectively different partner in a large root set. -/
theorem exists_separated_at_anchor (w₀ w₁ : F[X]) (A : Finset F) (eta : F)
    (hind : IndependentPair w₀ w₁)
    (hdeg₀ : w₀.natDegree < A.card) (hdeg₁ : w₁.natDegree < A.card)
    (hrow : w₀.eval eta ≠ 0 ∨ w₁.eval eta ≠ 0) :
    ∃ xi ∈ A, w₀.eval xi * w₁.eval eta - w₁.eval xi * w₀.eval eta ≠ 0 := by
  classical
  by_contra h
  have hvanish (xi : F) (hxi : xi ∈ A) :
      w₀.eval xi * w₁.eval eta - w₁.eval xi * w₀.eval eta = 0 := by
    by_contra hne
    exact h ⟨xi, hxi, hne⟩
  let p : F[X] := w₁.eval eta • w₀ + (-w₀.eval eta) • w₁
  have hpdeg : p.natDegree < A.card := by
    apply lt_of_le_of_lt (Polynomial.natDegree_add_le _ _)
    exact max_lt
      ((Polynomial.natDegree_smul_le _ _).trans_lt hdeg₀)
      ((Polynomial.natDegree_smul_le _ _).trans_lt hdeg₁)
  have hpzero : p = 0 := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' p A
    (fun xi hxi => by
      simpa [p, Polynomial.eval_add, Polynomial.eval_smul, smul_eq_mul,
        sub_eq_add_neg, mul_comm] using hvanish xi hxi) hpdeg
  obtain ⟨hz₁, hz₀⟩ := hind _ _ hpzero
  rcases hrow with hrow | hrow
  · exact hrow (neg_eq_zero.mp hz₀)
  · exact hrow hz₁

/-- At most D points collide with a fixed anchor for an independent pair of degree at most D. -/
theorem many_separated_at_anchor (w₀ w₁ : F[X]) (A : Finset F) (eta : F) (D : ℕ)
    (hind : IndependentPair w₀ w₁)
    (hdeg₀ : w₀.natDegree ≤ D) (hdeg₁ : w₁.natDegree ≤ D)
    (hrow : w₀.eval eta ≠ 0 ∨ w₁.eval eta ≠ 0) :
    A.card - D ≤ (A.filter fun xi =>
      w₀.eval xi * w₁.eval eta - w₁.eval xi * w₀.eval eta ≠ 0).card := by
  classical
  let p : F[X] := w₁.eval eta • w₀ + (-w₀.eval eta) • w₁
  have hpne : p ≠ 0 := by
    intro hpzero
    obtain ⟨hz₁, hz₀⟩ := hind _ _ hpzero
    rcases hrow with hrow | hrow
    · exact hrow (neg_eq_zero.mp hz₀)
    · exact hrow hz₁
  have hpdegree : p.natDegree ≤ D :=
    (Polynomial.natDegree_add_le _ _).trans (max_le
      ((Polynomial.natDegree_smul_le _ _).trans hdeg₀)
      ((Polynomial.natDegree_smul_le _ _).trans hdeg₁))
  have hbad : (A.filter fun x => p.eval x = 0).card ≤ D := by
    calc
      _ ≤ p.roots.toFinset.card := Finset.card_le_card (by
        intro x hx
        exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hpne).mpr (Finset.mem_filter.mp hx).2))
      _ ≤ p.roots.card := Multiset.toFinset_card_le _
      _ ≤ p.natDegree := Polynomial.card_roots' p
      _ ≤ D := hpdegree
  have hsum := Finset.card_filter_add_card_filter_not (s := A) (fun x => p.eval x = 0)
  have hgood : (A.filter fun x => ¬ p.eval x = 0) =
      A.filter (fun xi => w₀.eval xi * w₁.eval eta - w₁.eval xi * w₀.eval eta ≠ 0) := by
    ext x
    simp [p, Polynomial.eval_add, Polynomial.eval_smul, smul_eq_mul,
      sub_eq_add_neg, mul_comm]
  rw [hgood] at hsum
  omega

omit [DecidableEq F] in
/-- Dividing out an actual root is exact, including for the zero polynomial. -/
theorem remove_root_exact (p : F[X]) (xi : F) (hroot : p.eval xi = 0) :
    (X - C xi) * (p /ₘ (X - C xi)) = p :=
  Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hroot

omit [DecidableEq F] in
/-- The natural-degree bound decreases after division by a monic linear factor. -/
theorem remove_root_degree (p : F[X]) (xi : F) (D : ℕ) (hdegree : p.natDegree ≤ D) :
    (p /ₘ (X - C xi)).natDegree ≤ D - 1 := by
  rw [Polynomial.natDegree_divByMonic p (Polynomial.monic_X_sub_C xi),
    Polynomial.natDegree_X_sub_C]
  exact Nat.sub_le_sub_right hdegree 1

end PolynomialAnchors

section Deletion

variable {F : Type*} [Field F] [DecidableEq F]

open scoped BigOperators

/-- A scaled locator of distinct points has a simple root at every listed point. -/
theorem simple_locator_derivative (S : Finset F) (c x : F)
    (hc : c ≠ 0) (hx : x ∈ S) :
    (C c * ∏ y ∈ S, (X - C y)).derivative.eval x ≠ 0 := by
  have hfactor := Finset.mul_prod_erase S (fun y : F => (X - C y : F[X])) hx
  rw [← hfactor]
  have hp : (∏ y ∈ S.erase x, (x - y)) ≠ 0 := Finset.prod_ne_zero_iff.mpr
    (fun y hy => sub_ne_zero.mpr (Finset.mem_erase.mp hy).1.symm)
  simpa [Polynomial.derivative_mul, Polynomial.eval_prod] using mul_ne_zero hc hp

omit [DecidableEq F] in
/-- A simple determinant root prevents the difference-cofactor row from vanishing. -/
theorem cofactor_row_nonzero (f₀ f₁ g₀ g₁ w₀ w₁ L : F[X]) (x : F)
    (hrel₀ : f₀ = g₀ + L * w₀) (hrel₁ : f₁ = g₁ + L * w₁)
    (hroot : (f₀.eval x = 0 ∧ f₁.eval x = 0) ∨
      (g₀.eval x = 0 ∧ g₁.eval x = 0))
    (hsimple : (f₀ * g₁ - f₁ * g₀).derivative.eval x ≠ 0) :
    w₀.eval x ≠ 0 ∨ w₁.eval x ≠ 0 := by
  by_contra h
  simp only [not_or, not_not] at h
  have heq₀ : f₀.eval x = g₀.eval x := by simp [hrel₀, h.1]
  have heq₁ : f₁.eval x = g₁.eval x := by simp [hrel₁, h.2]
  have hz : f₀.eval x = 0 ∧ f₁.eval x = 0 ∧
      g₀.eval x = 0 ∧ g₁.eval x = 0 := by
    rcases hroot with ⟨hf₀, hf₁⟩ | ⟨hg₀, hg₁⟩
    · exact ⟨hf₀, hf₁, heq₀.symm.trans hf₀, heq₁.symm.trans hf₁⟩
    · exact ⟨heq₀.trans hg₀, heq₁.trans hg₁, hg₀, hg₁⟩
  apply hsimple
  simp [Polynomial.derivative_sub, Polynomial.derivative_mul,
    hz.1, hz.2.1, hz.2.2.1, hz.2.2.2]

omit [DecidableEq F] in
/-- Exact division preserves every other root. -/
theorem remove_root_preserves_eval (p : F[X]) (xi x : F)
    (hxi : p.eval xi = 0) (hx : p.eval x = 0) (hne : x ≠ xi) :
    (p /ₘ (X - C xi)).eval x = 0 := by
  have h := congrArg (Polynomial.eval x) (remove_root_exact p xi hxi)
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C, hx] at h
  exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hne)

omit [DecidableEq F] in
/-- Dividing a common root preserves the polynomial difference-cofactor identity. -/
theorem remove_root_preserves_relation (f g w L : F[X]) (xi : F)
    (hrel : f = g + L * w)
    (hf : f.eval xi = 0) (hg : g.eval xi = 0) (hw : w.eval xi = 0) :
    f /ₘ (X - C xi) = g /ₘ (X - C xi) + L * (w /ₘ (X - C xi)) := by
  apply mul_left_cancel₀ (Polynomial.X_sub_C_ne_zero xi)
  rw [mul_add, remove_root_exact f xi hf, remove_root_exact g xi hg,
    ← mul_assoc, mul_comm (X - C xi) L, mul_assoc, remove_root_exact w xi hw]
  exact hrel

omit [DecidableEq F] in
/-- Killing the cofactor row at a pair-region point kills both polynomial components. -/
theorem killed_combination_roots (f₀ f₁ g₀ g₁ w₀ w₁ L : F[X]) (x : F)
    (hrel₀ : f₀ = g₀ + L * w₀) (hrel₁ : f₁ = g₁ + L * w₁)
    (hroot : (f₀.eval x = 0 ∧ f₁.eval x = 0) ∨
      (g₀.eval x = 0 ∧ g₁.eval x = 0)) :
    (w₁.eval x • f₀ + (-w₀.eval x) • f₁).eval x = 0 ∧
    (w₁.eval x • g₀ + (-w₀.eval x) • g₁).eval x = 0 ∧
    (w₁.eval x • w₀ + (-w₀.eval x) • w₁).eval x = 0 := by
  have hw : (w₁.eval x • w₀ + (-w₀.eval x) • w₁).eval x = 0 := by simp; ring
  have heq : w₁.eval x • f₀ + (-w₀.eval x) • f₁ =
      (w₁.eval x • g₀ + (-w₀.eval x) • g₁) +
        L * (w₁.eval x • w₀ + (-w₀.eval x) • w₁) := by
    simp only [Polynomial.smul_eq_C_mul]
    rw [hrel₀, hrel₁]
    ring
  have hev : (w₁.eval x • f₀ + (-w₀.eval x) • f₁).eval x =
      (w₁.eval x • g₀ + (-w₀.eval x) • g₁).eval x := by
    rw [heq]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, hw, mul_zero, add_zero]
  rcases hroot with ⟨hf₀, hf₁⟩ | ⟨hg₀, hg₁⟩
  · have hf : (w₁.eval x • f₀ + (-w₀.eval x) • f₁).eval x = 0 := by simp [hf₀, hf₁]
    exact ⟨hf, hev.symm.trans hf, hw⟩
  · have hg : (w₁.eval x • g₀ + (-w₀.eval x) • g₁).eval x = 0 := by simp [hg₀, hg₁]
    exact ⟨hev.trans hg, hg, hw⟩

/-- Kill the cofactor row at x, then divide out that point from one component. -/
noncomputable def deleteAt (w₀ w₁ p₀ p₁ : F[X]) (x : F) : F[X] :=
  (w₁.eval x • p₀ + (-w₀.eval x) • p₁) /ₘ (X - C x)

omit [DecidableEq F] in
/-- Every component loses one degree bound in the deletion operation. -/
theorem delete_at_degree (w₀ w₁ p₀ p₁ : F[X]) (x : F) (D : ℕ)
    (hp₀ : p₀.natDegree ≤ D) (hp₁ : p₁.natDegree ≤ D) :
    (deleteAt w₀ w₁ p₀ p₁ x).natDegree ≤ D - 1 := by
  apply remove_root_degree
  exact (Polynomial.natDegree_add_le _ _).trans (max_le
    ((Polynomial.natDegree_smul_le _ _).trans hp₀)
    ((Polynomial.natDegree_smul_le _ _).trans hp₁))

omit [DecidableEq F] in
/-- A deleted column preserves its difference-cofactor relation and all other component roots. -/
theorem delete_at_preserves (f₀ f₁ g₀ g₁ w₀ w₁ L : F[X]) (x : F)
    (hrel₀ : f₀ = g₀ + L * w₀) (hrel₁ : f₁ = g₁ + L * w₁)
    (hroot : (f₀.eval x = 0 ∧ f₁.eval x = 0) ∨
      (g₀.eval x = 0 ∧ g₁.eval x = 0)) :
    deleteAt w₀ w₁ f₀ f₁ x =
      deleteAt w₀ w₁ g₀ g₁ x + L * deleteAt w₀ w₁ w₀ w₁ x ∧
    (∀ y : F, y ≠ x → f₀.eval y = 0 → f₁.eval y = 0 →
      (deleteAt w₀ w₁ f₀ f₁ x).eval y = 0) ∧
    (∀ y : F, y ≠ x → g₀.eval y = 0 → g₁.eval y = 0 →
      (deleteAt w₀ w₁ g₀ g₁ x).eval y = 0) := by
  obtain ⟨hf, hg, hw⟩ := killed_combination_roots f₀ f₁ g₀ g₁ w₀ w₁ L x hrel₀ hrel₁ hroot
  have hcomb : w₁.eval x • f₀ + (-w₀.eval x) • f₁ =
      (w₁.eval x • g₀ + (-w₀.eval x) • g₁) +
        L * (w₁.eval x • w₀ + (-w₀.eval x) • w₁) := by
    simp only [Polynomial.smul_eq_C_mul]
    rw [hrel₀, hrel₁]
    ring
  refine ⟨remove_root_preserves_relation _ _ _ L x hcomb hf hg hw, ?_, ?_⟩
  · intro y hy hy₀ hy₁
    exact remove_root_preserves_eval _ x y hf (by simp [hy₀, hy₁]) hy
  · intro y hy hy₀ hy₁
    exact remove_root_preserves_eval _ x y hg (by simp [hy₀, hy₁]) hy

omit [DecidableEq F] in
/-- Two selected deletions have the exact determinant formula and retain a nonzero determinant. -/
theorem two_anchor_deleted_determinant (f₀ f₁ g₀ g₁ w₀ w₁ L : F[X]) (xi eta : F)
    (hrel₀ : f₀ = g₀ + L * w₀) (hrel₁ : f₁ = g₁ + L * w₁)
    (hxi : f₀.eval xi = 0 ∧ f₁.eval xi = 0)
    (heta : g₀.eval eta = 0 ∧ g₁.eval eta = 0)
    (hsep : w₀.eval xi * w₁.eval eta - w₁.eval xi * w₀.eval eta ≠ 0)
    (hdet : f₀ * g₁ - f₁ * g₀ ≠ 0) :
    let d := deleteAt w₀ w₁ f₀ f₁ xi * deleteAt w₀ w₁ g₀ g₁ eta -
      deleteAt w₀ w₁ f₀ f₁ eta * deleteAt w₀ w₁ g₀ g₁ xi
    (X - C xi) * (X - C eta) * d =
      C (w₀.eval xi * w₁.eval eta - w₁.eval xi * w₀.eval eta) * (f₀ * g₁ - f₁ * g₀) ∧
    d ≠ 0 := by
  obtain ⟨hfξ, hgξ, _⟩ := killed_combination_roots f₀ f₁ g₀ g₁ w₀ w₁ L xi
    hrel₀ hrel₁ (Or.inl hxi)
  obtain ⟨hfη, hgη, _⟩ := killed_combination_roots f₀ f₁ g₀ g₁ w₀ w₁ L eta
    hrel₀ hrel₁ (Or.inr heta)
  have h := divided_determinant f₀ f₁ g₀ g₁
    (C (w₁.eval xi)) (C (-w₀.eval xi)) (C (w₁.eval eta)) (C (-w₀.eval eta))
    (X - C xi) (X - C eta)
    (deleteAt w₀ w₁ f₀ f₁ xi) (deleteAt w₀ w₁ f₀ f₁ eta)
    (deleteAt w₀ w₁ g₀ g₁ xi) (deleteAt w₀ w₁ g₀ g₁ eta)
    (by simpa [deleteAt, Polynomial.smul_eq_C_mul] using (remove_root_exact _ xi hfξ).symm)
    (by simpa [deleteAt, Polynomial.smul_eq_C_mul] using (remove_root_exact _ xi hgξ).symm)
    (by simpa [deleteAt, Polynomial.smul_eq_C_mul] using (remove_root_exact _ eta hfη).symm)
    (by simpa [deleteAt, Polynomial.smul_eq_C_mul] using (remove_root_exact _ eta hgη).symm)
  have hcoeff : C (w₁.eval xi) * C (-w₀.eval eta) - C (-w₀.eval xi) * C (w₁.eval eta) =
      C (w₀.eval xi * w₁.eval eta - w₁.eval xi * w₀.eval eta) := by
    simp only [map_sub, map_mul, map_neg]
    ring
  rw [hcoeff] at h
  refine ⟨h, ?_⟩
  intro hz
  rw [hz, mul_zero] at h
  exact mul_ne_zero (Polynomial.C_ne_zero.mpr hsep) hdet h.symm

/-- The determinant after two distinct point deletions is the scaled remaining locator. -/
theorem deleted_locator_formula (S : Finset F) (xi eta c s : F) (d : F[X])
    (hxi : xi ∈ S) (heta : eta ∈ S) (hne : eta ≠ xi)
    (hdet : (X - C xi) * (X - C eta) * d =
      C s * (C c * ∏ y ∈ S, (X - C y))) :
    d = C (s * c) * ∏ y ∈ (S.erase xi).erase eta, (X - C y) := by
  have he : eta ∈ S.erase xi := Finset.mem_erase.mpr ⟨hne, heta⟩
  have hfactor : (∏ y ∈ S, (X - C y : F[X])) =
      (X - C xi) * (X - C eta) * ∏ y ∈ (S.erase xi).erase eta, (X - C y) := by
    calc
      _ = (X - C xi) * ∏ y ∈ S.erase xi, (X - C y) :=
        (Finset.mul_prod_erase S (fun y : F => (X - C y : F[X])) hxi).symm
      _ = _ := by
        rw [← Finset.mul_prod_erase (S.erase xi) (fun y : F => (X - C y : F[X])) he]
        ring
  apply mul_left_cancel₀ (mul_ne_zero (Polynomial.X_sub_C_ne_zero xi) (Polynomial.X_sub_C_ne_zero eta))
  calc
    _ = C s * (C c * ∏ y ∈ S, (X - C y)) := hdet
    _ = _ := by rw [hfactor]; simp only [map_mul]; ring

end Deletion

/-- The two production deletion steps have the same root-count margin. -/
theorem production_anchor_margins :
    357913941 - (536870912 - 357913942) = 178956971 ∧
    (357913941 - 1) - ((536870912 - 1) - 357913942) = 178956971 := by decide

end AstraMcaPolynomialBasis

#print axioms AstraMcaPolynomialBasis.initial_determinant
#print axioms AstraMcaPolynomialBasis.change_basis_determinant
#print axioms AstraMcaPolynomialBasis.divided_determinant
#print axioms AstraMcaPolynomialBasis.cofactor_pair_independent
#print axioms AstraMcaPolynomialBasis.exists_separated_at_anchor
#print axioms AstraMcaPolynomialBasis.many_separated_at_anchor
#print axioms AstraMcaPolynomialBasis.remove_root_exact
#print axioms AstraMcaPolynomialBasis.remove_root_degree
#print axioms AstraMcaPolynomialBasis.simple_locator_derivative
#print axioms AstraMcaPolynomialBasis.cofactor_row_nonzero
#print axioms AstraMcaPolynomialBasis.remove_root_preserves_eval
#print axioms AstraMcaPolynomialBasis.remove_root_preserves_relation
#print axioms AstraMcaPolynomialBasis.killed_combination_roots
#print axioms AstraMcaPolynomialBasis.delete_at_degree
#print axioms AstraMcaPolynomialBasis.delete_at_preserves
#print axioms AstraMcaPolynomialBasis.two_anchor_deleted_determinant
#print axioms AstraMcaPolynomialBasis.deleted_locator_formula
#print axioms AstraMcaPolynomialBasis.production_anchor_margins
