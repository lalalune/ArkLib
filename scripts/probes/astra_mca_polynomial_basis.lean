/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.Tactic.Ring

/-!
# Polynomial algebra for the four-deletion MCA construction

The initial determinant identity, constant changes of basis, cofactor
independence, fixed-anchor selection and root division are formalized here.
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
#print axioms AstraMcaPolynomialBasis.production_anchor_margins
