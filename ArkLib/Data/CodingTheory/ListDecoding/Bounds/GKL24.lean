/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Team
-/

import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Matrix.Basis
import ArkLib.Data.Polynomial.Multivariate.Interpolation
import ArkLib.Data.Polynomial.Multivariate.HasseDerivative
import ArkLib.Data.CodingTheory.SubspaceDesign.Basic

/-!
# List-Decoding Capacity Bounds from GKL24
This file formalizes the polynomial interpolation bounds for list-decoding capacity
as presented in Guruswami-Kopparty-Lovelock 2024 (GKL24).
-/

namespace CodingTheory.Bounds.GKL24

open Polynomial MvPolynomial Matrix
open scoped BigOperators

variable {F : Type} [Field F]

/-- Generates a list of all pairs (i, j) with i + j < m -/
def pairs_lt : ℕ → List (ℕ × ℕ)
| 0 => []
| (m + 1) => pairs_lt m ++ (List.range (m + 1)).map (fun i => (i, m - i))

lemma length_pairs_lt (m : ℕ) : (pairs_lt m).length * 2 = m * (m + 1) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [pairs_lt, List.length_append, List.length_map, List.length_range]
    linarith

/-- Maps a pair to a Fin 2 multi-index -/
def d_of_pair (p : ℕ × ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 p.1 + Finsupp.single 1 p.2

/-- Generates conditions for a given point and multiplicity -/
def cond_list (p : F × F) (m : ℕ) : List ((F × F) × (Fin 2 →₀ ℕ)) :=
  (pairs_lt m).map (fun pair => (p, d_of_pair pair))

/-- Generates all conditions over all points -/
def all_conds (points : List (F × F)) (multiplicities : (F × F) → ℕ) : List ((F × F) × (Fin 2 →₀ ℕ)) :=
  points.bind (fun p => cond_list p (multiplicities p))

lemma length_all_conds (points : List (F × F)) (multiplicities : (F × F) → ℕ) :
  (all_conds points multiplicities).length = (points.map (fun p => (multiplicities p + 1) * multiplicities p / 2)).sum := by
  induction points with
  | nil => rfl
  | cons p ps ih =>
    rw [all_conds, List.bind_eq_flatMap, List.flatMap_cons, List.length_append, ih, cond_list]
    rw [List.map_cons, List.sum_cons]
    have h : (pairs_lt (multiplicities p)).length = (multiplicities p + 1) * multiplicities p / 2 := by
      have h2 := length_pairs_lt (multiplicities p)
      omega
    rw [List.length_map, h]

def MonomialIndex (deg_X deg_Y : ℕ) := Fin (deg_X + 1) × Fin (deg_Y + 1)

/-- The matrix representing the evaluation of Hasse derivatives. -/
def GKL24Matrix
    (points : List (F × F))
    (multiplicities : (F × F) → ℕ)
    (deg_X deg_Y : ℕ)
    (M : ℕ)
    (hM : M = (all_conds points multiplicities).length) :
    Matrix (Fin M) (MonomialIndex deg_X deg_Y) F :=
  fun k mono =>
    let p_d := (all_conds points multiplicities).get (k.cast hM.symm)
    eval ![p_d.1.1, p_d.1.2] (hasseDeriv p_d.2 (monomial ![mono.1.val, mono.2.val] 1))

lemma matrix_exists_mulVec_eq_zero_of_lt {m : ℕ} {n : Type*} [Fintype n] (A : Matrix (Fin m) n F) (h : m < Fintype.card n) :
  ∃ v : n → F, v ≠ 0 ∧ A.mulVec v = 0 := by
  by_contra h_not
  push_neg at h_not
  have h_inj : Function.Injective A.toLin' := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    by_contra h_nz
    exact h_not v h_nz hv
  have : Fintype.card n ≤ m := by simpa using LinearMap.finrank_le_finrank_of_injective h_inj
  omega

lemma Q_of_v_ne_zero {deg_X deg_Y : ℕ} (v : MonomialIndex deg_X deg_Y → F) (hv : v ≠ 0) :
  (∑ mono, v mono • monomial ![mono.1.val, mono.2.val] 1) ≠ 0 := by
  intro h_sum
  apply hv
  ext mono
  simp only [Pi.zero_apply]
  have h_coeff := congr_arg (MvPolynomial.coeff ![mono.1.val, mono.2.val]) h_sum
  simp only [map_sum, MvPolynomial.coeff_zero, MvPolynomial.coeff_smul] at h_coeff
  rw [Finset.sum_eq_single mono] at h_coeff
  · simp only [MvPolynomial.coeff_monomial, if_pos rfl, smul_eq_mul, mul_one] at h_coeff
    exact h_coeff
  · intro b _ hbm
    simp only [MvPolynomial.coeff_monomial]
    have h_neq : ![b.1.val, b.2.val] ≠ ![mono.1.val, mono.2.val] := by
      intro hc
      apply hbm
      ext i
      fin_cases i
      · have : (![b.1.val, b.2.val] 0 : ℕ) = ![mono.1.val, mono.2.val] 0 := by rw [hc]
        simp at this
        exact Fin.ext this
      · have : (![b.1.val, b.2.val] 1 : ℕ) = ![mono.1.val, mono.2.val] 1 := by rw [hc]
        simp at this
        exact Fin.ext this
    rw [if_neg h_neq, smul_zero]
  · intro h
    simp at h

/-- The GKL24 interpolation condition bounds the degrees required to ensure a non-zero
interpolating polynomial Q(X,Y) exists for given evaluation points and multiplicities. -/
theorem gkl24_interpolation_existence
    (points : Finset (F × F))
    (multiplicities : (F × F) → ℕ)
    (deg_X deg_Y : ℕ)
    (h_dim : (points.sum (fun p => (multiplicities p + 1) * multiplicities p / 2)) < (deg_X + 1) * (deg_Y + 1)) :
    ∃ Q : MvPolynomial (Fin 2) F, Q ≠ 0 ∧
      (MvPolynomial.degreeOf 0 Q ≤ deg_X) ∧
      (MvPolynomial.degreeOf 1 Q ≤ deg_Y) ∧
      ∀ p ∈ points, ArkLib.MvPolynomial.mult_ge ![p.1, p.2] (multiplicities p) Q := by
  sorry

end CodingTheory.Bounds.GKL24
