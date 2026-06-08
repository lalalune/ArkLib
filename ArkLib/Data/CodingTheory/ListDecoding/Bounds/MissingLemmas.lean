/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Team
-/
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-!
# Supporting degree lemma for list-decoding capacity bounds

`natDegree_aeval_le` bounds the degree of the univariate substitution `P(X) = Q(X, f(X))`
in terms of the bidegree of `Q` and `deg f`. This is the degree-bookkeeping step in the
Guruswami–Sudan list-decoding argument.
-/

open Polynomial MvPolynomial
open scoped BigOperators

variable {F : Type} [Field F]

/-- Bounding the degree of the substituted polynomial `P(X) = Q(X, f(X))`. -/
lemma natDegree_aeval_le (Q : MvPolynomial (Fin 2) F) (deg_X deg_Y : ℕ)
    (hX : MvPolynomial.degreeOf 0 Q ≤ deg_X)
    (hY : MvPolynomial.degreeOf 1 Q ≤ deg_Y)
    (f : Polynomial F) :
    (MvPolynomial.aeval (fun i => if i = 0 then (X : Polynomial F) else f) Q).natDegree
      ≤ deg_X + deg_Y * f.natDegree := by
  let g : Fin 2 → Polynomial F := fun i => if i = 0 then X else f
  have heval : MvPolynomial.aeval g Q
      = ∑ m ∈ Q.support, MvPolynomial.aeval g (MvPolynomial.monomial m (MvPolynomial.coeff m Q)) := by
    rw [← map_sum, ← MvPolynomial.as_sum]
  rw [heval]
  refine le_trans (Polynomial.natDegree_sum_le _ _) ?_
  refine Finset.sup_le ?_
  intro m hm
  simp only [Function.comp_apply]
  have h_eval_m : MvPolynomial.aeval g (MvPolynomial.monomial m (MvPolynomial.coeff m Q)) =
      Polynomial.C (MvPolynomial.coeff m Q) * g 0 ^ m 0 * g 1 ^ m 1 := by
    rw [MvPolynomial.aeval_monomial, Polynomial.algebraMap_eq, Finsupp.prod_fintype,
      Fin.prod_univ_two, ← mul_assoc]
    intro i; rw [pow_zero]
  rw [h_eval_m]
  have hg0 : g 0 = Polynomial.X := rfl
  have hg1 : g 1 = f := rfl
  rw [hg0, hg1]
  refine le_trans Polynomial.natDegree_mul_le ?_
  refine le_trans (add_le_add_right (Polynomial.natDegree_C_mul_le _ _) _) ?_
  refine le_trans Polynomial.natDegree_mul_le ?_
  have h0 : (Polynomial.X ^ m 0 : Polynomial F).natDegree ≤ m 0 := by
    have h_pow := Polynomial.natDegree_pow_le (Polynomial.X : Polynomial F) (m 0)
    have h_X : (Polynomial.X : Polynomial F).natDegree = 1 := Polynomial.natDegree_X
    rw [h_X, mul_one] at h_pow
    exact h_pow
  have h1 : (f ^ m 1).natDegree ≤ m 1 * f.natDegree := Polynomial.natDegree_pow_le _ _
  have hX_m : m 0 ≤ deg_X := le_trans (MvPolynomial.le_degreeOf hm) hX
  have hY_m : m 1 ≤ deg_Y := le_trans (MvPolynomial.le_degreeOf hm) hY
  calc
    (Polynomial.X ^ m 0 : Polynomial F).natDegree + (f ^ m 1).natDegree
      ≤ m 0 + m 1 * f.natDegree := add_le_add h0 h1
    _ ≤ deg_X + deg_Y * f.natDegree := add_le_add hX_m (Nat.mul_le_mul_right _ hY_m)
