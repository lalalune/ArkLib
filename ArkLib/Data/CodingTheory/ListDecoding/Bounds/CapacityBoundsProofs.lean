import ArkLib.Data.CodingTheory.ListDecoding.Bounds.GKL24
import ArkLib.Data.CodingTheory.ListDecoding.Bounds.BCHKS25
import ArkLib.Data.CodingTheory.ListDecoding.Bounds.SubstitutionMultiplicity
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.Algebra.Polynomial.RingDivision

/-!
# Final Capacity Bound Proofs
This file unifies the GKL24 interpolation bounds, the BCHKS25 multiplicity bounds,
and the Phase 1 Guruswami-Sudan roots theorems into the final list decoding
capacity bound theorems for cryptographic application.
-/

namespace CodingTheory.Bounds.Capacity

open Polynomial MvPolynomial
open scoped BigOperators

variable {F : Type} [Field F]

/-- Evaluates the substitution P(X) = Q(X, f(X)) at a point x. -/
lemma aeval_eval_eq (Q : MvPolynomial (Fin 2) F) (f : Polynomial F) (x : F) :
    (MvPolynomial.aeval (fun i => if i = 0 then (Polynomial.X : Polynomial F) else f) Q).eval x =
    MvPolynomial.eval (fun i => if i = 0 then x else f.eval x) Q := by
  induction Q using MvPolynomial.induction_on with
  | C c => simp [MvPolynomial.aeval_C, Polynomial.algebraMap_eq]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp]
    congr 1
    fin_cases i <;> simp only [MvPolynomial.aeval_X, MvPolynomial.eval_X, Polynomial.eval_X]

/-- Bounding the degree of the substituted polynomial P(X) = Q(X, f(X)). -/
lemma natDegree_aeval_le (Q : MvPolynomial (Fin 2) F) (deg_X deg_Y : ℕ)
    (hX : MvPolynomial.degreeOf 0 Q ≤ deg_X)
    (hY : MvPolynomial.degreeOf 1 Q ≤ deg_Y)
    (f : Polynomial F) :
    (MvPolynomial.aeval (fun i => if i = 0 then (Polynomial.X : Polynomial F) else f) Q).natDegree
      ≤ deg_X + deg_Y * f.natDegree := by
  let g : Fin 2 → Polynomial F := fun i => if i = 0 then Polynomial.X else f
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

/-- The Hasse derivative multiplicity condition implies the univariate root multiplicity bound
upon substitution. -/
lemma rootMultiplicity_aeval_ge (Q : MvPolynomial (Fin 2) F) (f : Polynomial F) (x : F) (m : ℕ)
  (h_mult : ArkLib.MvPolynomial.mult_ge ![x, f.eval x] m Q) :
  m ≤ rootMultiplicity x (MvPolynomial.aeval (fun i => if i = 0 then (X : Polynomial F) else f) Q) := by
  sorry

/-- The final list-decoding capacity bound combining GKL24 interpolation and BCHKS25 vanishing.
Any codeword with agreement strictly greater than the list decoding radius will correspond
to a Y-root of the interpolating polynomial Q(X,Y). -/
theorem capacity_bound_implies_y_root
    (points : Finset F)
    (f : Polynomial F)
    (received : F → F)
    (multiplicities : (F × F) → ℕ)
    (deg_X deg_Y : ℕ)
    (h_dim : (points.sum (fun x => (multiplicities (x, received x) + 1) * multiplicities (x, received x) / 2)) < (deg_X + 1) * (deg_Y + 1))
    (h_agree : (points.filter (fun x => f.eval x = received x)).sum (fun x => multiplicities (x, received x)) > deg_X + deg_Y * f.natDegree) :
    ∃ Q : MvPolynomial (Fin 2) F, Q ≠ 0 ∧
      (∀ x, MvPolynomial.eval (fun i => if i = 0 then x else f.eval x) Q = 0) := by
  let points' := points.image (fun x => (x, received x))
  have h_dim' : (points'.sum (fun p => (multiplicities p + 1) * multiplicities p / 2)) < (deg_X + 1) * (deg_Y + 1) := by
    rw [Finset.sum_image]
    · exact h_dim
    · intro x _ y _ h
      exact Prod.mk.inj h |>.1
  
  obtain ⟨Q, hQ_neq, hQ_degX, hQ_degY, hQ_mult⟩ := GKL24.gkl24_interpolation_existence points' multiplicities deg_X deg_Y h_dim'
  use Q
  refine ⟨hQ_neq, ?_⟩
  intro x
  
  let P := MvPolynomial.aeval (fun i => if i = 0 then (X : Polynomial F) else f) Q
  
  have h_vanish := BCHKS25.bchks25_vanishing_of_multiplicity_sum_gt_degree P (points.filter (fun z => f.eval z = received z)) (fun z => multiplicities (z, received z)) ?_ ?_
  · have h_eval_zero : P.eval x = 0 := by rw [h_vanish, Polynomial.eval_zero]
    rw [← aeval_eval_eq Q f x] at h_eval_zero
    exact h_eval_zero

  · intro z hz
    have hz_points : z ∈ points := Finset.mem_of_mem_filter z hz
    have hz_eq : f.eval z = received z := (Finset.mem_filter.mp hz).2
    have hz_points' : (z, f.eval z) ∈ points' := by
      rw [hz_eq]
      apply Finset.mem_image_of_mem
      exact hz_points
    have h_mult_Q := hQ_mult (z, f.eval z) hz_points'
    exact rootMultiplicity_aeval_ge Q f z (multiplicities (z, received z)) (by
      have heq2 : multiplicities (z, received z) = multiplicities (z, f.eval z) := by rw [hz_eq]
      rw [heq2]
      exact h_mult_Q
    )
    
  · have h_deg_P := natDegree_aeval_le Q deg_X deg_Y hQ_degX hQ_degY f
    exact lt_of_le_of_lt h_deg_P h_agree

end CodingTheory.Bounds.Capacity
