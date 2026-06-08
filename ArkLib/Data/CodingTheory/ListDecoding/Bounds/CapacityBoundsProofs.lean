import ArkLib.Data.CodingTheory.ListDecoding.Bounds.GKL24
import ArkLib.Data.CodingTheory.ListDecoding.Bounds.BCHKS25
import ArkLib.Data.CodingTheory.ListDecoding.GuruswamiSudan.Basic
import Mathlib.Data.MvPolynomial.Basic
import Mathlib.Data.MvPolynomial.Variables
import Mathlib.Data.Polynomial.RingDivision

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
  (MvPolynomial.aeval (fun i => if i = 0 then (X : Polynomial F) else f) Q).eval x =
  MvPolynomial.eval (fun i => if i = 0 then x else f.eval x) Q := by
  apply MvPolynomial.induction_on Q
  · intro c
    simp only [map_ofNat, map_C, eval_C]
  · intro p q hp hq
    simp only [map_add, eval_add, hp, hq]
  · intro p i hp
    simp only [map_mul, eval_mul, hp]
    congr 1
    revert i
    exact fun i => Fin.cases (by simp) (fun j => Fin.cases (by simp) (fun k => Fin.elim0 k) j) i

/-- Bounding the degree of the substituted polynomial P(X) = Q(X, f(X)). -/
lemma natDegree_aeval_le (Q : MvPolynomial (Fin 2) F) (deg_X deg_Y : ℕ)
  (hX : MvPolynomial.degreeOf 0 Q ≤ deg_X)
  (hY : MvPolynomial.degreeOf 1 Q ≤ deg_Y)
  (f : Polynomial F) :
  (MvPolynomial.aeval (fun i => if i = 0 then (X : Polynomial F) else f) Q).natDegree ≤ deg_X + deg_Y * f.natDegree := by
  sorry

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
