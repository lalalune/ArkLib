/-!
# Degree Bounds on Sums of Polynomials

This module provides a lemma bounding the natural degree of a sum of polynomials
when each term's natural degree is strictly bounded by a positive integer $n$.

In cryptographic and algebraic settings (such as polynomial identity testing or sharing schemes),
we frequently combine polynomials by summing them (e.g. random linear combinations or Lagrange
interpolation sums) and need to verify that the degree of the resulting polynomial remains strictly
bounded.
-/

import Mathlib.Algebra.Polynomial.BigOperators

namespace Polynomial

/--
The natural degree of a sum of polynomials is strictly less than $n$ (where $n > 0$)
if the natural degree of each individual summand is strictly less than $n$.
-/
theorem natDegree_sum_lt_of_forall_lt.{u_1, w}
  {ι : Type w} (s : Finset ι) {S : Type u_1} [Semiring S]
  {n : ℕ} [inst : NeZero n] (f : ι → Polynomial S) (h : ∀ i ∈ s, (f i).natDegree < n) :
  (∑ i ∈ s, f i).natDegree < n := by
  rw [←Nat.le_pred_iff_lt (by aesop (add safe forward [inst.out]) (add safe (by omega)))]
  exact natDegree_sum_le_of_forall_le _ _ <| fun i hi ↦
    Nat.le_pred_of_lt (h _ hi)

end Polynomial
