import Mathlib

/-! Interpolation-uniqueness foundations for the BCIKS20 coefficient-extraction chains. -/
(BCIKS20 §5 / BoundaryCardLatticeData). A function determined on > k points by a degree-≤k
polynomial has a UNIQUE such polynomial; two low-degree polys agreeing on enough points are
equal. These are the Vandermonde facts the coefficient-extraction residuals repeatedly invoke. -/

open Polynomial

namespace ProximityGap.InterpUniqueness

variable {F : Type*} [Field F]

/-- **Interpolation uniqueness (degree form).** Two polynomials of degree `< d` that agree at
`d` distinct points are equal. (Their difference has `< d` roots unless zero, but agrees at
`d` points.) -/
theorem eq_of_degree_lt_of_eval_eq {p q : F[X]} {Z : Finset F} {d : ℕ}
    (hp : p.degree < d) (hq : q.degree < d) (hZ : d ≤ Z.card)
    (hagree : ∀ z ∈ Z, p.eval z = q.eval z) :
    p = q := by
  classical
  -- `p - q` has degree `< d` and vanishes on `Z` with `|Z| ≥ d` distinct points.
  by_contra hne
  have hsub : p - q ≠ 0 := sub_ne_zero.mpr hne
  have hdeg : (p - q).degree < d :=
    lt_of_le_of_lt (Polynomial.degree_sub_le p q) (max_lt hp hq)
  -- every z ∈ Z is a root of p - q
  have hroots : Z ⊆ (p - q).roots.toFinset := by
    intro z hz
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hsub]
    simp [Polynomial.IsRoot, hagree z hz]
  -- so the root multiset has ≥ |Z| ≥ d elements, but a deg-<d nonzero poly has < d roots
  have hcard : (d : ℕ) ≤ (p - q).roots.toFinset.card :=
    le_trans hZ (Finset.card_le_card hroots)
  have hroots_le : (p - q).roots.toFinset.card ≤ (p - q).natDegree :=
    le_trans (Multiset.toFinset_card_le _) (Polynomial.card_roots' _)
  have hnatdeg : (p - q).natDegree < d := by
    by_cases h0 : p - q = 0
    · exact absurd h0 hsub
    · exact (Polynomial.natDegree_lt_iff_degree_lt h0).mpr hdeg
  omega

/-- **Coefficient agreement of the unique interpolant.** If `p, q` (degree `< d`) agree on a
`d`-point set, all their coefficients agree. -/
theorem coeff_eq_of_degree_lt_of_eval_eq {p q : F[X]} {Z : Finset F} {d : ℕ}
    (hp : p.degree < d) (hq : q.degree < d) (hZ : d ≤ Z.card)
    (hagree : ∀ z ∈ Z, p.eval z = q.eval z) (j : ℕ) :
    p.coeff j = q.coeff j := by
  rw [eq_of_degree_lt_of_eval_eq hp hq hZ hagree]

/-- **Bivariate coefficient extraction (assembly direction).** For a bivariate
`Q : F[X][X]` (`Q = ∑_j B_j · X^j`, `B_j := Q.coeff j ∈ F[X]`), specialising the *outer*
variable to `z` (mapping coefficients through `eval z`) gives a univariate `P_z` whose
`j`-th coefficient is `B_j(z)`.  This is the clean half of the BoundaryCardLatticeData /
§5 coefficient extraction: once a low-bidegree `Q` explaining the agreement exists, its
coefficient polynomials are literally `Q.coeff j`. -/
theorem coeff_specialize (Q : F[X][X]) (z : F) (j : ℕ) :
    ((Q.map (Polynomial.evalRingHom z)).coeff j) = (Q.coeff j).eval z := by
  rw [Polynomial.coeff_map]
  rfl

#print axioms ProximityGap.InterpUniqueness.eq_of_degree_lt_of_eval_eq
#print axioms ProximityGap.InterpUniqueness.coeff_eq_of_degree_lt_of_eval_eq
#print axioms ProximityGap.InterpUniqueness.coeff_specialize

end ProximityGap.InterpUniqueness
