import Mathlib.Tactic
import Mathlib.Data.Polynomial.Basic
import Mathlib.Data.Polynomial.Eval
import Mathlib.Data.Polynomial.Roots
import ArkLib.Data.Polynomial.Multivariate.Interpolation
import ArkLib.Data.Polynomial.Multivariate.HasseDerivative

open Polynomial
open Finset

variable {F : Type*} [Field F]

/-- Represents an evaluation point (x, y) -/
abbrev Point (F : Type*) := F × F

/-- Q(X, Y) is represented as a polynomial in Y with coefficients in F[X] -/
abbrev BivariatePoly (F : Type*) [CommRing F] := Polynomial (Polynomial F)

/-- A bivariate polynomial interpolates a point with multiplicity r if
    for any univariate polynomial f passing through the point, Q(X, f(X)) has a root
    at x of multiplicity at least r. -/
def InterpolatesPoint (Q : BivariatePoly F) (p : Point F) (r : ℕ) : Prop :=
  ∀ f : Polynomial F, f.eval p.1 = p.2 → (X - C p.1)^r ∣ Q.eval f

/-- Q interpolates a set of points with multiplicity r. -/
def InterpolatesPoints (Q : BivariatePoly F) (pts : Finset (Point F)) (r : ℕ) : Prop :=
  ∀ p ∈ pts, InterpolatesPoint Q p r

/-- A codeword represented by a polynomial f has sufficient agreement
    with the evaluation points if the degree of the divisor polynomial D
    (which captures the agreement points with multiplicity r) exceeds
    the degree of Q(X, f(X)). -/
def SufficientAgreement (Q : BivariatePoly F) (f : Polynomial F) (D : Polynomial F) : Prop :=
  (Q.eval f).natDegree < D.natDegree

/--
The core Guruswami-Sudan list decoding property.
If a bivariate polynomial Q(X, Y) interpolates the evaluation points such that
for a codeword f, the agreement points (with multiplicity r) induce a divisor D
of Q(X, f(X)), and we have sufficient agreement (deg Q(X, f(X)) < deg D),
then Q(X, f(X)) = 0, meaning f is a Y-root of Q.
-/
theorem guruswami_sudan_y_root
    (Q : BivariatePoly F)
    (f : Polynomial F)
    (D : Polynomial F)
    (h_dvd : D ∣ Q.eval f)
    (h_agree : SufficientAgreement Q f D) :
    (X - C f) ∣ Q := by
  have h_eval_zero : Q.eval f = 0 := by
    by_contra h_nonzero
    rcases h_dvd with ⟨K, hK⟩
    have hK_nz : K ≠ 0 := by
      rintro rfl
      simp only [mul_zero, zero_mul] at hK
      exact h_nonzero hK
    have hD_nz : D ≠ 0 := by
      rintro rfl
      simp only [mul_zero, zero_mul] at hK
      exact h_nonzero hK
    have h_deg_le : D.natDegree ≤ (Q.eval f).natDegree := by
      rw [hK]
      try rw [mul_comm K D]
      rw [natDegree_mul hD_nz hK_nz]
      omega
    have h_lt : (Q.eval f).natDegree < D.natDegree := h_agree
    linarith
  rw [dvd_iff_isRoot]
  exact h_eval_zero
