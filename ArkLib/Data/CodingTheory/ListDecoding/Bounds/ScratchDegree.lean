import Mathlib.Data.MvPolynomial.Basic
import Mathlib.Data.MvPolynomial.Variables
import Mathlib.Algebra.BigOperators.Basic

open Polynomial MvPolynomial
open scoped BigOperators

variable {F : Type} [CommRing F]

lemma totalDegree_le_of_degrees_le (Q : MvPolynomial (Fin 2) F) (deg_X deg_Y : ℕ)
    (hX : MvPolynomial.degrees Q 0 ≤ deg_X)
    (hY : MvPolynomial.degrees Q 1 ≤ deg_Y) :
    MvPolynomial.totalDegree Q ≤ deg_X + deg_Y := by
  sorry
