import Mathlib.Data.MvPolynomial.Basic
import Mathlib.Data.MvPolynomial.Variables
import Mathlib.Data.Polynomial.RingDivision

open Polynomial MvPolynomial
open scoped BigOperators

variable {F : Type} [Field F]

lemma natDegree_aeval_le (Q : MvPolynomial (Fin 2) F) (deg_X deg_Y : ℕ)
  (hX : MvPolynomial.degreeOf 0 Q ≤ deg_X)
  (hY : MvPolynomial.degreeOf 1 Q ≤ deg_Y)
  (f : Polynomial F) :
  (MvPolynomial.aeval (fun i => if i = 0 then (X : Polynomial F) else f) Q).natDegree ≤ deg_X + deg_Y * f.natDegree := by
  sorry
