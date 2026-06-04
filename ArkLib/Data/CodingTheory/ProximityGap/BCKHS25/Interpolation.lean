/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import CompPoly.ToMathlib.Polynomial.BivariateDegree
import Mathlib.Tactic

/-!
# Interpolation ingredients for the [BCKHS25] route

Supporting lemmas for the low-`Z`-degree Berlekamp–Welch pair
([BCKHS25] Lemma 2.1) and the improved Guruswami–Sudan interpolant (§3):
this file currently provides the vanishing upgrade — a bivariate polynomial
whose `X`-degree is below the number of its `X`-vanishing points is zero —
which converts "the kernel solution is nontrivial" into "the error-locator
component is nonzero" in both constructions.
-/

namespace BCKHS25

open Polynomial Polynomial.Bivariate

variable {F : Type*} [Field F] [DecidableEq F]

/-- A bivariate polynomial of `X`-degree less than the number of points at
which its `X`-evaluation vanishes is zero (coefficient-wise root counting).
The `A ≠ 0` upgrade of [BCKHS25] Lemma 2.1 and the §3 interpolant both reduce
to this. -/
theorem eq_zero_of_degreeX_lt_card_of_evalX_eq_zero {f : F[X][Y]}
    {s : Finset F} (hdeg : degreeX f < s.card)
    (h : ∀ a ∈ s, evalX a f = 0) : f = 0 := by
  classical
  ext j : 1
  show f.coeff j = (0 : F[X][Y]).coeff j
  rw [Polynomial.coeff_zero]
  -- the j-th Y-coefficient vanishes at every point of s
  have hc : ∀ a ∈ s, (f.coeff j).eval a = 0 := by
    intro a ha
    have h0 := h a ha
    have hcoeff : (evalX a f).coeff j = (f.coeff j).eval a := by
      simp [evalX, Polynomial.coeff]
    rw [h0] at hcoeff
    simpa using hcoeff.symm
  by_cases hj : j ∈ f.support
  · have hdegj : (f.coeff j).natDegree < s.card :=
      lt_of_le_of_lt (Finset.le_sup (f := fun n => (f.coeff n).natDegree) hj) hdeg
    exact Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' (f.coeff j) s hc hdegj
  · exact Polynomial.notMem_support_iff.mp hj

end BCKHS25
