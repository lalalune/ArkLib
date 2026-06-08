/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Team
-/

import ArkLib.Data.Polynomial.Multivariate.HasseDerivative
import ArkLib.Data.CodingTheory.SubspaceDesign.Basic

/-!
# List-Decoding Multiplicity Bounds from BCHKS25
This file formalizes the multiplicity assignment bounds from
Brakerski, Canetti, Holmgren, Kalai, and Stephens-Davidowitz (BCHKS25).
-/

namespace CodingTheory.Bounds.BCHKS25

open Polynomial MvPolynomial
open scoped BigOperators

variable {F : Type} [Field F]

/-- The BCHKS25 condition on polynomial evaluation: if the sum of multiplicities of roots
along a codeword exceeds the total degree of the polynomial, the polynomial must identically
vanish along that codeword. -/
theorem bchks25_vanishing_of_multiplicity_sum_gt_degree
    (Q : MvPolynomial (Fin 2) F)
    (f : F → F)
    (eval_points : Finset F)
    (multiplicities : F → ℕ)
    (h_mult : ∀ x ∈ eval_points, ArkLib.Polynomial.Multivariate.mult_ge Q (x, f x) (multiplicities x))
    (h_sum_gt : (eval_points.sum multiplicities) > MvPolynomial.totalDegree Q) :
    ∀ x, MvPolynomial.eval (fun i => if i = 0 then x else f x) Q = 0 := by
  sorry

end CodingTheory.Bounds.BCHKS25
