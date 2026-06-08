/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Team
-/

import ArkLib.Data.Polynomial.Multivariate.Interpolation
import ArkLib.Data.Polynomial.Multivariate.HasseDerivative
import ArkLib.Data.CodingTheory.SubspaceDesign.Basic

/-!
# List-Decoding Capacity Bounds from GKL24
This file formalizes the polynomial interpolation bounds for list-decoding capacity
as presented in Guruswami-Kopparty-Lovelock 2024 (GKL24).
-/

namespace CodingTheory.Bounds.GKL24

open Polynomial MvPolynomial
open scoped BigOperators

variable {F : Type} [Field F]

/-- The GKL24 interpolation condition bounds the degrees required to ensure a non-zero
interpolating polynomial Q(X,Y) exists for given evaluation points and multiplicities. -/
theorem gkl24_interpolation_existence
    (points : Finset (F × F))
    (multiplicities : (F × F) → ℕ)
    (deg_X deg_Y : ℕ)
    (h_dim : (points.sum (fun p => (multiplicities p + 1) * multiplicities p / 2)) < (deg_X + 1) * (deg_Y + 1)) :
    ∃ Q : MvPolynomial (Fin 2) F, Q ≠ 0 ∧
      (MvPolynomial.degreeOf 0 Q ≤ deg_X) ∧
      (MvPolynomial.degreeOf 1 Q ≤ deg_Y) ∧
      ∀ p ∈ points, ArkLib.MvPolynomial.mult_ge ![p.1, p.2] (multiplicities p) Q := by
  sorry

end CodingTheory.Bounds.GKL24
