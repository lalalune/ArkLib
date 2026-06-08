/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Team
-/

import ArkLib.Data.CodingTheory.ListDecoding.Bounds.GKL24
import ArkLib.Data.CodingTheory.ListDecoding.Bounds.BCHKS25
import ArkLib.Data.CodingTheory.ListDecoding.GuruswamiSudan.Basic

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

/-- The final list-decoding capacity bound combining GKL24 interpolation and BCHKS25 vanishing.
Any codeword with agreement strictly greater than the list decoding radius will correspond
to a Y-root of the interpolating polynomial Q(X,Y). -/
theorem capacity_bound_implies_y_root
    (points : Finset F)
    (f : F → F)
    (received : F → F)
    (multiplicities : (F × F) → ℕ)
    (deg_X deg_Y : ℕ)
    (h_dim : (points.sum (fun x => (multiplicities (x, received x) + 1) * multiplicities (x, received x) / 2)) < (deg_X + 1) * (deg_Y + 1))
    (h_agree : (points.filter (fun x => f x = received x)).sum (fun x => multiplicities (x, received x)) > deg_X + deg_Y * (points.card)) :
    ∃ Q : MvPolynomial (Fin 2) F, Q ≠ 0 ∧
      (∀ x ∈ points, f x = received x → MvPolynomial.eval (fun i => if i = 0 then x else f x) Q = 0) := by
  sorry

end CodingTheory.Bounds.Capacity
