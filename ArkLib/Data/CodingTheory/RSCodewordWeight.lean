/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.RSWeightEnumerator
import ArkLib.Data.CodingTheory.ReedSolomon

/-!
# Reed–Solomon codeword weight ↔ polynomial eval-support

The Hamming weight of the Reed–Solomon codeword `evalOnPoints domain p` equals the cardinality of the
polynomial's evaluation support `evalSupport domain p` (the points where `p` does not vanish).  This is
the bridge connecting the polynomial-level weight enumerator / near-count (`card_evalWeight_le`,
`card_evalWeight_le_sum`) to the actual codewords of `ReedSolomon.code`, completing the #82
covered-fraction chain at the codeword level: the count of near codewords is controlled by the count
of low-eval-weight polynomials, which the MDS weight enumerator bounds.
-/

namespace ArkLib.CS25

open scoped BigOperators
open Polynomial

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **RS codeword weight = polynomial eval-support size.**  `Δ₀(evalOnPoints domain p, 0)` (the Hamming
weight of the RS codeword of `p`) equals `|evalSupport domain p|` — the number of evaluation points at
which `p` does not vanish.  Essentially definitional: `(evalOnPoints domain p) i = p.eval (domain i)`. -/
theorem hammingNorm_evalOnPoints_eq_evalSupport_card (domain : ι ↪ F) {deg : ℕ}
    (p : Polynomial.degreeLT F deg) :
    hammingNorm (ReedSolomon.evalOnPoints domain (p : F[X])) = (evalSupport domain p).card := by
  unfold hammingNorm evalSupport
  congr 1

end ArkLib.CS25

-- Axiom audit.
#print axioms ArkLib.CS25.hammingNorm_evalOnPoints_eq_evalSupport_card
