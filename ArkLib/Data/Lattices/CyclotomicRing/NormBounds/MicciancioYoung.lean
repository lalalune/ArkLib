/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Data.Lattices.CyclotomicRing.NormBounds.Basic

/-!
# The Micciancio/Young Product Norm-Growth Bound

The honest Young/Micciancio inequality `‖(c·d)·v‖₂² ≤ ‖d‖₁² · ‖c·v‖₂²` over the cyclotomic
convolution with centered representatives: scaling an already-`c`-scaled vector by a further
ring element `d` of bounded centered `ℓ₁` norm grows the squared `ℓ₂` norm by at most `κ²`.

This is one of the two *deep* analytic inputs to the Greyhound [NS24] / Hachi [NOZ26]
weak-binding argument (discrete Cauchy–Schwarz over the cyclic convolution, together with
minimality of the centered representative; the product norm inequality `‖fg‖ ≤ ‖f‖₁·‖g‖` is
[Mic07, Lemma 2]). Its proof is currently deferred (`sorry`), exactly as in VCV-io's
`LatticeCrypto.Ring.NormBounds`.

## References

* [Micciancio, D., *Generalized Compact Knapsacks, Cyclic Lattices, and Efficient One-Way
    Functions*][Mic07]
* [Nguyen, N. K., and Seiler, G., *Greyhound: Fast Polynomial Commitments from Lattices*][NS24]
* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
    Polynomial Commitments over Extension Fields*][NOZ26]
-/

open scoped BigOperators

namespace ArkLib.Lattices.CyclotomicModulus

variable {q : ℕ} [NeZero q] [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)]
  (Φ : CyclotomicModulus (ZMod q)) [IsCyclotomic Φ]

/-- **Micciancio/Young product bound.** Scaling an already-`c`-scaled vector by a further
ring element `d` of bounded centered `ℓ₁` norm grows the squared `ℓ₂` norm by at most `κ²`
(the honest Young/Micciancio inequality `‖(c·d)·v‖₂² ≤ ‖d‖₁² · ‖c·v‖₂²` over the cyclotomic
convolution with centered representatives; discrete Cauchy–Schwarz, deferred). -/
theorem scalarVecMul_mul_l2NormSq_le {cols : ℕ} (c d : Rq Φ) (v : PolyVec (Rq Φ) cols)
    {κ βSq : ℕ} (hd : Rq.l1Norm Φ d ≤ κ)
    (hv : vecL2NormSq Φ (scalarVecMul c v) ≤ βSq) :
    vecL2NormSq Φ (scalarVecMul (c * d) v) ≤ scalarVecMulMulL2NormSqBound κ βSq := by
  sorry

end ArkLib.Lattices.CyclotomicModulus
