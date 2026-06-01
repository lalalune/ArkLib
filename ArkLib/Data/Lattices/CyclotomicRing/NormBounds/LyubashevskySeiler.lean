/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Data.Lattices.CyclotomicRing.NormBounds.Basic
import Mathlib.Data.Nat.Prime.Basic

/-!
# Lyubashevsky–Seiler: Short Elements Are Invertible

The Lyubashevsky–Seiler invertibility result [LS18, Corollary 1.2]; recalled as Lemma 3 of
the Hachi paper [NOZ26]: for a prime `q ≡ 5 (mod 8)` and power-of-two degree `deg φ`, a
nonzero element of `Rq Φ = ZMod q[X]/(φ)` whose centered Euclidean norm is below `√q` is a
unit.

This is the second *deep* input to the Greyhound [NS24] / Hachi [NOZ26] weak-binding argument
— a genuine piece of algebraic number theory (factorization of `φ mod q`, the maximal ideals
realized as ideal lattices of determinant `q^{d/2}`, and a minimum-distance lower bound via the
cyclotomic embedding). None of this is available in Mathlib in directly usable form, so the
result is deferred (`sorry`), exactly as in VCV-io's `LatticeCrypto.Ring.ShortInvertible`.

## References

* [Lyubashevsky, V., and Seiler, G., *Short, Invertible Elements in Partially Splitting
    Cyclotomic Rings*][LS18]
* [Nguyen, N. K., and Seiler, G., *Greyhound: Fast Polynomial Commitments from Lattices*][NS24]
* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
    Polynomial Commitments over Extension Fields*][NOZ26]
-/

open scoped BigOperators

namespace ArkLib.Lattices.CyclotomicModulus

variable {q : ℕ} [NeZero q] [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)]
  (Φ : CyclotomicModulus (ZMod q)) [IsCyclotomic Φ]

/-- **Lyubashevsky–Seiler: short elements are invertible** (LS18, Cor. 1.2; Hachi, Lemma 3).
For a prime `q ≡ 5 (mod 8)` and power-of-two degree `deg φ`, a nonzero element of `Rq Φ`
with centered `ℓ₁` norm `≤ κ` and `κ² < q` is a unit (then `‖c‖₂² ≤ ‖c‖₁² ≤ κ² < q`, the
LS bound `‖c‖ < √q`). A genuine piece of algebraic number theory (ideal-lattice minimum
distance via the cyclotomic embedding); recorded here with `sorry`. -/
theorem isUnit_of_l1Norm_le (hq5 : q % 8 = 5)
    (hd : ∃ α : ℕ, Φ.φ.natDegree = 2 ^ α) {c : Rq Φ} {κ : ℕ}
    (hpos : 0 < Rq.l1Norm Φ c) (hle : Rq.l1Norm Φ c ≤ κ) (hκ : κ ^ 2 < q) :
    IsUnit c := by
  sorry

end ArkLib.Lattices.CyclotomicModulus
