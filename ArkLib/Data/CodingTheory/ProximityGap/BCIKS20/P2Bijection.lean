/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2Reindex

/-!
# BCIKS20 Appendix A.4 — the value-multiset ↔ (i₁, λ) bijection bricks (toward `RestrictedFaaDiBrunoMatch`)

This file builds the combinatorial bijection underlying `RestrictedFaaDiBrunoMatch` (P2Close.lean)
brick-by-brick, on top of the proven zero/positive-part reindex (`P2Reindex.lean`).

A value multiset `m` (a bag of `card m` orders, summing to its degree) splits canonically as
`replicate (zeroCount m) 0 + positivePart m`.  The zero entries contribute `b 0` factors (= `α₀`
powers in the assembled-series application), and the positive part is the genuine partition `λ`.
These bricks isolate the entropy-free combinatorial content; the algebraic `W`/`ξ`/`ζ` clearing and
the `B_coeff`/Y-Hasse matching are layered on later.
-/

namespace BCIKS20.HenselNumerator

open ArkLib.PowerSeriesComposition

/-- **Zero-entry product extraction.**  For any value multiset `m` and family `b : ℕ → M`, the
product `∏_{j∈m} b j` factors as `(b 0)^{(# zero entries)} · ∏_{j∈positivePart m} b j`.

In the assembled-series application (`b j = coeff j βHenselAssembled`), this peels the `α₀ = b 0`
contributions of the zero orders, leaving the genuine partition product over the positive part. -/
theorem prod_map_eq_zero_pow_mul_positivePart {M : Type*} [CommMonoid M]
    (m : Multiset ℕ) (b : ℕ → M) :
    (m.map b).prod = (b 0) ^ (zeroCount m) * ((positivePart m).map b).prod := by
  conv_lhs => rw [← replicate_zero_add_positivePart m]
  rw [Multiset.map_add, Multiset.prod_add, Multiset.map_replicate, Multiset.prod_replicate]

end BCIKS20.HenselNumerator

-- Axiom audit.
#print axioms BCIKS20.HenselNumerator.prod_map_eq_zero_pow_mul_positivePart
