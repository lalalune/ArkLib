/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Dimension of the low-degree polynomial space

`Module.finrank R (Polynomial.degreeLT R k) = k`, via the canonical coefficient isomorphism
`Polynomial.degreeLTEquiv : degreeLT R k ≃ₗ[R] (Fin k → R)`.

This is the dimension count underlying polynomial interpolation and the Reed–Solomon / Berlekamp–
Welch / Polishchuk–Spielman existence arguments: the space of degree-`< k` polynomials is
`k`-dimensional, so a system with more constraints than `k` (or, bivariately, than the bidegree
dimension) has a nonzero solution.
-/

namespace Polynomial

variable {R : Type*} [DivisionRing R]

/-- The space of polynomials of degree `< k` over a division ring is `k`-dimensional. -/
@[simp]
theorem finrank_degreeLT (k : ℕ) : Module.finrank R (Polynomial.degreeLT R k) = k := by
  rw [(Polynomial.degreeLTEquiv R k).finrank_eq, Module.finrank_fintype_fun_eq_card,
    Fintype.card_fin]

end Polynomial
