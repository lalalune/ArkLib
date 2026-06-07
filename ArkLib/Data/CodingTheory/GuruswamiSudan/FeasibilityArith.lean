import Mathlib
import ArkLib.Data.CodingTheory.GuruswamiSudan.MonomialCount
import ArkLib.Data.CodingTheory.GuruswamiSudan.ListSizeBound

/-! Pure-arithmetic Guruswami–Sudan interpolation feasibility, obtained by feeding the explicit
monomial-count lower bound `card_monoIdx_ge_triangle` into the in-tree feasibility theorems. This
discharges the `#monomials`-shaped hypotheses (`hdim`) with a concrete inequality the regime can
check directly — no reference to `(monoIdx k D).card` survives. -/

open Polynomial

namespace GSListSizeBound

variable {F : Type*} [Field F]

/-- **Arithmetic interpolation feasibility in the GS window `D = m·a − 1`.** If a free parameter
`t ≤ m·a − 1` with `k·(t−1) ≤ m·a − 1` satisfies the explicit triangle inequality
`n·m(m+1)/2 < t·(m·a−1) − k·t(t−1)/2`, then a nonzero interpolant vanishing to order `m` at all
`n` points exists. This replaces the abstract `#monomials` hypothesis of
`interpolation_feasible_window` with a checkable arithmetic side condition. -/
theorem interpolation_feasible_window_arith (k m a n t : ℕ) (xs ys : Fin n → F)
    (htk : k * (t - 1) ≤ m * a - 1) (ht : t ≤ m * a - 1)
    (harith : n * (m * (m + 1) / 2) < t * (m * a - 1) - k * (t * (t - 1) / 2)) :
    ∃ c : GSMultInterp.CoeffSpace (F := F) k (m * a - 1), c ≠ 0 ∧
      ∀ i : Fin n, GSMultInterp.vanishesToOrder k (m * a - 1) m c (xs i) (ys i) :=
  interpolation_feasible_window k m a n xs ys
    (lt_of_lt_of_le harith (GSMultInterp.card_monoIdx_ge_triangle k (m * a - 1) t htk ht))

#print axioms GSListSizeBound.interpolation_feasible_window_arith

end GSListSizeBound
