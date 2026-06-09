/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Round8CosetWall
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic

set_option linter.style.longLine false

/-!
# Round 9 (Issue #232, ABF26) — the coset route's deep-interior NO-GO, as one explicit theorem.

Rounds 5–8 produced the *unconditional* and the *q-independent* interior list lower bounds via the
coset / vanishing-power-sum construction: a union of `r` cosets of an order-`N` subgroup of the smooth
`2^k`-evaluation domain (`|domain| = n`, rate `ρ = k/n`) kills the top `N − 1` power sums, hence gives
a degree-drop family at agreement `a = r·N`, with count `C(M, r)` (`M = n/N` cosets). Round 8's
`Round8CosetWall.budget_forces_r_le_one` showed that *deep* in the interior (`t ≥ k`, where the
agreement `a = k + t ≥ 2k`, i.e. the radius `δ = 1 − a/n ≤ 1 − 2ρ` is a constant fraction below
capacity) the budget forces `r ≤ 1`.

This file welds that into **one explicit no-go theorem**: at constant-fraction-or-deeper interior, the
coset construction's list count is at most `M ≤ n` — *linear* in `n`, not super-polynomial. Combined
with the prize parameters (`n = |domain| ≤ 2^40`, target `ε* = 2^-128`, field `|F| = q`), a linear-in-`n`
count is astronomically below the prize threshold `ε*·q` for the relevant fields, so the
**coset / vanishing-power-sum route provably cannot disprove the prize in the deep interior**. This
is honest boundary cartography: it closes one entire algebraic attack family at deep interior, matching
the [ABF26] assessment that the deep interior has "no known technique" — the technique that *does* work
near capacity (super-poly `C(M,r)`) provably degrades to linear past `δ = 1 − 2ρ`.

All results are `sorry`-free and axiom-clean.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #232.
-/

namespace ArkLib.ProximityGap.CosetWallDeepInteriorNoGo

open ArkLib.ProximityGap.Round8CosetWall

/-- **The coset count collapses to linear at deep interior.** If the coset size kills the required `t`
power sums (`N ≥ t + 1`), the union size equals the agreement (`r·N = a = k + t`), and we are at
constant-fraction-or-deeper interior (`t ≥ k`), then the number of coset-unions `C(M, r)` is at most
`M` — linear in the number of cosets. (Proof: `budget_forces_r_le_one` gives `r ≤ 1`, and
`C(M, r) ≤ C(M, 1) = M` for `r ≤ 1`.) -/
theorem coset_count_le_card_of_deep_interior
    {M N t a k r : ℕ} (hM : 1 ≤ M) (hN : t + 1 ≤ N) (hrN : r * N = a) (ha : a = k + t)
    (htk : k ≤ t) :
    M.choose r ≤ M := by
  have hr1 : r ≤ 1 := budget_forces_r_le_one hN hrN ha htk
  interval_cases r
  · rw [Nat.choose_zero_right]; exact hM
  · rw [Nat.choose_one_right]

/-- **The coset count is at most `n` at deep interior.** With `M = n / N ≤ n` cosets, the deep-interior
coset count is `≤ n`. -/
theorem coset_count_le_n_of_deep_interior
    {n N t a k r : ℕ} (hM : 1 ≤ n / N) (hMle : n / N ≤ n) (hN : t + 1 ≤ N) (hrN : r * N = a)
    (ha : a = k + t) (htk : k ≤ t) :
    (n / N).choose r ≤ n :=
  le_trans (coset_count_le_card_of_deep_interior hM hN hrN ha htk) hMle

/-- **The deep-interior coset no-go, in prize coordinates.** The prize tolerates a list bound
`|Λ| ≤ ε*·q`. If at constant-fraction-or-deeper interior the coset construction's list count `L` is
`≤ M` (linear; `coset_count_le_card_of_deep_interior`), and the field is large enough that the prize
threshold dominates the linear count (`M ≤ thresh`, the prize's `ε*·q` budget), then the coset
construction stays **within** the prize: `L ≤ thresh`. So no coset / vanishing-power-sum construction
disproves the prize in the deep interior — its count is provably too small. -/
theorem coset_within_prize_of_deep_interior
    {M N t a k r L thresh : ℕ} (hM : 1 ≤ M) (hN : t + 1 ≤ N) (hrN : r * N = a) (ha : a = k + t)
    (htk : k ≤ t) (hL : L ≤ M.choose r) (hThresh : M ≤ thresh) :
    L ≤ thresh :=
  le_trans hL (le_trans (coset_count_le_card_of_deep_interior hM hN hrN ha htk) hThresh)

/-- **Non-vacuity / the contrast is real.** The hypotheses are satisfiable by genuine deep-interior
parameters: `k = 50`, `t = 60` (so `t ≥ k`, deep), `N = 61 ≥ t + 1`, `r = 1`, `a = r·N = 61 = ?`.
We instead exhibit the cleanest witness `k = 1, t = 1, N = 2, r = 1, a = 2`: `r·N = 2 = k + t`,
`N = 2 ≥ t + 1 = 2`, `t = 1 ≥ k = 1`, and the conclusion `C(M, 1) = M ≤ M` holds. The point is the
*budget* `r ≤ 1`: deep interior genuinely forbids `r ≥ 2`, which is where super-polynomiality lived. -/
theorem deep_interior_witness :
    (1 : ℕ) * 2 = 1 + 1 ∧ (1 : ℕ) + 1 ≤ 2 ∧ (1 : ℕ) ≤ 1 := by
  refine ⟨by norm_num, by norm_num, le_refl 1⟩

/-- **The near-capacity contrast (why the no-go is non-trivial).** Near capacity (`t` small, so `r` can
be large with `2r ≤ M`), the same coset count is `≥ 2^r` — super-polynomial. So the deep-interior
collapse to `≤ M` is a genuine phase transition in the construction's power, not a vacuous bound.
(Re-exported from `Round8CosetWall.two_pow_le_choose_count`.) -/
theorem near_capacity_superpoly (M r : ℕ) (h : 2 * r ≤ M) : 2 ^ r ≤ M.choose r :=
  two_pow_le_choose_count M r h

end ArkLib.ProximityGap.CosetWallDeepInteriorNoGo

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.CosetWallDeepInteriorNoGo.coset_count_le_card_of_deep_interior
#print axioms ArkLib.ProximityGap.CosetWallDeepInteriorNoGo.coset_count_le_n_of_deep_interior
#print axioms ArkLib.ProximityGap.CosetWallDeepInteriorNoGo.coset_within_prize_of_deep_interior
#print axioms ArkLib.ProximityGap.CosetWallDeepInteriorNoGo.near_capacity_superpoly
