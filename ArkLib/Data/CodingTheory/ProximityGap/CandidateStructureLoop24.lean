/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Loop 24 — the per-fold recursion criterion: constant blowup ⟹ polynomial ⟹ prize TRUE

Loop 23 showed the smooth-domain prize is a recursion over the `m`-level `2^m`-fold tower: the
scale-`N` list relates to the scale-`N/2` list plus the one-fold orbit contribution. This file
formalizes the *quantitative* telescoping criterion that decides the prize.

Let `T j` be the list size at fold level `j` (so `T 0` is the base `μ_1` list, `T m` the full
scale-`N=2^m` list). The per-fold step gives a blowup factor `a`:

    T (j+1) ≤ a · T j.

Telescoping over the `m` levels gives `T m ≤ a^m · T 0` (`fold_recursion_telescopes`). The decisive
fact is what `a^m` is **when `a` is a constant** (independent of `N`): if `a ≤ 2^c`, then

    a^m ≤ (2^m)^c = N^c,

a **polynomial in the domain size** `N = 2^m` (`constant_blowup_polynomial`). So:

* **constant per-fold blowup `a ≤ 2^c` ⟹** total list `≤ (2^m)^c · T 0` ⟹ the prize mass clause with
  `c₁ = c` (Loop11/Loop13/Loop17 then clear the RHS) — **prize TRUE**;
* **per-fold blowup growing with `N`** (super-constant `a = a(N) → ∞`) ⟹ `a^m` super-polynomial in
  `N` ⟹ **prize FALSE** (Loop8 `q`-growth).

This is the exact dichotomy of the FRI/STIR-to-capacity soundness frontier (Loop23): the prize holds
iff the per-fold proximity-gap soundness blowup is `N`-independent. A single fold's single orbit is
absorbed (Loop21); the open question is whether the blowup *stays constant across all `m` folds* for
plain smooth-deterministic RS, or accumulates. This file proves the telescoping arithmetic,
sorry-free and axiom-clean. See `DISPROOF_LOG.md` (Loop24 — per-fold recursion criterion).
-/

namespace ArkLib.ProximityGap.StructureLoop24

/-- **Telescoping of the per-fold recursion.** If the list size `T` obeys `T (j+1) ≤ a · T j` at every
fold level with blowup factor `a ≥ 0` and nonneg sizes, then after `m` folds `T m ≤ a^m · T 0`. -/
theorem fold_recursion_telescopes
    (T : ℕ → ℝ) (a : ℝ) (ha : 0 ≤ a)
    (hstep : ∀ j, T (j + 1) ≤ a * T j) :
    ∀ m, T m ≤ a ^ m * T 0 := by
  intro m
  induction m with
  | zero => simp
  | succ n ih =>
      calc T (n + 1) ≤ a * T n := hstep n
        _ ≤ a * (a ^ n * T 0) := by exact mul_le_mul_of_nonneg_left ih ha
        _ = a ^ (n + 1) * T 0 := by ring

/-- **Constant blowup ⟹ polynomial in the domain size.** If the per-fold blowup factor is bounded by
a *constant* power of two, `a ≤ 2^c` (`a ≥ 0`), then over `m` folds the telescoped factor is at most
`(2^m)^c = N^c` — polynomial in the domain size `N = 2^m`. So a constant per-fold blowup yields a
list polynomial in `2^m`, exactly the prize RHS shape (`c₁ = c`). -/
theorem constant_blowup_polynomial
    {a : ℝ} {c m : ℕ} (ha : 0 ≤ a) (hac : a ≤ (2 : ℝ) ^ c) :
    a ^ m ≤ ((2 : ℝ) ^ m) ^ c := by
  calc a ^ m ≤ ((2 : ℝ) ^ c) ^ m := by gcongr
    _ = (2 : ℝ) ^ (c * m) := by rw [← pow_mul]
    _ = (2 : ℝ) ^ (m * c) := by rw [Nat.mul_comm]
    _ = ((2 : ℝ) ^ m) ^ c := by rw [pow_mul]

/-- **The prize-side conclusion (constant-blowup branch).** Combining the two: under a constant
per-fold blowup `a ≤ 2^c`, the full scale-`N=2^m` list is bounded by `(2^m)^c · T 0`, polynomial in
the domain size — the TRUE branch of the FRI-tower dichotomy. -/
theorem fold_list_polynomial_of_constant_blowup
    (T : ℕ → ℝ) {a : ℝ} {c : ℕ} (ha : 0 ≤ a) (hac : a ≤ (2 : ℝ) ^ c)
    (hT : ∀ j, 0 ≤ T j) (hstep : ∀ j, T (j + 1) ≤ a * T j) (m : ℕ) :
    T m ≤ ((2 : ℝ) ^ m) ^ c * T 0 := by
  refine le_trans (fold_recursion_telescopes T a ha hstep m) ?_
  exact mul_le_mul_of_nonneg_right (constant_blowup_polynomial ha hac) (hT 0)

end ArkLib.ProximityGap.StructureLoop24
