/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Loop 26 — additive vs multiplicative per-fold growth: the refined crux

Loop 24/25 telescoped the FRI-tower list recursion under the *multiplicative* model
`T(j+1) ≤ a·T(j)` (giving `a^m`, which is polynomial only if `a` is `N`-independent — the open
scalar). But that is the **pessimistic** model. FRI/STIR soundness analyses bound the error of a
multi-round protocol by a **union bound over rounds** — an *additive* per-round contribution. If the
list recursion is likewise additive,

    T(j+1) ≤ T(j) + b,

then it grows only **linearly** in the number of folds `m = log₂ N`:

    T(m) ≤ T(0) + m·b   ≤   T(0) + (2^m)·b,

since `m ≤ 2^m`. That is polynomial in the domain size `N = 2^m` with `c₁ = 1` — **unconditionally
prize-TRUE**, with no open scalar at all. So the genuine crux is sharper than Loop24/25 suggested:

> **Refined open question.** Is the smooth-deterministic per-fold list growth *additive*
> (`+b`, union-bound style ⇒ prize TRUE with `c₁=1`) or genuinely *multiplicative with an
> `N`-growing factor* (`×a(N)` ⇒ prize FALSE)? Constant-factor multiplicative growth is *also* fine
> (Loop24, `a^m = (2^m)^{log₂ a}`); only a *growing* multiplicative factor disproves.

This file proves the additive branch is unconditionally polynomial, sorry-free and axiom-clean —
narrowing the disproof target to "the per-fold factor must be multiplicative *and* `N`-growing", a
strictly stronger requirement than Loop24/25 alone stated. See `DISPROOF_LOG.md` (Loop26).
-/

namespace ArkLib.ProximityGap.StructureLoop26

/-- **Additive per-fold recursion is linear in the number of folds.** If `T(j+1) ≤ T(j) + b` at
every fold, then after `m` folds `T(m) ≤ T(0) + m·b`. -/
theorem additive_recursion_linear
    (T : ℕ → ℝ) (b : ℝ) (hstep : ∀ j, T (j + 1) ≤ T j + b) :
    ∀ m, T m ≤ T 0 + m * b := by
  intro m
  induction m with
  | zero => simp
  | succ n ih =>
      calc T (n + 1) ≤ T n + b := hstep n
        _ ≤ (T 0 + n * b) + b := by linarith
        _ = T 0 + (n + 1 : ℕ) * b := by push_cast; ring

/-- **Additive growth is polynomial in the domain size (`c₁ = 1`), unconditionally.** With `b ≥ 0`
and base `T(0) ≤ B₀`, since `m ≤ 2^m` the additive recursion gives `T(m) ≤ B₀ + (2^m)·b` — linear in
the domain size `N = 2^m`. So if the per-fold list growth is additive, the prize holds with `c₁ = 1`
and **no open scalar**: union-bound-style fold growth ⇒ prize TRUE. -/
theorem additive_recursion_le_domain
    (T : ℕ → ℝ) {b B₀ : ℝ} (hb : 0 ≤ b)
    (hstep : ∀ j, T (j + 1) ≤ T j + b) (hbase : T 0 ≤ B₀) (m : ℕ) :
    T m ≤ B₀ + ((2 : ℝ) ^ m) * b := by
  have hlin : T m ≤ T 0 + m * b := additive_recursion_linear T b hstep m
  have hm : (m : ℝ) ≤ (2 : ℝ) ^ m := by
    have := Nat.lt_two_pow_self (n := m)
    calc (m : ℝ) ≤ ((2 ^ m : ℕ) : ℝ) := by exact_mod_cast this.le
      _ = (2 : ℝ) ^ m := by push_cast; ring
  have hmb : (m : ℝ) * b ≤ ((2 : ℝ) ^ m) * b := mul_le_mul_of_nonneg_right hm hb
  linarith

end ArkLib.ProximityGap.StructureLoop26
