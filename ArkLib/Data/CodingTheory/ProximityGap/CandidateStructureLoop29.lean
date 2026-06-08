/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Loop 29 — the AFFINE per-fold recursion: the unified master criterion

Loops 24/26/27 (and the swarm's Loop28 variable-factor version) handled the multiplicative (`×a`),
additive (`+b`), and polynomial-additive special cases of the FRI-tower list recursion. The
*realistic* per-fold model is **affine** — each fold both branches multiplicatively and adds new close
codewords:

    T(j+1) ≤ a · T(j) + b.

This file proves the master bound subsuming the constant-coefficient cases: with multiplicative factor
`a ≥ 1` and additive term `b ≥ 0`,

    T(m) ≤ a^m · (T(0) + b·m).

(Recovers Loop26's `T(0) + b·m` at `a = 1`, and Loop24's `a^m·T(0)` at `b = 0`.) The polynomial
corollary gives the **complete dichotomy**: if `a ≤ 2^c` (`N`-independent multiplicative) and
`b ≤ (2^m)^d` (polynomial additive) with base `T(0) ≤ 1`, the full list is polynomial in `2^m` ⇒
**prize TRUE**; the prize is **FALSE** only if `a` grows with `N` or `b` is super-polynomial.

So across every constant-coefficient recursion shape (mult / add / poly-add / affine), the prize
verdict is the single question: **is the per-fold proximity-gap soundness contribution `N`-independent
multiplicative + polynomial additive (TRUE), or genuinely `N`-growing (FALSE)?** Sorry-free,
axiom-clean. See `DISPROOF_LOG.md` (Loop29 — affine master recursion).
-/

namespace ArkLib.ProximityGap.StructureLoop29

/-- **Affine per-fold recursion master bound.** If `T(j+1) ≤ a·T(j) + b` at every fold with `a ≥ 1`
and `b ≥ 0`, then `T(m) ≤ a^m · (T(0) + b·m)`. Subsumes the multiplicative (`b=0`) and additive
(`a=1`) cases. -/
theorem affine_recursion_bound
    (T : ℕ → ℝ) {a b : ℝ} (ha : 1 ≤ a) (hb : 0 ≤ b)
    (hstep : ∀ j, T (j + 1) ≤ a * T j + b) :
    ∀ m, T m ≤ a ^ m * (T 0 + b * m) := by
  have ha0 : 0 ≤ a := by linarith
  intro m
  induction m with
  | zero => simp
  | succ n ih =>
      have hpow1 : (1 : ℝ) ≤ a ^ (n + 1) := one_le_pow₀ ha
      calc T (n + 1) ≤ a * T n + b := hstep n
        _ ≤ a * (a ^ n * (T 0 + b * n)) + b := by
              have := mul_le_mul_of_nonneg_left ih ha0; linarith
        _ = a ^ (n + 1) * (T 0 + b * n) + b := by rw [pow_succ]; ring
        _ ≤ a ^ (n + 1) * (T 0 + b * n) + a ^ (n + 1) * b := by
              have hbb : b ≤ a ^ (n + 1) * b := by nlinarith [hpow1, hb]
              linarith
        _ = a ^ (n + 1) * (T 0 + b * (n + 1 : ℕ)) := by push_cast; ring

/-- **Polynomial corollary (the complete TRUE branch).** With an `N`-independent multiplicative factor
`a ≤ 2^c`, a polynomial additive term `b ≤ (2^m)^d`, base `0 ≤ T(0) ≤ 1`, the full scale-`2^m` list
obeys `T(m) ≤ (2^m)^c · (1 + (2^m)^d · 2^m)`, polynomial in `2^m` — clearing the prize RHS. The prize
is FALSE only outside these hypotheses (`N`-growing `a`, or super-polynomial `b`). -/
theorem affine_recursion_poly
    (T : ℕ → ℝ) {a b : ℝ} {c d m : ℕ}
    (ha : 1 ≤ a) (hac : a ≤ (2 : ℝ) ^ c) (hb : 0 ≤ b) (hbd : b ≤ ((2 : ℝ) ^ m) ^ d)
    (hT0lo : 0 ≤ T 0) (hbase : T 0 ≤ 1)
    (hstep : ∀ j, T (j + 1) ≤ a * T j + b) :
    T m ≤ ((2 : ℝ) ^ m) ^ c * (1 + ((2 : ℝ) ^ m) ^ d * (2 : ℝ) ^ m) := by
  have hmle : (m : ℝ) ≤ (2 : ℝ) ^ m := by
    have := Nat.lt_two_pow_self (n := m); exact_mod_cast this.le
  have hmain : T m ≤ a ^ m * (T 0 + b * m) := affine_recursion_bound T ha hb hstep m
  have hpow : a ^ m ≤ ((2 : ℝ) ^ m) ^ c := by
    calc a ^ m ≤ ((2 : ℝ) ^ c) ^ m := by gcongr
      _ = (2 : ℝ) ^ (m * c) := by rw [← pow_mul, Nat.mul_comm]
      _ = ((2 : ℝ) ^ m) ^ c := by rw [pow_mul]
  have hbm : b * (m : ℝ) ≤ ((2 : ℝ) ^ m) ^ d * (2 : ℝ) ^ m :=
    mul_le_mul hbd hmle (by positivity) (by positivity)
  have hinner : T 0 + b * (m : ℝ) ≤ 1 + ((2 : ℝ) ^ m) ^ d * (2 : ℝ) ^ m := by linarith
  have hinner0 : 0 ≤ T 0 + b * (m : ℝ) := by
    have : 0 ≤ b * (m : ℝ) := mul_nonneg hb (by positivity); linarith
  calc T m ≤ a ^ m * (T 0 + b * m) := hmain
    _ ≤ ((2 : ℝ) ^ m) ^ c * (1 + ((2 : ℝ) ^ m) ^ d * (2 : ℝ) ^ m) :=
        mul_le_mul hpow hinner hinner0 (by positivity)

end ArkLib.ProximityGap.StructureLoop29
