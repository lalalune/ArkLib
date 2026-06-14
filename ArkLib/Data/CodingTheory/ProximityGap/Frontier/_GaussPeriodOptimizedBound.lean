/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GaussPeriodMomentBound

/-!
# The optimized Gauss-period bound `‖η_b‖ ≤ √(2e · n · ln q)` (#407)

`GaussPeriodMomentBound.worstCaseIncompleteSumBound_of_energyBound` proves the **per-order**
moment bound `‖η_b‖² ≤ (q·(2r-1)‼·n^r)^{1/r}` from `GaussianEnergyBound G r`, and its docstring
notes that *minimizing over `r` (optimum `r* ≈ ln q`) yields the `√(2 n ln q)` Gauss-period bound*.
This file machine-checks that final optimization step, which was previously only stated informally.

The closed form is the prize sup-norm target up to the constant: choosing any order `r ≥ ln q`
collapses the field-size factor `q^{1/r} ≤ e`, and the crude factorial estimate
`(2r-1)‼ ≤ (2r)^r` gives `((2r-1)‼)^{1/r} ≤ 2r`, so

> `‖η_b‖² ≤ e · 2r · n = 2e · n · r`,  hence at `r = ⌈ln q⌉`:  `‖η_b‖ ≤ √(2e) · √(n · ln q)`.

This is **conditional on `GaussianEnergyBound G r`** — the proven char-0 / small-`n` input whose
char-`p` transfer at the prize parameters (`n = 2^μ`, `q ≈ n^4`, `r ≈ ln q`) is the single open
residual (= the BGK / Paley square-root-cancellation wall; see `EffectiveTransfer.lean` for the
proven regime `q > (2r)^{n/2}`).  It does **not** prove that input; it formalizes the elementary
implication `GaussianEnergyBound at r ≈ ln q ⟹ √-cancellation sup-norm`, pinning the constant.

The sharp constant `√2` needs Stirling `(2r-1)‼ ∼ √2·(2r/e)^r`; the crude `(2r)^r` here yields
`√(2e) ≈ 2.33` in its place — same shape, an explicit absolute constant.

Issue #407.
-/

open ArkLib.ProximityGap.GaussPeriodMomentBound

namespace ProximityGap.Frontier.GaussPeriodOptimizedBound

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Crude double-factorial estimate.** `(2r-1)‼ ≤ (2r)^r`: a product of `r` odd factors each
`≤ 2r`. -/
theorem doubleFactorial_le_pow (r : ℕ) :
    (Nat.doubleFactorial (2 * r - 1) : ℝ) ≤ ((2 * r : ℕ) : ℝ) ^ r := by
  have hnat : Nat.doubleFactorial (2 * r - 1) ≤ (2 * r) ^ r := by
    induction r with
    | zero => simp [Nat.doubleFactorial]
    | succ k ih =>
      -- (2(k+1)-1)‼ = (2k+1)·(2k-1)‼ ≤ (2k+1)·(2k)^k ≤ (2k+2)·(2k+2)^k = (2k+2)^{k+1}
      have hstep : 2 * (k + 1) - 1 = (2 * k + 1) := by omega
      rw [hstep, Nat.doubleFactorial]
      have h1 : (2 * k + 1 - 1) = 2 * k := by omega
      rw [h1]
      calc (2 * k + 1) * Nat.doubleFactorial (2 * k - 1)
          ≤ (2 * k + 1) * (2 * k) ^ k := by
            exact Nat.mul_le_mul_left _ ih
        _ ≤ (2 * (k + 1)) * (2 * (k + 1)) ^ k := by
            apply Nat.mul_le_mul
            · omega
            · exact Nat.pow_le_pow_left (by omega) k
        _ = (2 * (k + 1)) ^ (k + 1) := by rw [pow_succ]; ring
  calc (Nat.doubleFactorial (2 * r - 1) : ℝ)
      ≤ (((2 * r) ^ r : ℕ) : ℝ) := by exact_mod_cast hnat
    _ = ((2 * r : ℕ) : ℝ) ^ r := by push_cast; ring
