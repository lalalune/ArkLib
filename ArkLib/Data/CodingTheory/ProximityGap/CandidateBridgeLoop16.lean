/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.Field.Basic

/-!
# Loop 16 — the second-moment (Johnson) method's wall is *exactly* the carving threshold `η₀`

The in-tree `JohnsonList.johnson_list_bound` gives `|L|·(a² − n·b) ≤ n²` and is usable only under its
gap hypothesis `n·b ≤ a²` (`johnson_list_bound_div` needs the strict form). Instantiating it for the
prize via the rate-shift (Loop15) — agreement `a = (ρ+η)·n`, pairwise codeword agreement `b = ρ·n`
(RS is MDS: distinct degree-`<ρn` polynomials agree on `≤ ρn − 1 < ρn` points) — the Johnson
denominator is

    a² − n·b = ((ρ+η)n)² − n·(ρn) = n²·((ρ+η)² − ρ).

This is **positive iff `(ρ+η)² > ρ`, i.e. iff `η > η₀ = √ρ − ρ`** — exactly the carving threshold
(Loop10). So the *entire* second-moment / Johnson toolkit applies precisely on the large-gap side and
yields **no bound at all** in the small-gap band `0 < η ≤ η₀`: the denominator is `≤ 0` there.

**Consequence (honest).** The open core is not a gap in *this* development — it is the intrinsic wall
of every elementary (first/second-moment, Johnson, pairwise-agreement) argument. Crossing `η₀`
provably requires a genuinely higher method (Guruswami–Sudan multiplicities, which for *plain* RS
also top out at the Johnson radius, or the Brakensiek–Gopi–Makam genericity argument, which needs
*generic* — not smooth-deterministic — evaluation points). This is why the prize is the live frontier.

Sorry-free, axiom-clean. See `DISPROOF_LOG.md` (Loop16 — method wall = carving).
-/

namespace ArkLib.ProximityGap.BridgeLoop16

open scoped Real

/-- **The Johnson denominator under the rate-shift instantiation.** With agreement `a = (ρ+η)·n`
and pairwise agreement `b = ρ·n`, `a² − n·b = n²·((ρ+η)² − ρ)`. -/
theorem johnson_denom_eq (ρ η n : ℝ) :
    ((ρ + η) * n) ^ 2 - n * (ρ * n) = n ^ 2 * ((ρ + η) ^ 2 - ρ) := by ring

/-- **The method's gap hypothesis is satisfiable iff `(ρ+η)² > ρ`.** For `n > 0`, the Johnson
denominator `a² − n·b` is positive iff `ρ < (ρ+η)²`. -/
theorem johnson_denom_pos_iff (ρ η : ℝ) {n : ℝ} (hn : 0 < n) :
    0 < ((ρ + η) * n) ^ 2 - n * (ρ * n) ↔ ρ < (ρ + η) ^ 2 := by
  rw [johnson_denom_eq]
  have hn2 : 0 < n ^ 2 := by positivity
  constructor
  · intro h; nlinarith [h, hn2]
  · intro h; have : 0 < (ρ + η) ^ 2 - ρ := by linarith
    positivity

/-- **`(ρ+η)² > ρ ↔ η > η₀`.** The second-moment applicability condition is exactly the large-gap
condition `η > √ρ − ρ` (for `0 < ρ`, with `ρ + η ≥ 0`). -/
theorem sq_gt_iff_large_gap {ρ η : ℝ} (hρ0 : 0 < ρ) (hsum : 0 ≤ ρ + η) :
    ρ < (ρ + η) ^ 2 ↔ Real.sqrt ρ - ρ < η := by
  have hsqrt_nonneg : 0 ≤ Real.sqrt ρ := Real.sqrt_nonneg ρ
  have hs : Real.sqrt ρ ^ 2 = ρ := Real.sq_sqrt (le_of_lt hρ0)
  constructor
  · intro h
    -- `ρ < (ρ+η)²` and both `√ρ, ρ+η ≥ 0` ⇒ `√ρ < ρ+η`
    have hlt : Real.sqrt ρ < ρ + η := by
      nlinarith [h, hs, hsqrt_nonneg, hsum]
    linarith
  · intro h
    have hlt : Real.sqrt ρ < ρ + η := by linarith
    nlinarith [hlt, hs, hsqrt_nonneg, hsum]

/-- **The second-moment method yields no bound in the small-gap band.** For `0 < ρ < 1`, `n > 0`,
and a small gap `η < η₀ = √ρ − ρ` with `ρ + η ≥ 0`, the Johnson denominator is `≤ 0`, so
`johnson_list_bound`/`_div` give no list-size bound: the band is beyond the second-moment toolkit. -/
theorem second_moment_fails_in_band
    {ρ η n : ℝ} (hρ0 : 0 < ρ) (hn : 0 < n) (hsum : 0 ≤ ρ + η)
    (hsmall : η < Real.sqrt ρ - ρ) :
    ((ρ + η) * n) ^ 2 - n * (ρ * n) ≤ 0 := by
  by_contra h
  replace h : 0 < ((ρ + η) * n) ^ 2 - n * (ρ * n) := not_le.mp h
  have hsq : ρ < (ρ + η) ^ 2 := (johnson_denom_pos_iff ρ η hn).mp h
  have hgap : Real.sqrt ρ - ρ < η := (sq_gt_iff_large_gap hρ0 hsum).mp hsq
  linarith

end ArkLib.ProximityGap.BridgeLoop16
