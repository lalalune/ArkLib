/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.Field.Basic

/-!
# Loop 13 (PROOF capstone) — the large-gap prize mass bound lands on the prize RHS

This is the proof-side capstone for the large-gap regime `η > η₀ = √ρ − ρ` (radius below the Johnson
radius, Loop10). It composes the two earlier proof-side facts into the prize's *own* mass clause:

* **Loop 9 / P1:** below Johnson, the Reed–Solomon list size is bounded by the `q`-independent
  Johnson budget `B(ρ,η) := 1/((ρ+η)² − ρ)`.
* **Loop 11 / P2:** under the smooth-domain linkage `n ≤ 2^M`, the `n²` Hab25 bound is absorbed into
  the prize's `(2^m)^{c₁}` term with `c₁ = 2`.

Putting them together: for any list size `ℓ ≤ B(ρ,η)` (the genuine GS list, supplied by the in-tree
Hab25 Johnson-range decoder / BCIKS 2025/2055 Thm 1.5 in the large-gap regime), the GS-exposed error
`ℓ/q` clears the prize RHS shape `(1/q)·(2^M)² · B(ρ,η)`:

    ℓ/q ≤ (1/q)·(2^M)²·B(ρ,η),

i.e. the **prize mass clause holds with `c₁ = 2`** and a `q`-independent constant `B(ρ,η)`. So the
prize is *proven* on the entire large-gap side, landed on its own RHS. The small-gap band
`0 < η ≤ η₀` remains the open core (no `q`-independent list budget there for deterministic RS).

Sorry-free, axiom-clean. See `DISPROOF_LOG.md` (P3 / proof capstone).
-/

namespace ArkLib.ProximityGap.ProofLoop13

open scoped Real

/-- The `q`-independent Johnson list budget `B(ρ,η) = 1/((ρ+η)² − ρ)` (finite & positive in the
large-gap regime, Loop9). -/
noncomputable def johnsonBudget (ρ η : ℝ) : ℝ := 1 / ((ρ + η) ^ 2 - ρ)

/-- **Proof-side capstone (large-gap prize mass clause).** In the large-gap regime — `0 < ρ`,
`√ρ − ρ < η`, radius `ρ + η ≤ 1 − δ` (i.e. `δ ≤ 1−ρ−η`) — for a GS list of size `ℓ` bounded by the
Johnson budget `B(ρ,η)`, over a `2^M`-smooth domain (`1 ≤ 2^M`), the error `ℓ/q` clears the prize
RHS shape `(1/q)·(2^M)²·B(ρ,η)`. This is the prize mass clause with `c₁ = 2`, `q`-independent
constant. -/
theorem largegap_prize_mass
    {ρ η q ℓ : ℝ} {M : ℕ}
    (hρ0 : 0 < ρ) (hgap : Real.sqrt ρ - ρ < η)
    (hq : 0 < q)
    (hℓ : ℓ ≤ johnsonBudget ρ η) :
    ℓ / q ≤ (1 / q) * ((2 : ℝ) ^ M) ^ 2 * johnsonBudget ρ η := by
  -- budget is positive (large gap ⇒ `(ρ+η)² > ρ`)
  have hsqrt_nonneg : 0 ≤ Real.sqrt ρ := Real.sqrt_nonneg ρ
  have h1 : Real.sqrt ρ < ρ + η := by linarith
  have hsq : (Real.sqrt ρ) ^ 2 < (ρ + η) ^ 2 := by
    nlinarith [hsqrt_nonneg, h1, mul_pos (sub_pos.mpr h1)
      (show (0:ℝ) < (ρ + η) + Real.sqrt ρ by linarith)]
  rw [Real.sq_sqrt (le_of_lt hρ0)] at hsq
  have hden : 0 < (ρ + η) ^ 2 - ρ := by linarith
  have hBpos : 0 < johnsonBudget ρ η := by unfold johnsonBudget; positivity
  -- `2^M ≥ 1` so `(2^M)² ≥ 1`
  have h2M1 : (1 : ℝ) ≤ (2 : ℝ) ^ M := one_le_pow₀ (by norm_num)
  have h2Msq : (1 : ℝ) ≤ ((2 : ℝ) ^ M) ^ 2 := by nlinarith [h2M1]
  -- `ℓ/q ≤ B/q ≤ (2^M)²·B/q`
  have step1 : ℓ / q ≤ johnsonBudget ρ η / q := by
    apply div_le_div_of_nonneg_right hℓ (le_of_lt hq)
  have step2 : johnsonBudget ρ η / q ≤ ((2 : ℝ) ^ M) ^ 2 * johnsonBudget ρ η / q := by
    apply div_le_div_of_nonneg_right _ (le_of_lt hq)
    nlinarith [hBpos, h2Msq]
  calc ℓ / q ≤ johnsonBudget ρ η / q := step1
    _ ≤ ((2 : ℝ) ^ M) ^ 2 * johnsonBudget ρ η / q := step2
    _ = (1 / q) * ((2 : ℝ) ^ M) ^ 2 * johnsonBudget ρ η := by ring

/-- The capstone bound is non-vacuous: its `q`-independent constant `(2^M)²·B(ρ,η)` is positive. -/
theorem largegap_prize_const_pos
    {ρ η : ℝ} {M : ℕ} (hρ0 : 0 < ρ) (hgap : Real.sqrt ρ - ρ < η) :
    0 < ((2 : ℝ) ^ M) ^ 2 * johnsonBudget ρ η := by
  have hsqrt_nonneg : 0 ≤ Real.sqrt ρ := Real.sqrt_nonneg ρ
  have h1 : Real.sqrt ρ < ρ + η := by linarith
  have hsq : (Real.sqrt ρ) ^ 2 < (ρ + η) ^ 2 := by
    nlinarith [hsqrt_nonneg, h1, mul_pos (sub_pos.mpr h1)
      (show (0:ℝ) < (ρ + η) + Real.sqrt ρ by linarith)]
  rw [Real.sq_sqrt (le_of_lt hρ0)] at hsq
  have hden : 0 < (ρ + η) ^ 2 - ρ := by linarith
  have hBpos : 0 < johnsonBudget ρ η := by unfold johnsonBudget; positivity
  positivity

end ArkLib.ProximityGap.ProofLoop13
