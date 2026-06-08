/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The Johnson radius lies below capacity

For a code of relative minimum distance (capacity) `δ_min`, the Johnson list-decoding radius
is `J(δ_min) = 1 - √(1 - δ_min)`.  This file proves the basic relation
`J(δ_min) ≤ δ_min` (ABF26 §2, "Always `J(δ_min) ≤ δ_min`"; #232), so the Grand Challenge
threshold `δ*` genuinely lives in the gap `[J(δ_min), δ_min]`.

* `johnson_le_capacity` — `1 - √(1 - δ) ≤ δ` for `δ ∈ [0,1]`.
* `johnson_rs_le_capacity` — the Reed–Solomon instance `1 - √ρ ≤ 1 - ρ` for `ρ ∈ [0,1]`
  (capacity `δ_min = 1 - ρ`, Johnson `J = 1 - √ρ`).
-/

namespace ArkLib.JohnsonCapacity

open Real

/-- The Johnson radius `J(δ) = 1 - √(1 - δ)` never exceeds the capacity `δ`, for any
`δ ∈ [0,1]`.  Reason: `1 - δ ≤ 1` and `1 - δ ≥ 0` give `(1 - δ)² ≤ 1 - δ`, hence
`1 - δ ≤ √(1 - δ)`, i.e. `1 - √(1 - δ) ≤ δ`. -/
theorem johnson_le_capacity {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1) :
    1 - Real.sqrt (1 - δ) ≤ δ := by
  have hd : (0 : ℝ) ≤ 1 - δ := by linarith
  have hsq : (1 - δ) ^ 2 ≤ 1 - δ := by nlinarith
  have key : (1 - δ) ≤ Real.sqrt (1 - δ) := Real.le_sqrt_of_sq_le hsq
  linarith

/-- Reed–Solomon instance: with capacity `δ_min = 1 - ρ` and Johnson radius `J = 1 - √ρ`,
the Johnson radius lies below capacity, `1 - √ρ ≤ 1 - ρ`, for every rate `ρ ∈ [0,1]`. -/
theorem johnson_rs_le_capacity {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) :
    1 - Real.sqrt ρ ≤ 1 - ρ := by
  have hsq : ρ ^ 2 ≤ ρ := by nlinarith
  have key : ρ ≤ Real.sqrt ρ := Real.le_sqrt_of_sq_le hsq
  linarith

/-- The Johnson radius is nonnegative: `0 ≤ 1 - √(1 - δ)` for `δ ∈ [0,1]` (since
`√(1 - δ) ≤ √1 = 1`). -/
theorem johnson_nonneg {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1) : 0 ≤ 1 - Real.sqrt (1 - δ) := by
  have hle : Real.sqrt (1 - δ) ≤ 1 := by
    calc Real.sqrt (1 - δ) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt (by linarith)
      _ = 1 := Real.sqrt_one
  linarith

/-- The Johnson radius lies *strictly* below capacity on the open interval:
`1 - √(1 - δ) < δ` for `δ ∈ (0,1)`.  Hence the Grand Challenge gap `[J(δ_min), δ_min]` is a
genuine nondegenerate interval whenever `0 < δ_min < 1`. -/
theorem johnson_lt_capacity {δ : ℝ} (h0 : 0 < δ) (h1 : δ < 1) :
    1 - Real.sqrt (1 - δ) < δ := by
  have hd : (0 : ℝ) ≤ 1 - δ := by linarith
  have hsq : (1 - δ) ^ 2 < 1 - δ := by nlinarith
  have key : (1 - δ) < Real.sqrt (1 - δ) := (Real.lt_sqrt hd).mpr hsq
  linarith

end ArkLib.JohnsonCapacity
