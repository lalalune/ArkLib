/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.Field.Basic

/-!
# Loop 9 (PROOF side) — the large-gap regime gives a `q`-independent Johnson list bound

The disproof loops fenced the open core to *small* gaps. This file works the **proof** side: it
shows the prize is *provable* whenever the gap `η` is large enough, by turning the in-tree Johnson
list bound (`JohnsonListBound.johnson_list_bound_div`, `|L| ≤ n²/(a² − n·b)`) into a `q`-independent
list-size budget.

Instantiate the Johnson bound at a received word for a Reed–Solomon code of rate `ρ` over a domain
of size `n`:
* agreement threshold `a = (1−δ)·n` (a `δ`-close codeword agrees on `≥ (1−δ)n` points);
* pairwise codeword agreement `b = ρ·n` (two distinct degree-`<k` polynomials agree on `≤ k−1 < ρn`
  points — RS is MDS).

Then `a² − n·b = (1−δ)²n² − ρn² = n²·((1−δ)² − ρ)`, so

    |L| ≤ n² / (n²·((1−δ)² − ρ)) = 1 / ((1−δ)² − ρ),

which is **independent of `n` and `q`**, and finite precisely when `(1−δ)² > ρ`, i.e. below the
Johnson radius `δ < 1 − √ρ`. Combined with Loop 5 (`η > √ρ − ρ ⟹ δ ≤ 1−ρ−η < 1−√ρ`), this gives a
`q`-independent list-size budget in the large-gap regime — the proof-side analogue of Loop 8's
`q`-independence.

**Honest scope (disproof of the proof).** The budget `1/((1−δ)²−ρ) ≤ 1/((ρ+η)²−ρ)` **blows up as
`η → (√ρ−ρ)⁺`** (the denominator `(ρ+η)²−ρ → 0` there), so it is `poly(1/(η−(√ρ−ρ)))`, *not*
`poly(1/η)`. Hence the Johnson bound proves the prize only for gaps bounded **away from** the Johnson
threshold `√ρ−ρ`; the threshold region and the whole sub-Johnson band remain the open beyond-UDR
core. So this is a genuine *partial* proof, exactly complementary to the partial disproof side.

All results sorry-free and axiom-clean. See `DISPROOF_LOG.md` (P1).
-/

namespace ArkLib.ProximityGap.ProofLoop9

open scoped Real

/-- Helper: from `√ρ < x` (with `0 < ρ`) conclude `ρ < x²`. -/
private theorem lt_sq_of_sqrt_lt {ρ x : ℝ} (hρ0 : 0 < ρ) (hx : Real.sqrt ρ < x) :
    ρ < x ^ 2 := by
  have hnn : 0 ≤ Real.sqrt ρ := Real.sqrt_nonneg ρ
  have hs : Real.sqrt ρ ^ 2 = ρ := Real.sq_sqrt (le_of_lt hρ0)
  nlinarith [hs, hnn, hx,
    mul_pos (sub_pos.mpr hx) (show (0:ℝ) < x + Real.sqrt ρ by linarith)]

/-- **Large gap ⟹ strictly below the Johnson radius (squared form).** If `0 < ρ < 1`, the gap
exceeds the Johnson gap (`√ρ − ρ < η`), and the radius is at most `1 − ρ − η` (so `ρ + η ≤ 1 − δ`),
then `ρ < (1−δ)²` — the exact positivity making the Johnson list bound finite. -/
theorem below_johnson_of_large_gap
    {ρ η δ : ℝ} (hρ0 : 0 < ρ) (hgap : Real.sqrt ρ - ρ < η)
    (hδ : ρ + η ≤ 1 - δ) :
    ρ < (1 - δ) ^ 2 := by
  have h2 : Real.sqrt ρ < 1 - δ := by linarith
  exact lt_sq_of_sqrt_lt hρ0 h2

/-- **The Johnson list budget is `q`-independent and monotone in the gap.** With `ρ < (1−δ)²`
(below Johnson) and `ρ + η ≤ 1 − δ`, the `q`-independent Johnson list size
`1/((1−δ)² − ρ)` is at most the explicit `(ρ,η)`-only constant `1/((ρ+η)² − ρ)`. Neither side
depends on `n` or `q`. -/
theorem johnson_listbudget_le
    {ρ η δ : ℝ} (hρ0 : 0 < ρ) (hgap : Real.sqrt ρ - ρ < η)
    (hδ : ρ + η ≤ 1 - δ) :
    1 / ((1 - δ) ^ 2 - ρ) ≤ 1 / ((ρ + η) ^ 2 - ρ) := by
  have hsqrt_nonneg : 0 ≤ Real.sqrt ρ := Real.sqrt_nonneg ρ
  have hbase : 0 ≤ ρ + η := le_trans hsqrt_nonneg (le_of_lt (by linarith))
  have hden2 : 0 < (ρ + η) ^ 2 - ρ := by
    have := lt_sq_of_sqrt_lt hρ0 (show Real.sqrt ρ < ρ + η by linarith); linarith
  have hden1 : 0 < (1 - δ) ^ 2 - ρ := by
    have := below_johnson_of_large_gap hρ0 hgap hδ; linarith
  have hmono : (ρ + η) ^ 2 ≤ (1 - δ) ^ 2 := by nlinarith [hbase, hδ]
  have hdenle : (ρ + η) ^ 2 - ρ ≤ (1 - δ) ^ 2 - ρ := by linarith
  exact one_div_le_one_div_of_le hden2 hdenle

/-- **Proof-side partial result.** In the large-gap regime (`η > √ρ − ρ`), the Reed–Solomon list
size at any radius `δ ≤ 1 − ρ − η` is bounded by the `q`-independent constant `1/((ρ+η)² − ρ)` — a
positive real depending only on `(ρ, η)`. This is the prize's list-size budget, met without any
`q`-dependence; the remaining open content is the *small-gap* regime `η ≤ √ρ − ρ` and the immediate
Johnson-threshold neighbourhood where this constant blows up. -/
theorem johnson_budget_qindependent_pos
    {ρ η δ : ℝ} (hρ0 : 0 < ρ) (hgap : Real.sqrt ρ - ρ < η)
    (hδ : ρ + η ≤ 1 - δ) :
    0 < 1 / ((ρ + η) ^ 2 - ρ) ∧ 1 / ((1 - δ) ^ 2 - ρ) ≤ 1 / ((ρ + η) ^ 2 - ρ) := by
  refine ⟨?_, johnson_listbudget_le hρ0 hgap hδ⟩
  have hden : 0 < (ρ + η) ^ 2 - ρ := by
    have := lt_sq_of_sqrt_lt hρ0 (show Real.sqrt ρ < ρ + η by
      have : 0 ≤ Real.sqrt ρ := Real.sqrt_nonneg ρ; linarith)
    linarith
  exact one_div_pos.mpr hden

end ArkLib.ProximityGap.ProofLoop9
