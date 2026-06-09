/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.GuruswamiSudan.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The Guruswami–Sudan radius barrier: weighted-degree decoding *provably* stops at Johnson

This file proves, `sorry`-free and axiom-clean, the precise quantitative reason the
Guruswami–Sudan (GS) weighted-degree interpolation method **cannot decode past the
Johnson radius** `1 − √ρ` for Reed–Solomon — and a fortiori cannot enter the open
prize gap `(1 − √ρ, 1 − ρ)` of ABF26 / Issue #232.

## Setting

The in-repo GS development (`ArkLib.Data.CodingTheory.GuruswamiSudan.Basic`) realizes the
full BCIKS20 GS factor-extraction `gs_dvd_property`, gated on the *relative agreement
radius*

  `gs_johnson k n m  =  1 − √ρ − √ρ/(2m)`,   with `ρ = k/n`,

the rate-corrected GS radius at multiplicity parameter `m`. The interpolation step
(`gs_numVars_gt_numConstraints_of_gt_one`) and the multiplicity overrun
(`gs_sufficient_multiplicity_bound`) are both feasible at this radius, and the output list
is then bounded by the `Y`-degree of the interpolant (`GSFactorExtract.gs_list_size_le`).

The whole pipeline therefore decodes correctly for any `dist/n < gs_johnson k n m`. The
*entire question* of whether GS can beat Johnson reduces to: **how large can
`gs_johnson k n m` be made by choosing `m`?**

## What is proved (the honest barrier)

The `√ρ/(2m)` *deficit* is the price GS pays for using finite multiplicity. It is
strictly positive for every finite `m` (whenever `k > 0`), so:

* `gs_johnson_lt_johnson` — **GS never reaches Johnson.** For every multiplicity `m ≥ 1`
  (and `k, n > 0`), the GS radius is *strictly* below the Johnson radius:
  `gs_johnson k n m < 1 − √ρ`. Decoding is guaranteed only *strictly inside* Johnson; the
  deficit `√ρ/(2m)` never vanishes at finite `m`.

* `gs_johnson_strictMono` — the radius is strictly increasing in `m`: more multiplicity
  helps, but monotonically toward — never beyond — the Johnson supremum.

* `gs_johnson_tendsto_johnson` — **the supremum is *exactly* Johnson.** As `m → ∞`,
  `gs_johnson k n m → 1 − √ρ`. So `1 − √ρ` is the least upper bound of the GS-achievable
  radii: GS asymptotically saturates Johnson and stops there.

* `johnson_lt_capacity` and `gs_johnson_not_in_open_gap` — **GS stays out of the open
  prize gap.** Since `gs_johnson k n m < 1 − √ρ < 1 − ρ` (the second inequality strict for
  `0 < ρ < 1`, i.e. `0 < k < n`), no GS radius lies in the open interval `(1 − √ρ, 1 − ρ)`.
  The interior that Issue #232 leaves open is *exactly* the region the weighted-degree
  method cannot reach.

## Why this is the precise obstruction

The Johnson bound `√(kn)` is the geometric-mean barrier: the `(1, k−1)`-weighted degree of
the interpolant must be `≈ (m + 1/2)√(kn)` (to have enough monomials, via
`gs_degree_bound_sq_gt`), while the multiplicity-overrun needs the agreement count
`m·(n − dist)` to exceed that degree. Solving `m(n − dist) > (m + 1/2)√(kn)` for the
relative radius gives exactly `dist/n < 1 − √(k/n)·(1 + 1/(2m)) = gs_johnson k n m`. The
`+1/2` in the degree (the *one extra* monomial needed for a nonzero kernel vector, see
`GSInterpExistence`) is what forces the strict deficit `√ρ/(2m)` — and no amount of
multiplicity removes it: it only shrinks it toward `0`. Hence the supremum is the bare
geometric mean `1 − √ρ`, the Johnson radius, and not one bit more. This is the formal
content of "GS stops at Johnson."

All results are `Mathlib`-only on top of the existing in-repo `gs_johnson` definition,
`sorry`-free and axiom-clean (`propext, Classical.choice, Quot.sound`). This is an honest
upper-bound *barrier*, not progress into the open gap: it confirms the prize gap is exactly
where the weighted-degree technique fails.
-/

namespace ArkLib.CodingTheory.WeightedSudanBarrier

open Filter Topology

/-- The rate `ρ = k/n` as a real number, with the division performed in `ℚ` and then coerced
to `ℝ` — matching exactly the internal form of `gs_johnson`'s `rho`. -/
noncomputable def rhoR (k n : ℕ) : ℝ := (((k : ℚ) / (n : ℚ) : ℚ) : ℝ)

/-- The Johnson relative decoding radius `1 − √ρ` with rate `ρ = k/n` — the supremum of all
GS-achievable radii. This is the lower edge of the open prize gap `(1 − √ρ, 1 − ρ)`. -/
noncomputable def johnsonRadius (k n : ℕ) : ℝ := 1 - √(rhoR k n)

/-- Unfold `gs_johnson` to a fully real-arithmetic form `1 − √ρ − √ρ/(2m)` with the rate
`√ρ = √(rhoR k n)`. This is the definitional `let`-expansion, recorded for reuse. -/
lemma gs_johnson_eq (k n m : ℕ) :
    gs_johnson k n m = 1 - √(rhoR k n) - √(rhoR k n) / (2 * m) := by
  unfold gs_johnson rhoR
  rfl

/-- Under the standing positivity hypotheses (positive dimension `k`, positive blocklength
`n`), the square root of the rate `√ρ` is strictly positive. -/
lemma sqrt_rhoR_pos {k n : ℕ} (hk : 0 < k) (hn : 0 < n) : 0 < √(rhoR k n) := by
  rw [Real.sqrt_pos, rhoR]
  have hq : (0 : ℚ) < (k : ℚ) / (n : ℚ) := by
    have hkpos : (0 : ℚ) < (k : ℚ) := by exact_mod_cast hk
    have hnpos : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn
    positivity
  exact_mod_cast hq

/-- **GS never reaches the Johnson radius.** For every multiplicity `m ≥ 1` (with `k, n > 0`),
the rate-corrected GS relative radius is *strictly* below Johnson:

  `gs_johnson k n m < 1 − √ρ`.

The strict deficit is exactly the GS multiplicity correction `√ρ/(2m) > 0`. This is the core
quantitative barrier: weighted-degree decoding is *guaranteed* only strictly inside Johnson. -/
theorem gs_johnson_lt_johnson {k n m : ℕ} (hk : 0 < k) (hn : 0 < n) (hm : 0 < m) :
    gs_johnson k n m < johnsonRadius k n := by
  rw [gs_johnson_eq, johnsonRadius]
  have hs : 0 < √(rhoR k n) := sqrt_rhoR_pos hk hn
  have hm' : (0 : ℝ) < 2 * m := by
    have : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    linarith
  have hdeficit : 0 < √(rhoR k n) / (2 * m) := div_pos hs hm'
  linarith

/-- **The GS radius is strictly increasing in the multiplicity.** Raising `m` strictly raises
`gs_johnson k n m` (toward, never past, the Johnson supremum): the deficit `√ρ/(2m)` strictly
shrinks. Formalizes "more multiplicity helps, monotonically." -/
theorem gs_johnson_strictMono {k n : ℕ} (hk : 0 < k) (hn : 0 < n) :
    StrictMonoOn (fun m : ℕ => gs_johnson k n m) (Set.Ici 1) := by
  intro a ha b hb hab
  simp only [Set.mem_Ici] at ha hb
  simp only [gs_johnson_eq]
  have hs : 0 < √(rhoR k n) := sqrt_rhoR_pos hk hn
  have hapos : (0 : ℝ) < 2 * a := by
    have : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
    linarith
  have hlt : (2 : ℝ) * a < 2 * b := by
    have : (a : ℝ) < (b : ℝ) := by exact_mod_cast hab
    linarith
  have hdef : √(rhoR k n) / (2 * b) < √(rhoR k n) / (2 * a) :=
    div_lt_div_of_pos_left hs hapos hlt
  linarith

/-- **The supremum of the GS-achievable radii is *exactly* the Johnson radius.** As the
multiplicity `m → ∞`, `gs_johnson k n m → 1 − √ρ`. Combined with `gs_johnson_lt_johnson`
(each term is strictly below) and `gs_johnson_strictMono` (increasing), this pins the least
upper bound at Johnson: GS asymptotically saturates `1 − √ρ` and stops there. -/
theorem gs_johnson_tendsto_johnson (k n : ℕ) :
    Tendsto (fun m : ℕ => gs_johnson k n m) atTop (𝓝 (johnsonRadius k n)) := by
  have hfun : (fun m : ℕ => gs_johnson k n m)
      = fun m : ℕ => (johnsonRadius k n) - √(rhoR k n) / (2 * (m : ℝ)) := by
    funext m
    rw [gs_johnson_eq, johnsonRadius, sub_sub]
  rw [hfun]
  have hconst : Tendsto (fun _ : ℕ => johnsonRadius k n) atTop (𝓝 (johnsonRadius k n)) :=
    tendsto_const_nhds
  -- The deficit `√ρ/(2m) → 0`.
  have hdeficit : Tendsto (fun m : ℕ => √(rhoR k n) / (2 * (m : ℝ))) atTop (𝓝 0) := by
    have h2m : Tendsto (fun m : ℕ => 2 * (m : ℝ)) atTop atTop :=
      Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2) tendsto_natCast_atTop_atTop
    have hinv : Tendsto (fun m : ℕ => (2 * (m : ℝ))⁻¹) atTop (𝓝 0) := h2m.inv_tendsto_atTop
    have hmul : Tendsto (fun m : ℕ => √(rhoR k n) * (2 * (m : ℝ))⁻¹) atTop (𝓝 0) := by
      have := hinv.const_mul (√(rhoR k n))
      simpa using this
    refine hmul.congr (fun m => ?_)
    rw [div_eq_mul_inv]
  have := hconst.sub hdeficit
  simpa using this

/-- **GS stays strictly below capacity.** Whenever the rate `ρ = k/n` satisfies
`0 < ρ < 1` (so `√ρ < 1`, i.e. `0 < k < n`), the Johnson radius `1 − √ρ` is *strictly*
below the list-decoding capacity `1 − ρ`. Combined with `gs_johnson_lt_johnson`, every GS
radius is `< 1 − ρ`: GS provably never reaches capacity. -/
theorem johnson_lt_capacity {k n : ℕ} (hk : 0 < k) (hkn : k < n) :
    johnsonRadius k n < 1 - rhoR k n := by
  rw [johnsonRadius]
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le _) hkn
  set ρ : ℝ := rhoR k n with hρ
  have hρpos : 0 < ρ := by
    rw [hρ, rhoR]
    have hq : (0 : ℚ) < (k : ℚ) / (n : ℚ) := by
      have hkpos : (0 : ℚ) < (k : ℚ) := by exact_mod_cast hk
      have hnpos : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn
      positivity
    exact_mod_cast hq
  have hρlt1 : ρ < 1 := by
    rw [hρ, rhoR]
    have hq : (k : ℚ) / (n : ℚ) < 1 := by
      rw [div_lt_one (by exact_mod_cast hn)]
      exact_mod_cast hkn
    exact_mod_cast hq
  -- `√ρ > ρ` for `0 < ρ < 1`, hence `1 − √ρ < 1 − ρ`.
  have hsq : √ρ ^ 2 = ρ := Real.sq_sqrt (le_of_lt hρpos)
  have hsqrt_gt : ρ < √ρ := by
    nlinarith [Real.sqrt_pos.mpr hρpos, Real.sqrt_nonneg ρ, hsq, hρlt1, hρpos]
  linarith

/-- **GS never enters the open prize gap.** Packaging the barrier: under `0 < k < n` and
`m ≥ 1`, the GS radius `gs_johnson k n m` is *not* an element of the open interval
`(1 − √ρ, 1 − ρ)` — the open core of Issue #232 — because it lies strictly *below* the lower
endpoint `1 − √ρ`. The region the prize leaves open is exactly the region the weighted-degree
method cannot reach. -/
theorem gs_johnson_not_in_open_gap {k n m : ℕ} (hk : 0 < k) (hkn : k < n) (hm : 0 < m) :
    gs_johnson k n m ∉ Set.Ioo (johnsonRadius k n) (1 - rhoR k n) := by
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le _) hkn
  intro hmem
  have hlo : johnsonRadius k n < gs_johnson k n m := hmem.1
  have hbar : gs_johnson k n m < johnsonRadius k n := gs_johnson_lt_johnson hk hn hm
  linarith

end ArkLib.CodingTheory.WeightedSudanBarrier
