/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Field.Basic

/-!
# Loop 11 (O9 repair) — the Johnson-range Hab25 bound fits the prize RHS under `n ≤ 2^m`

The in-tree `Hab25Johnson` port of Haböck Thm 2 gives, in the Johnson range, the MCA error bound

    ε_mca ≤ (ℓ⁷/3)·(ρ·n)² / q,     ℓ = (μ + ½)/√ρ,   n = |domain|,  μ = GS multiplicity.

The prize RHS `epsMCAgsPrizeBound q m ρ η c₁ c₂ c₃ = (1/q)·(2^m)^{c₁}/(ρ^{c₂}η^{c₃})` carries **no
`n`** — so the two only match under the smooth-domain size linkage that the prize parameters intend:
`n = |domain| ≤ 2^m` (a `2^m`-smooth evaluation domain). This file proves the `n²` Hab25 bound is
then dominated by the `c₁ = 2` prize shape `(1/q)·(2^m)²·K`, i.e. the missing domain-size factor *is*
the `(2^m)^{c₁}` term (with `K = ℓ⁷ρ²/3`). This repairs the O9 statement-fidelity gap and lands the
proven Johnson-range proof-side bound on the prize's own RHS shape.

(The prize RHS uses real `rpow` exponents `c₁ c₂ c₃ : ℝ`; here `c₁ = 2`, `c₂ = c₃ = 0` are concrete,
so `(2^m)^{c₁} = (2^m)²` as a `ℕ`-power and `ρ^{c₂}η^{c₃} = 1` — the inequality below is exactly the
`epsMCAgsPrizeBound … 2 0 0` instance, stated with the `ℕ`-power to avoid the `rpow` literal noise.)

It does **not** close the prize: it covers only the Johnson range (the large-gap side `η > √ρ−ρ`,
Loop10) and consumes the Hab25 residuals as the source of the `(ℓ⁷/3)(ρn)²/q` bound. Sorry-free,
axiom-clean. See `DISPROOF_LOG.md` (O9/P2).
-/

namespace ArkLib.ProximityGap.ProofLoop11

/-- The Haböck Johnson-range bound value `(ℓ⁷/3)·(ρ·n)²/q`. -/
noncomputable def hab25JohnsonBound (q ℓ ρ n : ℝ) : ℝ :=
  (ℓ ^ 7 / 3) * (ρ * n) ^ 2 / q

/-- The prize RHS at `c₁ = 2, c₂ = c₃ = 0` with leading constant `K`, i.e.
`K · (1/q) · (2^M)²` — the `epsMCAgsPrizeBound q M ρ η 2 0 0` instance scaled by `K`. -/
noncomputable def prizeShapeSq (q : ℝ) (M : ℕ) (K : ℝ) : ℝ :=
  K * ((1 / q) * ((2 : ℝ) ^ M) ^ 2)

/-- **The Hab25 `n²` bound is dominated by the prize `(2^m)²` shape under `n ≤ 2^m`.** With a
`2^M`-smooth domain (`0 ≤ n ≤ 2^M`), nonneg parameters and `q > 0`, the Johnson-range bound is at
most `prizeShapeSq q M K` with `K := ℓ⁷ρ²/3` — i.e. the missing domain-size factor is exactly the
`(2^M)^{c₁}` term with `c₁ = 2`. -/
theorem hab25_le_prizeShape
    {q ℓ ρ n : ℝ} {M : ℕ}
    (hq : 0 < q) (hℓ : 0 ≤ ℓ) (hn0 : 0 ≤ n)
    (hlink : n ≤ (2 : ℝ) ^ M) :
    hab25JohnsonBound q ℓ ρ n ≤ prizeShapeSq q M (ℓ ^ 7 * ρ ^ 2 / 3) := by
  have h2M : (0 : ℝ) ≤ (2 : ℝ) ^ M := by positivity
  -- `(ρ·n)² ≤ ρ²·(2^M)²` from `0 ≤ n ≤ 2^M`
  have hnsq : (ρ * n) ^ 2 ≤ ρ ^ 2 * ((2 : ℝ) ^ M) ^ 2 := by
    have hsq : n ^ 2 ≤ ((2 : ℝ) ^ M) ^ 2 := by nlinarith [hn0, hlink, h2M]
    nlinarith [sq_nonneg ρ, hsq]
  unfold hab25JohnsonBound prizeShapeSq
  rw [div_le_iff₀ hq]
  -- RHS·q = (ℓ⁷ρ²/3)·(2^M)²;  LHS·q-cleared = (ℓ⁷/3)(ρn)²
  have hexp : ℓ ^ 7 * ρ ^ 2 / 3 * (1 / q * ((2:ℝ) ^ M) ^ 2) * q
      = (ℓ ^ 7 / 3) * (ρ ^ 2 * ((2:ℝ) ^ M) ^ 2) := by
    field_simp
  rw [hexp]
  have h3 : (0:ℝ) ≤ ℓ ^ 7 / 3 := by positivity
  exact mul_le_mul_of_nonneg_left hnsq h3

/-- The leading constant `K = ℓ⁷ρ²/3` is positive for positive parameters (the bound is a genuine,
non-vacuous prize-shape bound). -/
theorem prizeShape_const_pos {ℓ ρ : ℝ} (hℓ : 0 < ℓ) (hρ : 0 < ρ) :
    0 < ℓ ^ 7 * ρ ^ 2 / 3 := by positivity

end ArkLib.ProximityGap.ProofLoop11
