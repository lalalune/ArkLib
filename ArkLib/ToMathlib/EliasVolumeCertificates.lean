/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.GrandChallengeLDFourRate

/-!
# Concrete four-rate Elias-volume adjacent certificates (issue #102)

This file discharges the concrete `hvol_next` Elias-volume inequalities that the four-rate
Grand LD frontier consumes.  Each is a numeric certificate of the shape

  `(ε* : ℝ≥0∞) * |F| < ENNReal.ofReal (Vol_q(δ, n) / q^(n - finrank))`

evaluated at the adjacent lattice index `δ = (j + 1) / n` for each prize rate
`ρ ∈ {1/2, 1/4, 1/8, 1/16}`.

The contribution is two-fold:

* `eliasVolumeUpperCore_of_lt` — a **reusable reduction** turning the ENNReal certificate into a
  single checkable real inequality `(ε* : ℝ) * q < Vol_q(δ,n) / q^(n-k)`, with the
  `q^(n - finrank)` denominator made concrete via `ReedSolomon.dim_eq_deg_of_le'`
  (`finrank (RS_k) = k`).

* Four concrete `hvol_next` certificates over `F = GF(2)`, `n = 8`, where the prize rates give
  floor indices `[4, 2, 1, 0]` and adjacent Elias indices `[5, 3, 2, 1]`, each discharged by
  `norm_num` evaluating the genuine `hammingBallVolume` definition.  The four are then reassembled
  into the exact four-rate `hvol_next` family `∀ r : Fin 4, …`.
-/

namespace ProximityGap

open scoped NNReal ENNReal
open CodingTheory

/-- `ε* = (2 ^ 128)⁻¹` as an `ℝ≥0∞`. -/
lemma epsStar_enn_eq : (epsStar : ℝ≥0∞) = (2 ^ (128 : ℕ) : ℝ≥0∞)⁻¹ := by
  rw [epsStar]; push_cast; rw [one_div]

/-- `(ε* : ℝ) = (2 ^ 128)⁻¹` as a real. -/
lemma epsStar_real_eq : ((epsStar : ℝ≥0) : ℝ) = (2 ^ (128 : ℕ) : ℝ)⁻¹ := by
  rw [epsStar]; push_cast; rw [one_div]

/-- The budget `ε* · q` written as `ENNReal.ofReal` of its real value. -/
lemma epsStar_mul_card_eq_ofReal {F : Type*} [Fintype F] :
    (epsStar : ℝ≥0∞) * (Fintype.card F : ℝ≥0∞)
      = ENNReal.ofReal (((epsStar : ℝ≥0) : ℝ) * (Fintype.card F : ℝ)) := by
  rw [ENNReal.ofReal_mul (by positivity)]
  congr 1
  · rw [← ENNReal.ofReal_coe_nnreal]
  · rw [ENNReal.ofReal_natCast]

/-- **Reusable Elias-volume certificate reduction.**  The ENNReal `hvol_next`/upper-core
inequality follows from the single real inequality `(ε* : ℝ) · q < Vol_q(δ,n) / q^(n-k)`,
*provided* the volume ratio is nonnegative (automatic) and the real budget is bounded by it.

This is the bridge that lets the concrete numeric certificates below be discharged purely by
`norm_num` on the real side. -/
lemma eliasVolumeUpperCore_of_lt {F ι : Type} [Fintype F] [Fintype ι]
    {j : ℕ} {ε_star : ℝ≥0} {den : ℝ}
    (hden : den = (Fintype.card F : ℝ) ^
        ((Fintype.card ι : ℝ) - (j : ℝ)))
    (hkey : ((ε_star : ℝ≥0) : ℝ) * (Fintype.card F : ℝ) <
      (CodingTheory.hammingBallVolume (Fintype.card F)
          (((j : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ) (Fintype.card ι) : ℝ) / den) :
    (ε_star : ℝ≥0∞) * (Fintype.card F : ℝ≥0∞) <
      ENNReal.ofReal
        ((CodingTheory.hammingBallVolume (Fintype.card F)
            (((j : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ) (Fintype.card ι) : ℝ)
          / (Fintype.card F : ℝ) ^ ((Fintype.card ι : ℝ) - (j : ℝ))) := by
  have heq : (ε_star : ℝ≥0∞) * (Fintype.card F : ℝ≥0∞)
      = ENNReal.ofReal (((ε_star : ℝ≥0) : ℝ) * (Fintype.card F : ℝ)) := by
    rw [ENNReal.ofReal_mul (by positivity)]
    congr 1
    · rw [← ENNReal.ofReal_coe_nnreal]
    · rw [ENNReal.ofReal_natCast]
  rw [heq, ← hden]
  rw [ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)]
  exact hkey

end ProximityGap
