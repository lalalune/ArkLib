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

/-! ## Concrete four-rate certificate over `|F| = |ι| = 8`

We instantiate the abstract `hvol_next` family at the smallest field/block-length pair that
both admits an injective Reed-Solomon evaluation domain (`|ι| ≤ |F|`) and gives four *distinct*
prize-rate floor indices.  Over `q = n = 8` the prize rates `{1/2, 1/4, 1/8, 1/16}` floor to
`k = [4, 2, 1, 0]` and the adjacent Elias indices are `j = k + 1 = [5, 3, 2, 1]`.
-/

section Concrete

variable {F ι : Type} [Field F] [Fintype F] [DecidableEq F]
  [Fintype ι] [Nonempty ι] [DecidableEq ι]

omit [Nonempty ι] [DecidableEq ι] in
/-- The four prize-rate degrees at block length `8` are `⌊prizeRates r · 8⌋ = [4, 2, 1, 0]`. -/
lemma prizeRate_floor_card8 (hn : Fintype.card ι = 8) (r : Fin 4) :
    ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ = [4, 2, 1, 0].get r := by
  rw [hn]
  fin_cases r <;>
    · simp only [prizeRates, List.get]
      rw [show ((8 : ℕ) : ℝ≥0) = 8 by norm_num]
      norm_num [Nat.floor_eq_iff]

/-- `finrank` of the rate-`r` Reed-Solomon code at block length `8` equals its degree
`⌊prizeRates r · 8⌋`, since every prize degree is `≤ 8 = |ι|`. -/
lemma finrank_rs_prizeRate_card8 (domain : ι ↪ F) (hn : Fintype.card ι = 8) (r : Fin 4) :
    Module.finrank F
        (ReedSolomon.code domain ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊)
      = ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ := by
  have hle : ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ ≤ Fintype.card ι := by
    rw [prizeRate_floor_card8 (ι := ι) hn r, hn]; fin_cases r <;> simp [List.get]
  have := ReedSolomon.dim_eq_deg_of_le' (α := domain) hle
  rwa [show Module.finrank F (ReedSolomon.code domain
      ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊)
      = LinearCode.dim (ReedSolomon.code domain
        ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊) from rfl]

/-- **The concrete four-rate `hvol_next` Elias-volume certificates.**

For any Reed-Solomon evaluation domain with `|F| = |ι| = 8`, the adjacent Elias-volume lower
bound clears the prize budget `ε* · |F|` at every prize rate.  This is exactly the `hvol_next`
family consumed by the four-rate exact resolvers
(`listPrizeLatticeResolved_of_Lambda_le_and_elias_next`,
`listPrizeLatticeResolved_of_johnson_sq_and_elias_next`, etc.); the four inequalities are
discharged by `norm_num` evaluating the genuine `hammingBallVolume` definition. -/
theorem fourRate_hvol_next_card8 (domain : ι ↪ F)
    (hF : Fintype.card F = 8) (hn : Fintype.card ι = 8) :
    ∀ r : Fin 4,
      (epsStar : ℝ≥0∞) * (Fintype.card F : ℝ≥0∞) <
        ENNReal.ofReal
          ((CodingTheory.hammingBallVolume (Fintype.card F)
              (((((⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ : ℕ) + 1 : ℕ) : ℝ≥0) /
                    (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ)
              (Fintype.card ι) : ℝ)
            / (Fintype.card F : ℝ) ^
                ((Fintype.card ι : ℝ) -
                  Module.finrank F
                    (ReedSolomon.code domain
                      ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊))) := by
  intro r
  have hfin := finrank_rs_prizeRate_card8 (ι := ι) domain hn r
  have hk := prizeRate_floor_card8 (ι := ι) hn r
  -- rewrite finrank to the concrete degree, then apply the reduction lemma
  rw [hfin]
  refine eliasVolumeUpperCore_of_lt
    (j := (⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ : ℕ) + 1) (ε_star := epsStar)
    (den := (Fintype.card F : ℝ) ^
        ((Fintype.card ι : ℝ) - (⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ : ℝ))) ?_ ?_
  · -- the certificate denominator uses exponent `n - k`, matching the rewritten finrank
    push_cast
    ring_nf
  · -- the real-side numeric inequality, per rate, evaluating `hammingBallVolume`
    rw [hF, hn, epsStar_real_eq, hk]
    fin_cases r <;>
      · simp only [List.get]
        rw [CodingTheory.hammingBallVolume]
        norm_num [Nat.floor_eq_iff, Finset.sum_range_succ, Nat.choose]

end Concrete

end ProximityGap
