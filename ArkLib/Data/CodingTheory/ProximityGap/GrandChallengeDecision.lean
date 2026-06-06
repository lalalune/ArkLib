/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.GrandChallengeCollapse
import ArkLib.Data.CodingTheory.ProximityGap.GrandChallengeRadiusOneExact
import ArkLib.Data.CodingTheory.ProximityGap.MCAEndpointLower
import ArkLib.Data.CodingTheory.ProximityGap.MCAEndpointUpper
import ArkLib.Data.CodingTheory.ProximityGap.SubsetSumRadiusOne

/-!
# Decision of the formalized §1 Grand MCA Prize at both field-size extremes

This file composes the endpoint-collapse equivalence (`GrandChallengeCollapse`:
`mcaPrize domain ↔ ∀ j, ε_mca(RS_j, 1) ≤ 2⁻¹²⁸`), the universal pinning upper bound
(`MCAEndpointUpper`: `ε_mca(MC, δ) ≤ 2ⁿ/q`), and the spike lower bound
(`MCAEndpointLower`: `min(n-k, q)/q ≤ ε_mca(RS, 1)`) into a *decision* of the formal
ABF26 §1 MCA prize predicate outside an explicit middle band of field sizes:

* `mcaPrize_of_huge_field` — for `q ≥ 2^(n+128)` the formal prize predicate **holds**
  (with the vacuous maximal witness `δ* = 1`).
* `not_mcaPrize_of_spike_band` — for `q < 2¹²⁸ · (n - ⌊n/16⌋)` (and `n ≥ 16`) the
  formal prize predicate is **false**: at the rate-`1/16` instance the radius-one MCA
  error already exceeds `2⁻¹²⁸`.
* `epsMCA_one_bracket` — inside the remaining band the radius-one value is bracketed
  by `min(n-k, q)/q` and `2ⁿ/q`; `GrandChallengeRadiusOneExact.epsMCA_one_eq_choose_div`
  pins it exactly (to `C(n, k+1)/q`) once `q > C(C(n,k+1), 2)`, and
  `SubsetSumRadiusOne` raises the floor to `|Σ_{k+1}(L)|/q` unconditionally.

Together with `grandMCAChallenge_iff_choose_le` and `not_listDecodingPrize`, this
completes the resolution of the *formalized* §1 grand-challenge predicates up to the
explicitly-named middle band; the paper's intended *determination* problem (the lattice
threshold of `ε_mca` between the Johnson and capacity radii) lives in the witness /
lattice framework (`GrandChallengesLattice`, `GrandMCAResolution`), not in these
predicates. See `[ABF26]` §1.
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace ProximityGap

open scoped NNReal ENNReal

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **Huge-field decision (positive direction).** For `q ≥ 2^(n+128)` the formal §1 MCA
prize predicate holds: by the endpoint collapse it suffices to bound `ε_mca(·, 1)` at each
prize rate, and the universal pinning bound `2ⁿ/q ≤ 2⁻¹²⁸` does so uniformly. -/
theorem mcaPrize_of_huge_field (domain : ι ↪ F)
    (hq : 2 ^ (Fintype.card ι + 128) ≤ Fintype.card F) :
    GrandChallenges.mcaPrize domain := by
  rw [mcaPrize_iff_forall_epsMCA_one]
  intro j
  exact epsMCA_le_epsStar_of_huge_field
    (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊) 1 hq

/-- **Small-field decision (negative direction).** For `n ≥ 16` and
`q < 2¹²⁸ · (n - ⌊n/16⌋)`, the formal §1 MCA prize predicate is false: at the prize rate
`ρ = 1/16` (index `j = 3`) the spike floor gives `ε_mca(RS, 1) > 2⁻¹²⁸`, contradicting
the radius-one bound forced by the endpoint collapse. -/
theorem not_mcaPrize_of_spike_band (domain : ι ↪ F)
    (hn : 16 ≤ Fintype.card ι)
    (hq : Fintype.card F <
      2 ^ (128 : ℕ) * (Fintype.card ι - ⌊prizeRates 3 * (Fintype.card ι : ℝ≥0)⌋₊)) :
    ¬ GrandChallenges.mcaPrize domain := by
  intro hprize
  set k := ⌊prizeRates 3 * (Fintype.card ι : ℝ≥0)⌋₊ with hk_def
  have hrate : prizeRates 3 = 1 / 16 := by
    unfold prizeRates
    norm_num
  have h16 : (16 : ℝ≥0) ≤ (Fintype.card ι : ℝ≥0) := by exact_mod_cast hn
  -- `k ≥ 1`: `(1/16)·n ≥ 1` for `n ≥ 16`.
  have hk1 : 1 ≤ k := by
    rw [hk_def]
    refine Nat.le_floor ?_
    rw [hrate, Nat.cast_one]
    calc (1 : ℝ≥0) = (1 / 16) * 16 := by norm_num
      _ ≤ (1 / 16) * (Fintype.card ι : ℝ≥0) := by gcongr
  -- `k + 1 ≤ n`: `⌊n/16⌋ + 1 ≤ n/16 + 15n/16 = n` for `n ≥ 16`.
  have hkn : k + 1 ≤ Fintype.card ι := by
    have hkr : (k : ℝ≥0) ≤ (1 / 16) * (Fintype.card ι : ℝ≥0) := by
      rw [hk_def, ← hrate]
      exact Nat.floor_le (zero_le _)
    have hcast : ((k + 1 : ℕ) : ℝ≥0) ≤ (Fintype.card ι : ℝ≥0) := by
      push_cast
      calc (k : ℝ≥0) + 1
          ≤ (1 / 16) * (Fintype.card ι : ℝ≥0) + 1 := by gcongr
        _ ≤ (1 / 16) * (Fintype.card ι : ℝ≥0) + (15 / 16) * (Fintype.card ι : ℝ≥0) := by
            gcongr
            calc (1 : ℝ≥0) ≤ 15 := by norm_num
              _ = (15 / 16) * 16 := by norm_num
              _ ≤ (15 / 16) * (Fintype.card ι : ℝ≥0) := by gcongr
        _ = (Fintype.card ι : ℝ≥0) := by
            rw [← add_mul]
            norm_num
    exact_mod_cast hcast
  have h3 := (mcaPrize_iff_forall_epsMCA_one domain).mp hprize 3
  exact absurd h3
    (not_le.mpr (epsStar_lt_epsMCA_one_of_field_small domain k hk1 hkn hq))

/-- **Two-sided bracket on the radius-one MCA error** — the quantity that, by the endpoint
collapse, *is* the formal Grand MCA Challenge: `min(n-k, q)/q ≤ ε_mca(RS, 1) ≤ 2ⁿ/q`. The
exact value `C(n, k+1)/q` is available for `q > C(C(n,k+1), 2)`
(`epsMCA_one_eq_choose_div`). -/
theorem epsMCA_one_bracket (domain : ι ↪ F) (k : ℕ) (hk : k ≤ Fintype.card ι) :
    ((min (Fintype.card ι - k) (Fintype.card F) : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤
      epsMCA (F := F) (A := F) (ReedSolomon.code domain k : Set (ι → F)) 1 ∧
    epsMCA (F := F) (A := F) (ReedSolomon.code domain k : Set (ι → F)) 1 ≤
      (2 ^ (Fintype.card ι) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) :=
  ⟨epsMCA_one_ge domain k hk, epsMCA_le_two_pow_card_div (ReedSolomon.code domain k) 1⟩

/-- Every prize rate is `≤ 1/2`. -/
private lemma prizeRates_le_half (j : Fin 4) : prizeRates j ≤ 1 / 2 := by
  unfold prizeRates
  have h2 : (2 : ℝ≥0) ^ (1 : ℕ) ≤ 2 ^ (j.val + 1) :=
    pow_le_pow_right₀ one_le_two (by omega)
  rw [pow_one] at h2
  exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) h2

/-- For `n ≥ 2`, every prize-rate degree satisfies `k_j + 1 ≤ n`. -/
private lemma prizeRate_floor_add_one_le (j : Fin 4) (hn : 2 ≤ Fintype.card ι) :
    ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ + 1 ≤ Fintype.card ι := by
  set k := ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ with hk_def
  have h2 : (2 : ℝ≥0) ≤ (Fintype.card ι : ℝ≥0) := by exact_mod_cast hn
  have hkr : (k : ℝ≥0) ≤ (1 / 2) * (Fintype.card ι : ℝ≥0) := by
    rw [hk_def]
    refine le_trans (Nat.floor_le (zero_le _)) ?_
    gcongr
    exact prizeRates_le_half j
  have hcast : ((k + 1 : ℕ) : ℝ≥0) ≤ (Fintype.card ι : ℝ≥0) := by
    push_cast
    calc (k : ℝ≥0) + 1
        ≤ (1 / 2) * (Fintype.card ι : ℝ≥0) + 1 := by gcongr
      _ ≤ (1 / 2) * (Fintype.card ι : ℝ≥0) + (1 / 2) * (Fintype.card ι : ℝ≥0) := by
          gcongr
          calc (1 : ℝ≥0) = (1 / 2) * 2 := by norm_num
            _ ≤ (1 / 2) * (Fintype.card ι : ℝ≥0) := by gcongr
      _ = (Fintype.card ι : ℝ≥0) := by
          rw [← add_mul]
          norm_num
  exact_mod_cast hcast

/-- **Complete decision of the formal §1 MCA prize above the quadratic field threshold.**
Whenever `q > C(C(n, k_j+1), 2)` for each prize rate (so the radius-one value is *exactly*
`C(n, k_j+1)/q` by `epsMCA_one_eq_choose_div`), the formal MCA prize predicate is
equivalent to four explicit numeric inequalities `C(n, k_j+1)/q ≤ 2⁻¹²⁸`. In this regime
the formalized Grand MCA Challenge is therefore *fully decided* by finite arithmetic. -/
theorem mcaPrize_iff_of_quadratic_field (domain : ι ↪ F)
    (hn : 2 ≤ Fintype.card ι)
    (hq : ∀ j : Fin 4,
      (Nat.choose (Fintype.card ι)
        (⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ + 1)).choose 2 < Fintype.card F) :
    GrandChallenges.mcaPrize domain ↔
      ∀ j : Fin 4,
        ((Nat.choose (Fintype.card ι)
            (⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ + 1) : ℕ) : ℝ≥0∞) /
            (Fintype.card F : ℝ≥0∞) ≤ (epsStar : ENNReal) := by
  unfold GrandChallenges.mcaPrize GrandChallenges.grandMCAChallengeRSrate
    GrandChallenges.grandMCAChallengeRS
  exact forall_congr' fun j =>
    grandMCAChallenge_iff_choose_le domain
      (prizeRate_floor_add_one_le j hn) (hq j) epsStar

end ProximityGap
