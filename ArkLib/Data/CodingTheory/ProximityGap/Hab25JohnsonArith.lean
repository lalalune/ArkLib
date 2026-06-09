/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Hab25NumericEdge

/-!
# Hab25 §3 — the closed-form Johnson parameter inequality

The S11 reduction (`Hab25NumericEdge.lean` / `Hab25AffineCapture.lean`) left exactly one
arithmetic input: `L·n/|F| ≤ johnsonBoundReal domain k η δ` for the per-stack list size
`L`. This file discharges it for every `L` up to the paper's list bound `ℓ = (m+½)/√ρ₊`:

* `rhoPlus`, `johnsonM` — mirrors of the `let`-bound quantities of
  `rs_epsMCA_johnson_range_boundReal`, with `johnsonBoundReal_eq` exposing the closed form;
* `rhoPlus_pos`, `rhoPlus_le_two` (for `k ≤ n`), `le_johnsonM` (`3 ≤ m`);
* `johnson_key_arith` — the heart: `3·ρ₊ ≤ 2·(m+½)⁴`, trivially true with room to spare
  (`ρ₊ ≤ 2`, `m ≥ 3` gives `6 ≤ 2·3.5⁴ = 300.125`); hence the list term
  `(m+½)/√ρ₊` is dominated by the main term `2(m+½)⁵/(3ρ₊^{3/2})`;
* `johnson_real_edge` — the capstone: for any `L ≤ (m+½)/√ρ₊`,

    `L·n/|F| ≤ johnsonBoundReal domain k η δ`.

Combined with `johnsonNumericBound_of_per_stack_cover` (or
`johnsonNumericBound_of_affine_capture`), the **only** remaining input to the Johnson MCA
bound is the per-stack capture data itself. Axiom-clean:
`[propext, Classical.choice, Quot.sound]`.
-/

set_option linter.unusedSectionVars false

namespace CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

open CodingTheory
open scoped NNReal ENNReal

variable {ι₀ : Type} [Fintype ι₀] [Nonempty ι₀] [DecidableEq ι₀]
variable {F₀ : Type} [Field F₀] [Fintype F₀] [DecidableEq F₀]

/-- Mirror of the `ρ₊ = k/n + 1/n` quantity of `rs_epsMCA_johnson_range_boundReal`. -/
noncomputable def rhoPlus (_domain : ι₀ ↪ F₀) (k : ℕ) : ℝ :=
  (k : ℝ) / (Fintype.card ι₀ : ℝ) + 1 / (Fintype.card ι₀ : ℝ)

/-- Mirror of the GS multiplicity parameter `m = max ⌈√ρ₊/(2η)⌉ 3` of
`rs_epsMCA_johnson_range_boundReal`. -/
noncomputable def johnsonM (domain : ι₀ ↪ F₀) (k : ℕ) (η : ℝ≥0) : ℝ :=
  max ⌈(rhoPlus domain k ^ ((1 : ℝ) / 2)) / (2 * η)⌉ 3

/-- The closed form of `johnsonBoundReal`, with the `let`-bound quantities named. -/
theorem johnsonBoundReal_eq (domain : ι₀ ↪ F₀) (k : ℕ) (η δ : ℝ≥0) :
    Hab25Johnson.johnsonBoundReal domain k η δ =
      ((2 * (johnsonM domain k η + 1/2) ^ 5 +
          3 * (johnsonM domain k η + 1/2) * (δ : ℝ) * rhoPlus domain k)
        / (3 * rhoPlus domain k ^ ((3 : ℝ) / 2)) * (Fintype.card ι₀ : ℝ)
      + (johnsonM domain k η + 1/2) / rhoPlus domain k ^ ((1 : ℝ) / 2))
      / (Fintype.card F₀ : ℝ) :=
  rfl

theorem rhoPlus_pos (domain : ι₀ ↪ F₀) (k : ℕ) : 0 < rhoPlus domain k := by
  have hn : (0 : ℝ) < (Fintype.card ι₀ : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have h1 : (0 : ℝ) < 1 / (Fintype.card ι₀ : ℝ) := by positivity
  have h2 : (0 : ℝ) ≤ (k : ℝ) / (Fintype.card ι₀ : ℝ) := by positivity
  rw [rhoPlus]
  linarith

theorem rhoPlus_le_two (domain : ι₀ ↪ F₀) {k : ℕ} (hk : k ≤ Fintype.card ι₀) :
    rhoPlus domain k ≤ 2 := by
  have hn : (0 : ℝ) < (Fintype.card ι₀ : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hn1 : (1 : ℝ) ≤ (Fintype.card ι₀ : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hk' : (k : ℝ) ≤ (Fintype.card ι₀ : ℝ) := by exact_mod_cast hk
  have h1 : (k : ℝ) / (Fintype.card ι₀ : ℝ) ≤ 1 := by
    rw [div_le_one hn]; exact hk'
  have h2 : 1 / (Fintype.card ι₀ : ℝ) ≤ 1 := by
    rw [div_le_one hn]; exact hn1
  rw [rhoPlus]
  linarith

theorem le_johnsonM (domain : ι₀ ↪ F₀) (k : ℕ) (η : ℝ≥0) :
    (3 : ℝ) ≤ johnsonM domain k η := by
  have := le_max_right (⌈(rhoPlus domain k ^ ((1 : ℝ) / 2)) / (2 * (η : ℝ))⌉ : ℝ) 3
  simpa [johnsonM] using this

/-- **The key arithmetic**: `3·ρ₊ ≤ 2·(m+½)⁴` — with `ρ₊ ≤ 2` and `m ≥ 3` this is
`6 ≤ 2·(3.5)⁴`, true with two orders of magnitude to spare. -/
theorem johnson_key_arith (domain : ι₀ ↪ F₀) {k : ℕ} (η : ℝ≥0)
    (hk : k ≤ Fintype.card ι₀) :
    3 * rhoPlus domain k ≤ 2 * (johnsonM domain k η + 1/2) ^ 4 := by
  have h2 := rhoPlus_le_two domain hk
  have hm := le_johnsonM domain k η
  nlinarith [sq_nonneg (johnsonM domain k η + 1/2), sq_nonneg (johnsonM domain k η - 3)]

/-- **The closed-form Johnson parameter inequality.** For any per-stack list size `L` up to
the paper's list bound `ℓ = (m+½)/√ρ₊`,

  `L·n/|F| ≤ johnsonBoundReal domain k η δ`.

The list term is dominated by the main term of the closed form (via `johnson_key_arith`),
the cross term is nonnegative, and the trailing `+(m+½)/√ρ₊` absorbs nothing further. This
discharges the `hreal` hypothesis of `johnsonNumericBound_of_per_stack_cover` and
`johnsonNumericBound_of_affine_capture`. -/
theorem johnson_real_edge (domain : ι₀ ↪ F₀) {k : ℕ} (η δ : ℝ≥0) (L : ℕ)
    (hk : k ≤ Fintype.card ι₀)
    (hL : (L : ℝ) ≤ (johnsonM domain k η + 1/2) / rhoPlus domain k ^ ((1 : ℝ) / 2)) :
    ((L * Fintype.card ι₀ : ℕ) : ℝ) / (Fintype.card F₀ : ℝ) ≤
      Hab25Johnson.johnsonBoundReal domain k η δ := by
  have hρ := rhoPlus_pos domain k
  have hm := le_johnsonM domain k η
  have hn : (0 : ℝ) < (Fintype.card ι₀ : ℝ) := by exact_mod_cast Fintype.card_pos
  have hF : (0 : ℝ) < (Fintype.card F₀ : ℝ) := by exact_mod_cast Fintype.card_pos
  set m : ℝ := johnsonM domain k η with hmdef
  set ρ : ℝ := rhoPlus domain k with hρdef
  have hmhalf : (0 : ℝ) < m + 1/2 := by linarith
  -- rpow facts
  have hsqrt_pos : (0 : ℝ) < ρ ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hρ _
  have h32_pos : (0 : ℝ) < ρ ^ ((3 : ℝ) / 2) := Real.rpow_pos_of_pos hρ _
  have hsplit : ρ ^ ((3 : ℝ) / 2) = ρ * ρ ^ ((1 : ℝ) / 2) := by
    rw [← Real.rpow_one_add' hρ.le (by norm_num : (1 : ℝ) + 1/2 ≠ 0)]
    norm_num
  rw [johnsonBoundReal_eq]
  -- reduce to the numerator inequality
  rw [div_le_div_iff_of_pos_right hF]
  · -- `L·n ≤ mainTerm·n + listTerm`
    have hLn : ((L * Fintype.card ι₀ : ℕ) : ℝ) = (L : ℝ) * (Fintype.card ι₀ : ℝ) := by
      push_cast; ring
    rw [hLn, ← hρdef, ← hmdef]
    -- the list bound dominates: `L ≤ (m+½)/√ρ ≤ 2(m+½)⁵/(3ρ^{3/2})`
    have hkey : (m + 1/2) / ρ ^ ((1 : ℝ) / 2) ≤
        2 * (m + 1/2) ^ 5 / (3 * ρ ^ ((3 : ℝ) / 2)) := by
      rw [div_le_div_iff₀ hsqrt_pos (by positivity)]
      -- `(m+½)·3ρ^{3/2} ≤ 2(m+½)⁵·√ρ` ⇔ `3ρ ≤ 2(m+½)⁴`
      rw [hsplit]
      have hka := johnson_key_arith domain (k := k) η hk
      rw [← hρdef, ← hmdef] at hka
      calc (m + 1/2) * (3 * (ρ * ρ ^ ((1 : ℝ) / 2)))
          = ((3 * ρ) * (m + 1/2)) * ρ ^ ((1 : ℝ) / 2) := by ring
        _ ≤ ((2 * (m + 1/2) ^ 4) * (m + 1/2)) * ρ ^ ((1 : ℝ) / 2) := by
            have : (3 * ρ) * (m + 1/2) ≤ (2 * (m + 1/2) ^ 4) * (m + 1/2) :=
              mul_le_mul_of_nonneg_right hka (le_of_lt hmhalf)
            exact mul_le_mul_of_nonneg_right this (le_of_lt hsqrt_pos)
        _ = 2 * (m + 1/2) ^ 5 * ρ ^ ((1 : ℝ) / 2) := by ring
    have hmain : (L : ℝ) * (Fintype.card ι₀ : ℝ) ≤
        2 * (m + 1/2) ^ 5 / (3 * ρ ^ ((3 : ℝ) / 2)) * (Fintype.card ι₀ : ℝ) := by
      refine mul_le_mul_of_nonneg_right (le_trans hL hkey) (le_of_lt hn)
    have hcross : (0 : ℝ) ≤ 3 * (m + 1/2) * (δ : ℝ) * ρ := by positivity
    have hlist : (0 : ℝ) ≤ (m + 1/2) / ρ ^ ((1 : ℝ) / 2) := by positivity
    have hexpand : 2 * (m + 1/2) ^ 5 / (3 * ρ ^ ((3 : ℝ) / 2)) * (Fintype.card ι₀ : ℝ) ≤
        (2 * (m + 1/2) ^ 5 + 3 * (m + 1/2) * (δ : ℝ) * ρ)
          / (3 * ρ ^ ((3 : ℝ) / 2)) * (Fintype.card ι₀ : ℝ) := by
      refine mul_le_mul_of_nonneg_right ?_ (le_of_lt hn)
      refine div_le_div_of_nonneg_right ?_ (by positivity) |>.trans_eq rfl
      · linarith
    calc (L : ℝ) * (Fintype.card ι₀ : ℝ)
        ≤ 2 * (m + 1/2) ^ 5 / (3 * ρ ^ ((3 : ℝ) / 2)) * (Fintype.card ι₀ : ℝ) := hmain
      _ ≤ (2 * (m + 1/2) ^ 5 + 3 * (m + 1/2) * (δ : ℝ) * ρ)
            / (3 * ρ ^ ((3 : ℝ) / 2)) * (Fintype.card ι₀ : ℝ) := hexpand
      _ ≤ (2 * (m + 1/2) ^ 5 + 3 * (m + 1/2) * (δ : ℝ) * ρ)
            / (3 * ρ ^ ((3 : ℝ) / 2)) * (Fintype.card ι₀ : ℝ)
          + (m + 1/2) / ρ ^ ((1 : ℝ) / 2) := le_add_of_nonneg_right hlist

end CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

/-! ## Axiom audit — all kernel-clean. -/
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.johnsonBoundReal_eq
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.johnson_key_arith
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.johnson_real_edge
