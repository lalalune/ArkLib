import Mathlib

open Nat

/-- Pure-ℕ collapse of the assembled per-term structured weight bound to the loose
`(2(k+1)+1)·d·D` target.  This is the ℕ engine behind the BCIKS20 Appendix-A P1 per-term WALL
(`βHenselSuccTermStructuredWeightResidual`): given the structured IH, the four factor weights
`W^{i1+δ-1}`, `ξ^{2i1+Σλ-2}`, `B_{i1,λ}`, `∏β^λ` add (sub-additively) to this LHS, and it collapses
to the loose target.  The surviving-partition lower bound `i1 = 0 → 2 ≤ Σλ` is the genuine
`λ ≠ λ(t+1)` exclusion (it makes the `ξ`-coefficient telescope to exactly `2k`). -/
theorem structured_term_collapse (d dH D wW k i1 sl : ℕ)
    (hd : 2 ≤ d) (hdH : 1 ≤ dH) (hdHd : dH ≤ d) (hW : wW + dH ≤ D)
    (hi1 : i1 ≤ k + 1) (hσ : sl ≤ k + 1 - i1)
    (hσ0 : i1 = 0 → 2 ≤ sl) :
    (i1 + (if i1 = 0 then 1 else 0) - 1) * wW
      + (2 * i1 + sl - 2) * ((d - 1) * (D - dH + 1))
      + ((d - sl) * (D + 1 - dH) + (D - sl))
      + (sl + ((k + 1 - i1) + sl) * wW + (2 * (k + 1 - i1) - sl) * ((d - 1) * (D - dH + 1)))
      ≤ (2 * (k + 1) + 1) * d * D := by
  -- Step A: the two ξ-coefficients add to exactly 2*k (key cancellation; needs surviving bound).
  have hXcoef : (2 * i1 + sl - 2) + (2 * (k + 1 - i1) - sl) = 2 * k := by
    rcases Nat.eq_zero_or_pos i1 with h | h
    · subst h; have h2 := hσ0 rfl; omega
    · omega
  -- Step B: the two wW-coefficients add to ≤ k+1+sl.
  have hWcoef : (i1 + (if i1 = 0 then 1 else 0) - 1) + ((k + 1 - i1) + sl) ≤ k + 1 + sl := by
    rcases Nat.eq_zero_or_pos i1 with h | h
    · subst h; simp only [if_pos rfl]; omega
    · rw [if_neg (by omega)]; omega
  -- Abbreviate the ξ-weight atom and the truncated coefficients (so `ring` can regroup).
  set X := (d - 1) * (D - dH + 1) with hX
  set DdH := D + 1 - dH with hDdH
  set eW := i1 + (if i1 = 0 then 1 else 0) - 1 with heW
  set eξ := 2 * i1 + sl - 2 with heξ
  set mσ := 2 * (k + 1 - i1) - sl with hmσ
  set mw := (k + 1 - i1) + sl with hmw
  set dσ := d - sl with hdσ
  set Dσ := D - sl with hDσ
  -- Regroup (all subtraction now hidden inside atoms).
  have hreg :
      eW * wW + eξ * X + (dσ * DdH + Dσ) + (sl + mw * wW + mσ * X)
        = (eW + mw) * wW + (eξ + mσ) * X + (dσ * DdH + Dσ) + sl := by ring
  rw [hreg, hXcoef]
  -- Bound the regrouped coefficients.
  have hb1 : (eW + mw) * wW ≤ (k + 1 + sl) * wW := Nat.mul_le_mul_right _ hWcoef
  have hb2 : dσ * DdH ≤ d * DdH := Nat.mul_le_mul_right _ (Nat.sub_le d sl)
  have hb3 : Dσ ≤ D := Nat.sub_le D sl
  refine le_trans (by
    refine Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hb1 le_rfl)
      (Nat.add_le_add hb2 hb3)) le_rfl) ?_
  -- Now: (k+1+sl)*wW + 2*k*X + (d*DdH + D) + sl ≤ (2(k+1)+1)*d*D.
  -- Unfold atoms and eliminate truncated subtraction with additive witnesses.
  simp only [hX, hDdH]
  have hDdH_ge : dH ≤ D := by omega
  obtain ⟨r, rfl⟩ : ∃ r, D = dH + r := ⟨D - dH, by omega⟩
  obtain ⟨c, rfl⟩ : ∃ c, d = c + 2 := ⟨d - 2, by omega⟩
  have hwWr : wW ≤ r := by omega
  have hσk : sl ≤ k + 1 := by omega
  have hd1 : (c + 2) - 1 = c + 1 := by omega
  have hr1 : (dH + r) - dH + 1 = r + 1 := by omega
  have hrD : (dH + r) + 1 - dH = r + 1 := by omega
  rw [hd1, hr1, hrD]
  nlinarith [hwWr, hσk, Nat.mul_le_mul_right (r + 1) hwWr,
    Nat.mul_le_mul hσk (le_refl (r + 1)),
    Nat.zero_le (k * c), Nat.zero_le (k * r), Nat.zero_le (c * r),
    Nat.zero_le (k * c * r), Nat.zero_le (dH * c), Nat.zero_le (k * dH)]
