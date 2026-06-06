import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.Curves

open ProximityGap Code NNReal Finset Function ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory LinearCode

namespace ScratchBoundary2

-- Existence of a strict δ' < δ with the same floor, when δ·n is NOT an integer.
-- "not an integer" is captured as: ⌊δ·n⌋ < δ·n  (strict, i.e. fractional part > 0).
example (n : ℕ) {δ : ℝ≥0} (hn : 0 < n)
    (hfrac : (Nat.floor (δ * n) : ℝ≥0) < δ * n) :
    ∃ δ' : ℝ≥0, δ' < δ ∧ Nat.floor (δ' * n) = Nat.floor (δ * n) := by
  set j : ℕ := Nat.floor (δ * n) with hj
  have hnne : (n : ℝ≥0) ≠ 0 := by exact_mod_cast hn.ne'
  -- δ > j/n since δ·n > j.
  have hδ_gt : (j : ℝ≥0) / n < δ := by
    rw [div_lt_iff₀ (by positivity)]
    exact hfrac
  -- midpoint between j/n and δ.
  set δ' : ℝ≥0 := ((j : ℝ≥0) / n + δ) / 2 with hδ'
  have hlt1 : (j : ℝ≥0) / n < δ' := by
    rw [hδ', lt_div_iff₀ two_pos, mul_two]; gcongr
  have hlt2 : δ' < δ := by
    rw [hδ', div_lt_iff₀ two_pos, mul_two]; gcongr
  refine ⟨δ', hlt2, ?_⟩
  -- floor(δ'·n) = j.  lower: δ'·n > j ; upper: δ'·n < δ·n < j+1.
  have hlow : (j : ℝ≥0) ≤ δ' * n := by
    rw [← div_le_iff₀ (by positivity : (0:ℝ≥0) < n)] at *
    exact le_of_lt hlt1
  have hδn_lt : δ * n < (j : ℝ≥0) + 1 := by
    exact_mod_cast Nat.lt_floor_add_one (δ * (n : ℝ≥0))
  have hup : δ' * n < (j : ℝ≥0) + 1 := by
    calc δ' * n < δ * n := by exact mul_lt_mul_of_pos_right hlt2 (by positivity)
      _ < (j : ℝ≥0) + 1 := hδn_lt
  have hfloor_le : Nat.floor (δ' * (n : ℝ≥0)) ≤ j := by
    have hup' : δ' * (n : ℝ≥0) < ((j + 1 : ℕ) : ℝ≥0) := by push_cast; exact hup
    have := (Nat.floor_lt (zero_le _)).mpr hup'
    omega
  have hfloor_ge : j ≤ Nat.floor (δ' * (n : ℝ≥0)) := by
    apply (Nat.le_floor_iff (zero_le _)).mpr
    exact hlow
  omega

end ScratchBoundary2
