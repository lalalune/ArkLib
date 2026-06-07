import ArkLib.Data.CodingTheory.Connections.ListDecodingAndCA

namespace CodingTheory

theorem johnson_lift_two_mul_toNNReal_le_scratch
    (δ η : ℝ) (hη_pos : 0 < η) (hη_le_δ : η ≤ δ) (hδ_lt : δ < 1) :
    2 * (((1 - (1 - δ + η) ^ ((1 : ℝ) / 2)).toNNReal : ℝ)) ≤ δ := by
  set x : ℝ := δ - η with hx
  have hx0 : 0 ≤ x := by
    rw [hx]
    linarith
  have hx1 : x ≤ 1 := by
    rw [hx]
    linarith
  have hmain : 2 * (1 - Real.sqrt (1 - x)) ≤ x := by
    have hlin_nonneg : 0 ≤ 1 - x / 2 := by linarith
    have hsq_le : (1 - x / 2) ^ 2 ≤ 1 - x := by
      nlinarith [sq_nonneg x]
    have hsqrt_ge : 1 - x / 2 ≤ Real.sqrt (1 - x) :=
      Real.le_sqrt_of_sq_le hsq_le
    nlinarith
  have hrpow : (1 - δ + η) ^ ((1 : ℝ) / 2) = Real.sqrt (1 - x) := by
    rw [show 1 - δ + η = 1 - x by rw [hx]; ring]
    rw [← Real.sqrt_eq_rpow]
  have hnonneg_radius : 0 ≤ 1 - (1 - δ + η) ^ ((1 : ℝ) / 2) := by
    rw [hrpow]
    have hsqrt_le_one : Real.sqrt (1 - x) ≤ 1 := by
      rw [Real.sqrt_le_one]
      linarith
    linarith
  rw [Real.toNNReal_of_nonneg hnonneg_radius]
  simp only [NNReal.coe_mk]
  rw [hrpow]
  nlinarith [hmain, hη_pos]

end CodingTheory
