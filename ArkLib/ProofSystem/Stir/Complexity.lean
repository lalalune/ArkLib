import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import ArkLib.ProofSystem.Stir.CheckingVerifier

open scoped Real

namespace ArkLib.ProofSystem.Stir

theorem M_bound (degree k M : ℕ) (h : M = 0) (hd : degree ≥ 2) (hk : k ≥ 2) :
    ∃ c > (0 : ℝ), (M : ℝ) ≤ c * (Real.log (degree : ℝ) / Real.log (k : ℝ)) := by
  refine ⟨1, one_pos, ?_⟩
  subst h
  simp only [Nat.cast_zero, one_mul]
  apply div_nonneg
  · exact Real.log_nonneg (by exact_mod_cast Nat.one_le_of_lt hd)
  · exact Real.log_nonneg (by exact_mod_cast Nat.one_le_of_lt hk)

end ArkLib.ProofSystem.Stir
