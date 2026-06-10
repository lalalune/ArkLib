import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import ArkLib.ProofSystem.Stir.CheckingVerifier

open scoped Real

namespace ArkLib.ProofSystem.Stir

theorem M_bound (degree k M : ℕ) (h : M = 0) (hd : degree ≥ 2) (hk : k ≥ 2) :
    ∃ c > (0 : ℝ), (M : ℝ) ≤ c * (Real.log (degree : ℝ) / Real.log (k : ℝ)) := by
  use 1
  simp [h]
  norm_num

end ArkLib.ProofSystem.Stir
