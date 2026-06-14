import ArkLib.ProofSystem.Whir.MutualCorrAgreement

/-! # The formalized `mca_capacity_bound_CONJECTURE` is trivially TRUE (not "unprovable").

Docstring claims this up-to-capacity MCA conjecture is "DISPROVEN ... unprovable as written". That
holds for the GENUINE conjecture (a meaningful, sub-1, capacity-tight bound). But the FORMALIZED
statement `∃ c₁ c₂ : ℕ, ∀ f η δ, Pr[…] ≤ ofReal(((parℓ-1)^{c₂}(2^m)^{c₂})/(η^{c₁}ρ^{c₁+c₂}|F|))`
has UNBOUNDED `∃ c₁ c₂` and no `< 1` requirement. With `c₁=0, c₂=|F|` the RHS `≥ 1` (since
`0<ρ≤1` and `((parℓ-1)2^m)^{|F|} ≥ 2^{|F|} ≥ |F|`), so `Pr ≤ 1 ≤ RHS` vacuously.
(Status correction 2026-06-10: this file IS in the build — imported by `ArkLib.lean`.) -/

open scoped NNReal ENNReal
open MutualCorrAgreement ProbabilityTheory ReedSolomon Generator

namespace MCACapacityTrivial

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]

theorem mca_capacity_bound_CONJECTURE_trivially_true
    (α : F) (φ : ι ↪ F) (m : ℕ) [Smooth φ]
    (parℓ_type : Type) [Fintype parℓ_type] (exp : parℓ_type ↪ ℕ)
    (hr0 : 0 < (RSGenerator.genRSC parℓ_type φ m exp).rate)
    (hr1 : (RSGenerator.genRSC parℓ_type φ m exp).rate ≤ 1)
    (hp : 2 ≤ (Fintype.card parℓ_type - 1) * 2 ^ m) :
    mca_capacity_bound_CONJECTURE α φ m parℓ_type exp := by
  classical
  unfold mca_capacity_bound_CONJECTURE
  refine ⟨0, Fintype.card F, ?_⟩
  intro f η _hη δ _hδ
  refine le_trans (PMF.coe_le_one _ _) ?_
  rw [← ENNReal.ofReal_one]
  apply ENNReal.ofReal_le_ofReal
  set cF := Fintype.card F with hcF
  set ρ := (RSGenerator.genRSC parℓ_type φ m exp).rate with hρ
  have hcardF_pos : 0 < (cF : ℝ) := by
    have : 0 < cF := Fintype.card_pos; exact_mod_cast this
  have hcard1 : 1 ≤ Fintype.card parℓ_type := by
    by_contra h; push_neg at h
    interval_cases (Fintype.card parℓ_type) <;> simp_all
  have h2cF : ((cF : ℝ)) ≤ (2 : ℝ) ^ cF := by
    have hlt := Nat.lt_two_pow_self (n := cF)
    calc (cF : ℝ) ≤ ((2 ^ cF : ℕ) : ℝ) := by exact_mod_cast le_of_lt hlt
      _ = (2 : ℝ) ^ cF := by push_cast; ring
  have hbase : (2 : ℝ) ≤ ((Fintype.card parℓ_type : ℝ) - 1) * (2 : ℝ) ^ m := by
    have hnat : (2 : ℝ) ≤ (((Fintype.card parℓ_type - 1) * 2 ^ m : ℕ) : ℝ) := by exact_mod_cast hp
    have hcast : (((Fintype.card parℓ_type - 1) * 2 ^ m : ℕ) : ℝ)
        = ((Fintype.card parℓ_type : ℝ) - 1) * (2 : ℝ) ^ m := by
      push_cast [Nat.cast_sub hcard1]; ring
    rwa [hcast] at hnat
  rw [pow_zero, one_mul, zero_add, le_div_iff₀ (by positivity), one_mul, ← mul_pow]
  calc ρ ^ cF * (cF : ℝ)
      ≤ 1 * (cF : ℝ) := by gcongr; exact pow_le_one₀ (le_of_lt hr0) hr1
    _ = (cF : ℝ) := one_mul _
    _ ≤ (2 : ℝ) ^ cF := h2cF
    _ ≤ (((Fintype.card parℓ_type : ℝ) - 1) * (2 : ℝ) ^ m) ^ cF := by
        gcongr

end MCACapacityTrivial



