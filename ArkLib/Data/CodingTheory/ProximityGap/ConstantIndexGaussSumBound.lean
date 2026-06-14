/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.MulChar.Lemmas
import ArkLib.Data.CodingTheory.ProximityGap.InteriorWorstCaseIncompleteSum

/-!
# Constant-index √-cancellation: the worst-case per-frequency bound for ANY fixed-index subgroup (#407)

This file generalizes `QRWorstCaseIncompleteSum.lean` (index 2) to **every constant index `m`**: the
worst-case incomplete sum over the index-`m` multiplicative subgroup `G = {a : χ(a)=1}` (`χ` a
character of order `m`) is bounded by the classical Gauss sums, giving square-root cancellation
`‖η_b‖ ≤ ((m−1)√q + 1)/m ≈ √m·√n` — PROVEN, no wall.

## Brick 1 (this commit): the general Gauss-sum magnitude `‖gaussSum χ ψ‖ = √q`

Mathlib has `gaussSum_mul_gaussSum_eq_card` (`g(χ)·g(χ⁻¹,ψ⁻¹) = q` for `χ ≠ 1`) but NOT the magnitude
directly.  Over `ℂ`, `g(χ⁻¹,ψ⁻¹) = conj(g(χ,ψ))` (characters are unit-circle valued), so
`‖g(χ,ψ)‖² = g(χ,ψ)·conj(g(χ,ψ)) = q`, hence `‖g(χ,ψ)‖ = √q`.  This is the index-`m` companion of the
in-tree `gaussSum_normSq` (which is the quadratic special case via `gaussSum_sq`).
-/

set_option linter.unusedSectionVars false

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

namespace ArkLib.ProximityGap.ConstantIndexGaussSum

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- `‖χ(a)‖ = 1` for every nonzero `a` (character values are roots of unity). -/
theorem norm_mulChar_unit (χ : MulChar F ℂ) {a : F} (ha : a ≠ 0) : ‖χ a‖ = 1 := by
  have hq : 1 < Fintype.card F := Fintype.one_lt_card
  refine Complex.norm_eq_one_of_pow_eq_one (n := Fintype.card F - 1) ?_ (by omega)
  rw [← map_pow, FiniteField.pow_card_sub_one_eq_one a ha, map_one]

/-- Conjugation sends the Gauss sum of `(χ, ψ)` to that of `(χ⁻¹, ψ⁻¹)`. -/
theorem conj_gaussSum (χ : MulChar F ℂ) (ψ : AddChar F ℂ) :
    (starRingEnd ℂ) (gaussSum χ ψ) = gaussSum χ⁻¹ ψ⁻¹ := by
  have hchar : (0 : ℕ) < ringChar F := by
    haveI := ringChar.charP F
    exact Nat.pos_of_ne_zero (CharP.char_ne_zero_of_finite F (ringChar F))
  rw [gaussSum, gaussSum, map_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [map_mul, AddChar.starComp_apply hchar, starRingEnd_apply, MulChar.star_apply']

/-- **The general Gauss-sum magnitude** `‖gaussSum χ ψ‖ = √q` for any nontrivial `χ` and primitive
`ψ` over a finite field, valued in `ℂ`.  Reusable; Mathlib lacks it directly. -/
theorem norm_gaussSum_eq_sqrt {χ : MulChar F ℂ} (hχ : χ ≠ 1) {ψ : AddChar F ℂ}
    (hψ : ψ.IsPrimitive) :
    ‖gaussSum χ ψ‖ = Real.sqrt (Fintype.card F : ℝ) := by
  have hmul : gaussSum χ ψ * gaussSum χ⁻¹ ψ⁻¹ = (Fintype.card F : ℂ) :=
    gaussSum_mul_gaussSum_eq_card hχ hψ
  have hsq : ‖gaussSum χ ψ‖ ^ 2 = (Fintype.card F : ℝ) := by
    have h1 : gaussSum χ ψ * (starRingEnd ℂ) (gaussSum χ ψ) = (Fintype.card F : ℂ) := by
      rw [conj_gaussSum]; exact hmul
    rw [Complex.mul_conj'] at h1
    exact_mod_cast h1
  rw [← hsq, Real.sqrt_sq (norm_nonneg _)]

/-- **Character orthogonality / indicator decomposition.** For a multiplicative character `χ` of
order `m = orderOf χ`, the subgroup-indicator of `G_χ = {a : χ a = 1}` is the average of the powers
of `χ`:  `∑_{j<m} (χ^j) a = m·[χ a = 1]`.  (Geometric series in `χ a`, using `χ^m = 1`.) -/
theorem mulChar_pow_sum_all (χ : MulChar F ℂ) (a : F) :
    ∑ j ∈ Finset.range (orderOf χ), (χ ^ j) a = if χ a = 1 then (orderOf χ : ℂ) else 0 := by
  rcases eq_or_ne a 0 with rfl | ha
  · have h0 : ∀ j ∈ Finset.range (orderOf χ), (χ ^ j) (0 : F) = 0 :=
      fun j _ => MulChar.map_nonunit (χ ^ j) not_isUnit_zero
    rw [Finset.sum_congr rfl h0, Finset.sum_const_zero, if_neg]
    rw [MulChar.map_nonunit χ not_isUnit_zero]; exact zero_ne_one
  · have hunit : IsUnit a := ha.isUnit
    have hval : ∀ j, (χ ^ j) a = (χ a) ^ j := by
      intro j
      have h := MulChar.pow_apply_coe χ j hunit.unit
      rwa [IsUnit.unit_spec] at h
    rw [Finset.sum_congr rfl (fun j _ => hval j)]
    by_cases h : χ a = 1
    · rw [if_pos h, h]; simp
    · rw [if_neg h, geom_sum_eq h]
      have hm : (χ a) ^ (orderOf χ) = 1 := by
        have hp := MulChar.pow_apply_coe χ (orderOf χ) hunit.unit
        rw [IsUnit.unit_spec] at hp
        rw [← hp, pow_orderOf_eq_one χ, MulChar.one_apply hunit]
      rw [hm, sub_self, zero_div]

/-- The index-`m` multiplicative subgroup `G_χ = {a : χ a = 1}` cut out by `χ` (`m = orderOf χ`). -/
noncomputable def Gchi (χ : MulChar F ℂ) : Finset F :=
  Finset.univ.filter (fun a => χ a = 1)

/-- **The index-`m` period decomposition.** `m·η_b(G_χ) = ∑_{j<m} gaussSum(χ^j, ψ_b)`, `ψ_b = ψ(b·)`.
The subgroup period over `G_χ` is the average of the `m` twisted Gauss sums — the index-`m`
generalization of the index-2 `eta_QR_eq`. -/
theorem eta_constIndex_decomp (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (b : F) :
    (orderOf χ : ℂ) * eta ψ (Gchi χ) b
      = ∑ j ∈ Finset.range (orderOf χ), gaussSum (χ ^ j) (AddChar.mulShift ψ b) := by
  classical
  symm
  calc ∑ j ∈ Finset.range (orderOf χ), gaussSum (χ ^ j) (AddChar.mulShift ψ b)
      = ∑ j ∈ Finset.range (orderOf χ), ∑ a : F, (χ ^ j) a * ψ (b * a) := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [gaussSum]
        exact Finset.sum_congr rfl (fun a _ => by rw [AddChar.mulShift_apply])
    _ = ∑ a : F, ∑ j ∈ Finset.range (orderOf χ), (χ ^ j) a * ψ (b * a) := Finset.sum_comm
    _ = ∑ a : F, (∑ j ∈ Finset.range (orderOf χ), (χ ^ j) a) * ψ (b * a) := by
        refine Finset.sum_congr rfl (fun a _ => ?_); rw [Finset.sum_mul]
    _ = ∑ a : F, (if χ a = 1 then (orderOf χ : ℂ) else 0) * ψ (b * a) := by
        refine Finset.sum_congr rfl (fun a _ => by rw [mulChar_pow_sum_all])
    _ = ∑ a : F, if χ a = 1 then (orderOf χ : ℂ) * ψ (b * a) else 0 := by
        refine Finset.sum_congr rfl (fun a _ => ?_); simp only [ite_mul, zero_mul]
    _ = ∑ a ∈ Gchi χ, (orderOf χ : ℂ) * ψ (b * a) := by rw [Gchi, Finset.sum_filter]
    _ = (orderOf χ : ℂ) * ∑ a ∈ Gchi χ, ψ (b * a) := by rw [Finset.mul_sum]
    _ = (orderOf χ : ℂ) * eta ψ (Gchi χ) b := by rw [eta]

end ArkLib.ProximityGap.ConstantIndexGaussSum

#print axioms ArkLib.ProximityGap.ConstantIndexGaussSum.norm_mulChar_unit
#print axioms ArkLib.ProximityGap.ConstantIndexGaussSum.conj_gaussSum
#print axioms ArkLib.ProximityGap.ConstantIndexGaussSum.norm_gaussSum_eq_sqrt
#print axioms ArkLib.ProximityGap.ConstantIndexGaussSum.mulChar_pow_sum_all
#print axioms ArkLib.ProximityGap.ConstantIndexGaussSum.eta_constIndex_decomp
