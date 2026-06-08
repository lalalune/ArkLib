/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.LinearCombination

/-!
# Per-codeword line-agreement count (#232, MCA→Johnson building block)

A genuinely novel elementary brick toward the open MCA→Johnson regime. The hard part of bounding the
MCA error over the affine line `{u₀ + γ·u₁}` is *bivariate*; but the **per-codeword** sub-count is a
clean pigeonhole on the line's per-coordinate solution map.

  `line_agree_count_mul_le` — for words `u₀, u₁, c`, the number of scalars `γ` at which the line
  point `u₀ + γ·u₁` agrees with `c` on at least `a` coordinates, times `(a − b₀)`, is at most the
  Hamming weight of `u₁`, where `b₀ = #{i : u₁ i = 0 ∧ u₀ i = c i}` is the always-agree count.

Reason: at a coordinate `i` with `u₁ i ≠ 0`, the equation `u₀ i + γ·u₁ i = c i` has the *unique*
solution `γ = (c i − u₀ i)/u₁ i`, so agreement with `c` at index `i` (for `u₁ i ≠ 0`) pins `γ`. Thus
`agree(γ) = b₀ + #{i : u₁ i ≠ 0, γ = γ_i}`, and summing the second term over all `γ` counts each
support coordinate once (`= weight(u₁)`). Each high-agreement `γ` contributes `≥ a − b₀`, giving the
bound by double counting.

This is the codeword-local half of the BCIKS20 correlated-agreement argument; the remaining
(open/research-scale) part is bounding the *number of codewords* that any line point can be close to
beyond the Johnson radius. Axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #232.
- [BCIKS20] Proximity gaps for Reed–Solomon codes.
-/

namespace ProximityGap

open Finset

variable {ι F : Type*} [Fintype ι] [DecidableEq ι] [Field F] [DecidableEq F]

set_option linter.unusedSectionVars false in
/-- **Per-codeword line-agreement count.** The scalars `γ` whose line point `u₀ + γ·u₁` agrees with
`c` on `≥ a` coordinates are few: their count times `(a − b₀)` is at most `weight(u₁)`, where
`b₀ = #{i : u₁ i = 0 ∧ u₀ i = c i}`. (A single fixed codeword can be hit with high agreement by only
`≤ weight(u₁)/(a − b₀)` scalars on the line.) -/
theorem line_agree_count_mul_le [Fintype F] (u₀ u₁ c : ι → F) (a : ℕ) :
    (univ.filter (fun γ : F => a ≤ (univ.filter (fun i => u₀ i + γ * u₁ i = c i)).card)).card
        * (a - (univ.filter (fun i => u₁ i = 0 ∧ u₀ i = c i)).card)
      ≤ (univ.filter (fun i => u₁ i ≠ 0)).card := by
  classical
  set B : Finset ι := univ.filter (fun i => u₁ i = 0 ∧ u₀ i = c i) with hB
  set W : Finset ι := univ.filter (fun i => u₁ i ≠ 0) with hW
  set g : ι → F := fun i => (c i - u₀ i) * (u₁ i)⁻¹ with hg
  set bad : Finset F :=
    univ.filter (fun γ : F => a ≤ (univ.filter (fun i => u₀ i + γ * u₁ i = c i)).card) with hbad
  -- coordinate-level equivalence on the support `W`
  have hY : ∀ (γ : F) (i : ι), u₁ i ≠ 0 → ((u₀ i + γ * u₁ i = c i) ↔ g i = γ) := by
    intro γ i hi
    simp only [hg]
    rw [← div_eq_mul_inv, div_eq_iff hi]
    constructor
    · intro h; linear_combination -h
    · intro h; linear_combination -h
  -- agreement at `γ` splits as `b₀` (always-agree) plus the support coords whose unique root is `γ`
  have hagree : ∀ γ : F, (univ.filter (fun i => u₀ i + γ * u₁ i = c i)).card
      = B.card + (W.filter (fun i => g i = γ)).card := by
    intro γ
    have hX : (univ.filter (fun i => u₀ i + γ * u₁ i = c i)).filter (fun i => u₁ i = 0) = B := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hB]
      constructor
      · rintro ⟨hp, h0⟩; rw [h0, mul_zero, add_zero] at hp; exact ⟨h0, hp⟩
      · rintro ⟨h0, he⟩; refine ⟨?_, h0⟩; rw [h0, mul_zero, add_zero]; exact he
    have hYset : (univ.filter (fun i => u₀ i + γ * u₁ i = c i)).filter (fun i => ¬ u₁ i = 0)
        = W.filter (fun i => g i = γ) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hW]
      constructor
      · rintro ⟨hp, h0⟩; exact ⟨h0, (hY γ i h0).mp hp⟩
      · rintro ⟨h0, hgi⟩; exact ⟨(hY γ i h0).mpr hgi, h0⟩
    rw [← Finset.filter_card_add_filter_neg_card_eq_card
      (s := univ.filter (fun i => u₀ i + γ * u₁ i = c i)) (p := fun i => u₁ i = 0), hX, hYset]
  -- fiberwise count of the support over the root map equals `weight(u₁)`
  have hsum : ∑ γ : F, (W.filter (fun i => g i = γ)).card = W.card := by
    rw [← Finset.card_eq_sum_card_fiberwise (fun i _ => Finset.mem_univ (g i))]
  -- each `bad` scalar has support-multiplicity `≥ a - b₀`
  have hmult_ge : ∀ γ ∈ bad, a - B.card ≤ (W.filter (fun i => g i = γ)).card := by
    intro γ hγ
    simp only [hbad, Finset.mem_filter, Finset.mem_univ, true_and] at hγ
    have := hagree γ
    omega
  calc bad.card * (a - B.card)
      = ∑ _γ ∈ bad, (a - B.card) := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ γ ∈ bad, (W.filter (fun i => g i = γ)).card := Finset.sum_le_sum hmult_ge
    _ ≤ ∑ γ : F, (W.filter (fun i => g i = γ)).card :=
        Finset.sum_le_sum_of_subset (Finset.subset_univ bad)
    _ = W.card := hsum

#print axioms line_agree_count_mul_le

end ProximityGap
