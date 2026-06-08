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
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.LinearCombination

/-!
# Per-codeword line-agreement count (#232, MCA→Johnson building block)

A genuinely novel elementary brick toward the open MCA→Johnson regime. The hard part of
bounding the MCA error over the affine line `{u₀ + γ·u₁}` is *bivariate*; but the
**per-codeword** sub-count is a clean pigeonhole on the line's per-coordinate solution map.

  `line_agree_count_mul_le` — for words `u₀, u₁, c`, the number of scalars `γ` at
  which the line point `u₀ + γ·u₁` agrees with `c` on at least `a` coordinates,
  times `(a − b₀)`, is at most the Hamming weight of `u₁`, where
  `b₀ = #{i : u₁ i = 0 ∧ u₀ i = c i}` is the always-agree count.

Reason: at a coordinate `i` with `u₁ i ≠ 0`, the equation `u₀ i + γ·u₁ i = c i`
has the *unique* solution `γ = (c i − u₀ i)/u₁ i`, so agreement with `c` at index
`i` (for `u₁ i ≠ 0`) pins `γ`. Thus
`agree(γ) = b₀ + #{i : u₁ i ≠ 0, γ = γ_i}`, and summing the second term over all
`γ` counts each support coordinate once (`= weight(u₁)`). Each high-agreement `γ`
contributes `≥ a − b₀`, giving the bound by double counting.

This is the codeword-local half of the BCIKS20 correlated-agreement argument; the remaining
(open/research-scale) part is bounding the *number of codewords* that any line point can be close to
beyond the Johnson radius. Axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*.
  2026. #232.
- [BCIKS20] Proximity gaps for Reed–Solomon codes.
-/

namespace ProximityGap

open Finset

variable {ι F : Type*} [Fintype ι] [Field F] [DecidableEq F]

/-- **Finite-set per-codeword line-agreement count.** If every scalar in a finite
set `G` makes the line point `u₀ + γ·u₁` agree with `c` on at least `a`
coordinates, then `|G| · (a - b₀) ≤ weight(u₁)`, where
`b₀ = #{i : u₁ i = 0 ∧ u₀ i = c i}` is the always-agree count. -/
theorem line_agree_finset_mul_le (G : Finset F) (u₀ u₁ c : ι → F) (a : ℕ)
    (hG : ∀ γ ∈ G, a ≤ (univ.filter (fun i => u₀ i + γ * u₁ i = c i)).card) :
    G.card * (a - (univ.filter (fun i => u₁ i = 0 ∧ u₀ i = c i)).card)
      ≤ (univ.filter (fun i => u₁ i ≠ 0)).card := by
  classical
  set B : Finset ι := univ.filter (fun i => u₁ i = 0 ∧ u₀ i = c i) with hB
  set W : Finset ι := univ.filter (fun i => u₁ i ≠ 0) with hW
  set g : ι → F := fun i => (c i - u₀ i) * (u₁ i)⁻¹ with hg
  set fiber : F → Finset ι := fun γ => W.filter (fun i => g i = γ) with hfiber
  have hY :
      ∀ (γ : F) (i : ι), u₁ i ≠ 0 →
        ((u₀ i + γ * u₁ i = c i) ↔ g i = γ) := by
    intro γ i hi
    simp only [hg]
    rw [← div_eq_mul_inv, div_eq_iff hi]
    constructor
    · intro h; linear_combination -h
    · intro h; linear_combination -h
  have hagree : ∀ γ : F, (univ.filter (fun i => u₀ i + γ * u₁ i = c i)).card
      = B.card + (fiber γ).card := by
    intro γ
    have hX :
        (univ.filter (fun i => u₀ i + γ * u₁ i = c i)).filter
          (fun i => u₁ i = 0) = B := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hB]
      constructor
      · rintro ⟨hp, h0⟩; rw [h0, mul_zero, add_zero] at hp; exact ⟨h0, hp⟩
      · rintro ⟨h0, he⟩; refine ⟨?_, h0⟩; rw [h0, mul_zero, add_zero]; exact he
    have hYset : (univ.filter (fun i => u₀ i + γ * u₁ i = c i)).filter (fun i => ¬ u₁ i = 0)
        = fiber γ := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hW, hfiber]
      constructor
      · rintro ⟨hp, h0⟩; exact ⟨h0, (hY γ i h0).mp hp⟩
      · rintro ⟨h0, hgi⟩; exact ⟨(hY γ i h0).mpr hgi, h0⟩
    rw [← Finset.card_filter_add_card_filter_not
      (s := univ.filter (fun i => u₀ i + γ * u₁ i = c i))
      (p := fun i => u₁ i = 0), hX, hYset]
  have hdisj : (G : Set F).Pairwise (fun γ γ' => Disjoint (fiber γ) (fiber γ')) := by
    intro γ hγ γ' hγ' hne
    rw [Finset.disjoint_left]
    intro i hi hi'
    simp only [hfiber, Finset.mem_filter] at hi hi'
    exact hne (hi.2.symm.trans hi'.2)
  have hsum_le : (∑ γ ∈ G, (fiber γ).card) ≤ W.card := by
    have hsum : (G.biUnion fiber).card = ∑ γ ∈ G, (fiber γ).card :=
      Finset.card_biUnion (fun x hx y hy h => hdisj hx hy h)
    have hsub : G.biUnion fiber ⊆ W := by
      intro i hi
      rw [Finset.mem_biUnion] at hi
      obtain ⟨γ, _hγ, hiγ⟩ := hi
      rw [hfiber] at hiγ
      exact (Finset.mem_filter.mp hiγ).1
    rw [← hsum]
    exact Finset.card_le_card hsub
  have hmult_ge : ∀ γ ∈ G, a - B.card ≤ (fiber γ).card := by
    intro γ hγ
    have hle := hG γ hγ
    rw [hagree γ] at hle
    omega
  calc
    G.card * (a - B.card)
        = ∑ _γ ∈ G, (a - B.card) := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ γ ∈ G, (fiber γ).card := Finset.sum_le_sum hmult_ge
    _ ≤ W.card := hsum_le

/-- **Per-codeword line-agreement count.** The scalars `γ` whose line point
`u₀ + γ·u₁` agrees with `c` on `≥ a` coordinates are few: their count times
`(a − b₀)` is at most `weight(u₁)`, where
`b₀ = #{i : u₁ i = 0 ∧ u₀ i = c i}`. A single fixed codeword can be hit with high
agreement by only `≤ weight(u₁)/(a − b₀)` scalars on the line. -/
theorem line_agree_count_mul_le [Fintype F] (u₀ u₁ c : ι → F) (a : ℕ) :
    (univ.filter
        (fun γ : F =>
          a ≤ (univ.filter (fun i => u₀ i + γ * u₁ i = c i)).card)).card
        * (a - (univ.filter (fun i => u₁ i = 0 ∧ u₀ i = c i)).card)
      ≤ (univ.filter (fun i => u₁ i ≠ 0)).card := by
  classical
  set bad : Finset F :=
    univ.filter
      (fun γ : F =>
        a ≤ (univ.filter (fun i => u₀ i + γ * u₁ i = c i)).card) with hbad
  refine line_agree_finset_mul_le bad u₀ u₁ c a ?_
  intro γ hγ
  rw [hbad, Finset.mem_filter] at hγ
  exact hγ.2

#print axioms line_agree_finset_mul_le
#print axioms line_agree_count_mul_le

/-- **Assembly brick: line bad-γ count ≤ sum over witness codewords.** If every
"bad" scalar `γ` (line agrees with some codeword on `≥ a` coordinates) has its
witness codeword in a finite list `L`, then the number of bad scalars is at most
the sum, over `c ∈ L`, of the per-codeword line-agreement counts. Combined with
`line_agree_count_mul_le`, this reduces the MCA→Johnson bad-γ bound to bounding
the *witness-codeword count* `|L|` — the remaining research-scale ingredient. -/
theorem badGamma_card_le_sum [Fintype F] (u₀ u₁ : ι → F) (a : ℕ) (L : Finset (ι → F))
    (bad : Finset F)
    (hwit :
      ∀ γ ∈ bad, ∃ c ∈ L, a ≤ (univ.filter (fun i => u₀ i + γ * u₁ i = c i)).card) :
    bad.card ≤ ∑ c ∈ L,
      (univ.filter
        (fun γ : F => a ≤ (univ.filter (fun i => u₀ i + γ * u₁ i = c i)).card)).card := by
  classical
  refine le_trans (Finset.card_le_card ?_) Finset.card_biUnion_le
  intro γ hγ
  obtain ⟨c, hcL, hc⟩ := hwit γ hγ
  rw [Finset.mem_biUnion]
  exact ⟨c, hcL, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hc⟩

#print axioms badGamma_card_le_sum

/-- **Quantitative assembly.** Suppose every bad scalar has some witness codeword in
`L`, and every witness codeword has at most `b` always-agree coordinates
`{i : u₁ i = 0 ∧ u₀ i = c i}`. Then the bad-scalar count times the usable
agreement gap `(a - b)` is bounded by the list size times the support of `u₁`.

This is the first packaged inequality in the MCA→Johnson direction: the remaining
research-scale input is to control the witness-codeword list `L`, while this lemma
turns such a control into a bad-γ count. -/
theorem badGamma_mul_gap_le_list_mul_weight
    (u₀ u₁ : ι → F) (a b : ℕ) (L : Finset (ι → F)) (bad : Finset F)
    (hwit :
      ∀ γ ∈ bad, ∃ c ∈ L, a ≤ (univ.filter (fun i => u₀ i + γ * u₁ i = c i)).card)
    (hbase :
      ∀ c ∈ L, (univ.filter (fun i => u₁ i = 0 ∧ u₀ i = c i)).card ≤ b) :
    bad.card * (a - b) ≤ L.card * (univ.filter (fun i => u₁ i ≠ 0)).card := by
  classical
  let witness : F → ι → F := fun γ =>
    if hγ : γ ∈ bad then (hwit γ hγ).choose else 0
  let weight : ℕ := (univ.filter (fun i => u₁ i ≠ 0)).card
  have hwL : ∀ γ ∈ bad, witness γ ∈ L := by
    intro γ hγ
    simp only [witness, dif_pos hγ]
    exact (hwit γ hγ).choose_spec.1
  have hwhigh :
      ∀ γ ∈ bad,
        a ≤ (univ.filter (fun i => u₀ i + γ * u₁ i = witness γ i)).card := by
    intro γ hγ
    simp only [witness, dif_pos hγ]
    exact (hwit γ hγ).choose_spec.2
  have hpart :
      bad.card = ∑ c ∈ L, (bad.filter (fun γ => witness γ = c)).card :=
    Finset.card_eq_sum_card_fiberwise hwL
  have hper : ∀ c ∈ L, (bad.filter (fun γ => witness γ = c)).card * (a - b) ≤ weight := by
    intro c hc
    set G := bad.filter (fun γ => witness γ = c) with hG
    have hGhigh :
        ∀ γ ∈ G, a ≤ (univ.filter (fun i => u₀ i + γ * u₁ i = c i)).card := by
      intro γ hγ
      rw [hG] at hγ
      have hγbad : γ ∈ bad := (Finset.mem_filter.mp hγ).1
      have hγwit : witness γ = c := (Finset.mem_filter.mp hγ).2
      simpa [hγwit] using hwhigh γ hγbad
    have hline := line_agree_finset_mul_le G u₀ u₁ c a hGhigh
    have hgap :
        a - b ≤ a - (univ.filter (fun i => u₁ i = 0 ∧ u₀ i = c i)).card := by
      have hb := hbase c hc
      omega
    exact le_trans (Nat.mul_le_mul_left G.card hgap) (by simpa [hG, weight] using hline)
  calc
    bad.card * (a - b)
        = (∑ c ∈ L, (bad.filter (fun γ => witness γ = c)).card) * (a - b) := by
          rw [hpart]
    _ = ∑ c ∈ L, (bad.filter (fun γ => witness γ = c)).card * (a - b) := by
          rw [mul_comm, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro c hc
          rw [mul_comm]
    _ ≤ ∑ _c ∈ L, weight := Finset.sum_le_sum hper
    _ = L.card * weight := by rw [Finset.sum_const, smul_eq_mul]

/-- Full-support specialization of `badGamma_mul_gap_le_list_mul_weight`. If `u₁`
has no zero coordinates, the always-agree baseline is zero for every codeword, so
`bad.card * a` is bounded by the witness-list size times the support of `u₁`. -/
theorem badGamma_mul_le_list_mul_weight_of_fullSupport
    (u₀ u₁ : ι → F) (a : ℕ) (L : Finset (ι → F)) (bad : Finset F)
    (hwit :
      ∀ γ ∈ bad, ∃ c ∈ L, a ≤ (univ.filter (fun i => u₀ i + γ * u₁ i = c i)).card)
    (hsupp : ∀ i, u₁ i ≠ 0) :
    bad.card * a ≤ L.card * (univ.filter (fun i => u₁ i ≠ 0)).card := by
  classical
  have hbase :
      ∀ c ∈ L, (univ.filter (fun i => u₁ i = 0 ∧ u₀ i = c i)).card ≤ 0 := by
    intro c _hc
    have hempty : univ.filter (fun i => u₁ i = 0 ∧ u₀ i = c i) = ∅ :=
      Finset.filter_eq_empty_iff.mpr fun i _ hi => hsupp i hi.1
    rw [hempty, Finset.card_empty]
  simpa using badGamma_mul_gap_le_list_mul_weight u₀ u₁ a 0 L bad hwit hbase

#print axioms badGamma_mul_gap_le_list_mul_weight
#print axioms badGamma_mul_le_list_mul_weight_of_fullSupport

end ProximityGap
