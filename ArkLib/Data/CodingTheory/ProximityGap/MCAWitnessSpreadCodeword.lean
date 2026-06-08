/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAWitnessSpread

/-!
# Codeword-level witness pinning: the honest list-decoding ⇒ MCA reduction (ABF26 #232)

`MCAEndpointUpper.lean` bounds `ε_mca ≤ 2^n / |F|` by showing the witness **set** map `γ ↦ S_γ`
is injective on bad scalars (each set pins at most one bad `γ`), so the bad-scalar count is at
most the number of subsets `2^n`. `MCAWitnessSpread.lean` records the dual lower-bound
obstruction: distinct bad scalars require distinct witness sets.

This file sharpens the count from the witness *set* level to the witness *codeword* level. The
payoff is the **honest** form of ABF26 direction §2 (list-decoding ⇒ MCA): below `δ = 1/2`, the
MCA bad-scalar count of a full-support line is at most the number of codewords agreeing with some
line point on a size-`≥(1-δ)n` set — i.e. the *line list size*. This is *not* the refuted
black-box double-coverage reduction (`LineDecodingCounting.lean`); it uses a disjointness
pigeonhole that is unconditionally valid for `δ < 1/2`.

## Main results

* `unique_bad_gamma_common_codeword_general` — **codeword pinning (general).** For any line and any
  codeword `w`, if `w` agrees with `u₀ + γ₁·u₁` on `S₁` and with `u₀ + γ₂·u₁` on `S₂` where the
  overlap outruns the zero-set of `u₁` (`|ι| + #{i : u₁ i = 0} < |S₁| + |S₂|`), then `γ₁ = γ₂`.
* `unique_bad_gamma_common_codeword` — the full-support specialization (`#{i : u₁ i = 0} = 0`, so
  the condition is just `|ι| < |S₁| + |S₂|`).
* `overlap_subset_zeros` — two distinct line points sharing a codeword overlap only inside the
  zero-set of `u₁`.
* `fiber_card_packing` — **all-stacks** count: one codeword witnesses at most `(n-z)/(t-z)` bad
  scalars (`z = #{u₁ = 0}`), via a disjoint packing of the cleaned witness sets.
* `card_sum_gt_of_lt_half` — the `δ < 1/2` driver: two witness sets each of size `≥ (1-δ)n`
  satisfy `|ι| < |S₁| + |S₂|`.
* `badCount_le_witnessCodeword_card` — **the reduction.** For `δ < 1/2` and a full-support line,
  the bad-scalar count is at most the number of distinct line-witnessing codewords (the line list
  size). Plug into `ProximityGap.epsMCA_le_of_badCount_le` to obtain an `ε_mca` bound from any
  uniform list-size bound.

## Honest scope

The full-support hypothesis on `u₁` in the headline reduction is genuine: for a line whose second
word has many zeros, a single codeword can witness several bad scalars (it agrees with the whole
line on the zero coordinates), so the codeword-level pinning degrades — quantified exactly by the
zero-count term in `unique_bad_gamma_common_codeword_general`. And the line list size itself,
beyond the Johnson radius for explicit smooth-domain RS, is the open prize core — this file
reduces MCA to it, it does not bound it.

All results are hole-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
  Tracking issue #232; direction §2 (list-decoding ⇒ MCA).
-/

set_option linter.unusedSectionVars false

open scoped NNReal ENNReal BigOperators
open ProximityGap Code

namespace ProximityGap.MCAWitnessSpreadCodeword

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- **Codeword pinning (general).** If a single codeword `w` agrees with the line `u₀ + γ₁·u₁` on
`S₁` and with `u₀ + γ₂·u₁` on `S₂`, and the two witness sets are jointly large enough that their
overlap must contain a coordinate where `u₁ ≠ 0` (`|ι| + #{i : u₁ i = 0} < |S₁| + |S₂|`), then
`γ₁ = γ₂`. No full-support assumption: the overlap simply has to outrun the zero-set of `u₁`. -/
theorem unique_bad_gamma_common_codeword_general
    (u₀ u₁ : ι → A)
    {γ₁ γ₂ : F} {w : ι → A} {S₁ S₂ : Finset ι}
    (hcard : Fintype.card ι + (Finset.univ.filter (fun i => u₁ i = 0)).card
        < S₁.card + S₂.card)
    (h₁ : ∀ i ∈ S₁, w i = u₀ i + γ₁ • u₁ i)
    (h₂ : ∀ i ∈ S₂, w i = u₀ i + γ₂ • u₁ i) :
    γ₁ = γ₂ := by
  by_contra hne
  have hd : γ₁ - γ₂ ≠ 0 := sub_ne_zero.mpr hne
  have hun : (S₁ ∪ S₂).card ≤ Fintype.card ι := by simpa using Finset.card_le_univ (S₁ ∪ S₂)
  have hui : (S₁ ∪ S₂).card + (S₁ ∩ S₂).card = S₁.card + S₂.card :=
    Finset.card_union_add_card_inter S₁ S₂
  have hintergt : (Finset.univ.filter (fun i => u₁ i = 0)).card < (S₁ ∩ S₂).card := by omega
  have hnsub : ¬ (S₁ ∩ S₂) ⊆ Finset.univ.filter (fun i => u₁ i = 0) := fun hsub =>
    absurd (Finset.card_le_card hsub) (not_le.mpr hintergt)
  obtain ⟨i, hiInter, hiZero⟩ := Finset.not_subset.mp hnsub
  rw [Finset.mem_inter] at hiInter
  have hu1 : u₁ i ≠ 0 := fun h => hiZero (Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩)
  have e : u₀ i + γ₁ • u₁ i = u₀ i + γ₂ • u₁ i := by rw [← h₁ i hiInter.1, ← h₂ i hiInter.2]
  have hz : (γ₁ - γ₂) • u₁ i = 0 := by
    have h3 : γ₁ • u₁ i = γ₂ • u₁ i := add_left_cancel e
    rw [sub_smul, h3, sub_self]
  exact hu1 (by rw [← inv_smul_smul₀ hd (u₁ i), hz, smul_zero])

/-- **Codeword pinning (full-support line).** The full-support specialization of
`unique_bad_gamma_common_codeword_general`: when `u₁` has no zeros, the zero-set is empty so the
overlap condition is just `|ι| < |S₁| + |S₂|`. -/
theorem unique_bad_gamma_common_codeword
    (u₀ u₁ : ι → A) (hsupp : ∀ i, u₁ i ≠ 0)
    {γ₁ γ₂ : F} {w : ι → A} {S₁ S₂ : Finset ι}
    (hcard : Fintype.card ι < S₁.card + S₂.card)
    (h₁ : ∀ i ∈ S₁, w i = u₀ i + γ₁ • u₁ i)
    (h₂ : ∀ i ∈ S₂, w i = u₀ i + γ₂ • u₁ i) :
    γ₁ = γ₂ := by
  refine unique_bad_gamma_common_codeword_general u₀ u₁ ?_ h₁ h₂
  have hempty : (Finset.univ.filter (fun i => u₁ i = 0)) = ∅ :=
    Finset.filter_eq_empty_iff.mpr fun i _ => hsupp i
  rw [hempty, Finset.card_empty]; omega

/-- **Overlap core.** A single codeword `w` agreeing with two *distinct* line points overlaps only
inside the zero-set of `u₁`: on `S₁ ∩ S₂`, `(γ₁ - γ₂)·u₁ = 0`, so `u₁ = 0` there. -/
theorem overlap_subset_zeros
    (u₀ u₁ w : ι → A) {γ₁ γ₂ : F} (hne : γ₁ ≠ γ₂) {S₁ S₂ : Finset ι}
    (h₁ : ∀ i ∈ S₁, w i = u₀ i + γ₁ • u₁ i)
    (h₂ : ∀ i ∈ S₂, w i = u₀ i + γ₂ • u₁ i) :
    S₁ ∩ S₂ ⊆ Finset.univ.filter (fun i => u₁ i = 0) := by
  intro i hi
  rw [Finset.mem_inter] at hi
  have hd : γ₁ - γ₂ ≠ 0 := sub_ne_zero.mpr hne
  have e : u₀ i + γ₁ • u₁ i = u₀ i + γ₂ • u₁ i := by rw [← h₁ i hi.1, ← h₂ i hi.2]
  have hz : (γ₁ - γ₂) • u₁ i = 0 := by rw [sub_smul, add_left_cancel e, sub_self]
  have hu : u₁ i = 0 := by rw [← inv_smul_smul₀ hd (u₁ i), hz, smul_zero]
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hu⟩

/-- **Per-codeword fiber-packing bound (all stacks — no full-support assumption).** A single
codeword `w` witnesses at most `(n - z)/(t - z)` bad scalars, where `z = #{i : u₁ i = 0}` and each
witness set has size `≥ t > z`: the cleaned witness sets `S_γ \ zeros(u₁)` are pairwise disjoint
(by `overlap_subset_zeros`), each of size `≥ t - z`, packed inside the `(n - z)`-element non-zero
coordinate set. For a full-support line (`z = 0`) with `t > n/2` this gives at most one bad scalar
per codeword, recovering `unique_bad_gamma_common_codeword`. -/
theorem fiber_card_packing
    (u₀ u₁ w : ι → A) (t : ℕ) (G : Finset F) (S : F → Finset ι)
    (hSt : ∀ γ ∈ G, t ≤ (S γ).card)
    (hagree : ∀ γ ∈ G, ∀ i ∈ S γ, w i = u₀ i + γ • u₁ i)
    (htz : (Finset.univ.filter (fun i => u₁ i = 0)).card < t) :
    G.card * (t - (Finset.univ.filter (fun i => u₁ i = 0)).card)
      ≤ Fintype.card ι - (Finset.univ.filter (fun i => u₁ i = 0)).card := by
  set Z := Finset.univ.filter (fun i => u₁ i = 0) with hZ
  set f : F → Finset ι := fun γ => S γ \ Z with hf
  have hdisj : (G : Set F).Pairwise (fun γ γ' => Disjoint (f γ) (f γ')) := by
    intro γ hγ γ' hγ' hne
    rw [Finset.disjoint_left]
    intro i hi hi'
    simp only [hf, Finset.mem_sdiff] at hi hi'
    have hsub := overlap_subset_zeros u₀ u₁ w hne
      (fun j hj => hagree γ hγ j hj) (fun j hj => hagree γ' hγ' j hj)
    exact hi.2 (hsub (Finset.mem_inter.mpr ⟨hi.1, hi'.1⟩))
  have hcard_f : ∀ γ ∈ G, t - Z.card ≤ (f γ).card := by
    intro γ hγ
    have h1 : (S γ).card ≤ (f γ).card + Z.card := by
      simpa [hf] using Finset.card_le_card_sdiff_add_card (s := S γ) (t := Z)
    have h2 := hSt γ hγ
    omega
  have hbU : (G.biUnion f) ⊆ Finset.univ \ Z := by
    intro i hi
    rw [Finset.mem_biUnion] at hi
    obtain ⟨γ, _, hiγ⟩ := hi
    simp only [hf, Finset.mem_sdiff] at hiγ ⊢
    exact ⟨Finset.mem_univ i, hiγ.2⟩
  have hsum : (G.biUnion f).card = ∑ γ ∈ G, (f γ).card :=
    Finset.card_biUnion (fun x hx y hy h => hdisj hx hy h)
  have hle : (∑ γ ∈ G, (f γ).card) ≤ Fintype.card ι - Z.card := by
    rw [← hsum]
    calc (G.biUnion f).card ≤ (Finset.univ \ Z).card := Finset.card_le_card hbU
      _ = Fintype.card ι - Z.card := by
          rw [← Finset.compl_eq_univ_sdiff, Finset.card_compl]
  calc G.card * (t - Z.card) = ∑ _γ ∈ G, (t - Z.card) := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ γ ∈ G, (f γ).card := Finset.sum_le_sum hcard_f
    _ ≤ Fintype.card ι - Z.card := hle

/-- **The `δ < 1/2` overlap driver.** Two witness sets each of relative size `≥ 1 - δ` jointly
exceed `|ι|` when `δ < 1/2`, so they must overlap. -/
theorem card_sum_gt_of_lt_half (δ : ℝ≥0) (hδ : δ < 1/2) {S₁ S₂ : Finset ι}
    (h₁ : (1 - δ) * Fintype.card ι ≤ (S₁.card : ℝ≥0))
    (h₂ : (1 - δ) * Fintype.card ι ≤ (S₂.card : ℝ≥0)) :
    Fintype.card ι < S₁.card + S₂.card := by
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos (α := ι)
  have hδ1 : δ ≤ 1 := le_of_lt (lt_of_lt_of_le hδ (by norm_num))
  have hδ' : (δ : ℝ) < 1/2 := by exact_mod_cast hδ
  have c1 : (1 - (δ : ℝ)) * Fintype.card ι ≤ (S₁.card : ℝ) := by
    have h := NNReal.coe_le_coe.mpr h₁
    rwa [NNReal.coe_mul, NNReal.coe_sub hδ1, NNReal.coe_natCast, NNReal.coe_natCast,
      NNReal.coe_one] at h
  have c2 : (1 - (δ : ℝ)) * Fintype.card ι ≤ (S₂.card : ℝ) := by
    have h := NNReal.coe_le_coe.mpr h₂
    rwa [NNReal.coe_mul, NNReal.coe_sub hδ1, NNReal.coe_natCast, NNReal.coe_natCast,
      NNReal.coe_one] at h
  have key : (Fintype.card ι : ℝ) < (S₁.card : ℝ) + (S₂.card : ℝ) := by
    nlinarith [c1, c2, hn, hδ', mul_pos hn (by linarith : (0:ℝ) < 1 - 2 * δ)]
  exact_mod_cast key

open Classical in
/-- **Bad-scalar count ≤ line list size (`δ < 1/2`, full-support line).** The honest list-decoding
⇒ MCA reduction: below `δ = 1/2`, distinct bad scalars are witnessed by distinct codewords, so the
bad-scalar count of the stack `u` is at most the number of codewords agreeing with some line point
`u 0 + γ·(u 1)` on a size-`≥(1-δ)n` set — the line list size. Combine with
`ProximityGap.epsMCA_le_of_badCount_le` to turn a uniform list-size bound into an `ε_mca` bound. -/
theorem badCount_le_witnessCodeword_card
    (C : Set (ι → A)) (δ : ℝ≥0) (hδ : δ < 1/2) (u : WordStack A (Fin 2) ι)
    (hsupp : ∀ i, u 1 i ≠ 0) :
    (Finset.univ.filter (fun γ : F => mcaEvent C δ (u 0) (u 1) γ)).card
      ≤ (Finset.univ.filter (fun w : ι → A => w ∈ C ∧ ∃ S : Finset ι,
          (1 - δ) * Fintype.card ι ≤ (S.card : ℝ≥0) ∧
          ∃ γ : F, ∀ i ∈ S, w i = u 0 i + γ • u 1 i)).card := by
  apply Finset.card_le_card_of_injOn
    (f := fun γ => if hγ : mcaEvent C δ (u 0) (u 1) γ
      then (hγ.choose_spec.2.1).choose else 0)
  · intro γ hγf
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hγf
    have hγ : mcaEvent C δ (u 0) (u 1) γ := hγf
    have hspec := hγ.choose_spec
    have hwspec := hspec.2.1.choose_spec
    simp only [dif_pos hγ, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
    exact ⟨hwspec.1, hγ.choose, hspec.1, γ, fun i hi => hwspec.2 i hi⟩
  · intro γ₁ hγ₁f γ₂ hγ₂f hfeq
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hγ₁f hγ₂f
    have hγ₁ : mcaEvent C δ (u 0) (u 1) γ₁ := hγ₁f
    have hγ₂ : mcaEvent C δ (u 0) (u 1) γ₂ := hγ₂f
    simp only [dif_pos hγ₁, dif_pos hγ₂] at hfeq
    set w := (hγ₁.choose_spec.2.1).choose with hw
    have h1spec := hγ₁.choose_spec
    have h2spec := hγ₂.choose_spec
    have hw1 := h1spec.2.1.choose_spec
    have hw2 := h2spec.2.1.choose_spec
    have hcard := card_sum_gt_of_lt_half δ hδ h1spec.1 h2spec.1
    refine unique_bad_gamma_common_codeword (u 0) (u 1) hsupp hcard (w := w)
      (S₁ := hγ₁.choose) (S₂ := hγ₂.choose) ?_ ?_
    · intro i hi; exact hw1.2 i hi
    · intro i hi
      have hi2 := hw2.2 i hi
      rw [← hfeq] at hi2
      exact hi2

#print axioms unique_bad_gamma_common_codeword_general
#print axioms unique_bad_gamma_common_codeword
#print axioms overlap_subset_zeros
#print axioms fiber_card_packing
#print axioms card_sum_gt_of_lt_half
#print axioms badCount_le_witnessCodeword_card

end ProximityGap.MCAWitnessSpreadCodeword
