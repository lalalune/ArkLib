/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.JohnsonBound.Basic
import ArkLib.Data.CodingTheory.ListDecodability
import ArkLib.Data.CodingTheory.CodeGeometry

/-!
# ABF26 §3.1 — Johnson family `J_{q,ℓ}, J_q, J` and Theorem 3.2 / Corollary 3.3

Extensions to `JohnsonBound/Basic.lean` matching the paper-shaped statements from
ABF26 §3.1 (Arnon-Boneh-Fenzi, *Open Problems in List Decoding and Correlated
Agreement*, 2026).

The existing `JohnsonBound.J q δ : ℝ` matches the paper's `J_q(δ)`. This file adds:

- `JohnsonBound.Jqℓ q ℓ δ` — paper's `J_{q,ℓ}(δ)`, with the additional `ℓ/(ℓ-1)` factor
  inside the square root.
- `JohnsonBound.Jcap δ` — paper's asymptotic Johnson bound `J(δ) := 1 - √(1 - δ)`.

The three are related by `J_{q,ℓ}(δ) →_{ℓ → ∞} J_q(δ) →_{q → ∞} J(δ)`; we state the
limit relationships in docstrings but do not formalise the limits (the paper does
not prove them either).

The file also states the paper-shaped versions of:

- `johnson_bound_lambda_le_ell` — ABF26 Theorem 3.2 [Joh62]:
  `|Λ(C, J_{q,ℓ}(δ_min(C)))| ≤ ℓ`.
- `mds_johnson_lambda_le` — ABF26 Corollary 3.3:
  for any MDS code `C` of rate `ρ` and `η > 0`, `|Λ(C, 1 - √ρ - η)| ≤ 1/(2·η·ρ)`.

Both are admitted as external results (T3.2 has an existing in-tree proof via
`johnson_bound` / `johnson_bound_alphabet_free` in `JohnsonBound/Basic.lean` that
needs porting from the absolute-distance form to ABF26's `Lambda` form; C3.3
follows from L2.6 + T3.2, but uses the asymptotic Johnson radius which crosses
ArkLib's existing rate/distance bridge).

## References

- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*.
  2026.
- [Joh62] Johnson. (Original Johnson bound paper.)
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace JohnsonBound

open Real
open Finset

/-- **ABF26 Definition 3.1, `J_{q,ℓ}`.** Paper's q-ary ℓ-radius Johnson function:

  `J_{q,ℓ}(δ) := (1 - 1/q) · (1 - √(1 - q/(q-1) · ℓ/(ℓ-1) · δ))`

For `ℓ = 2` this is the binary Johnson radius; as `ℓ → ∞`, `Jqℓ q ℓ δ → J q δ`
(the existing `JohnsonBound.J`). The `ℓ` parameter is the target list size. -/
noncomputable def Jqℓ (q ℓ : ℚ) (δ : ℚ) : ℝ :=
  let frac : ℚ := q / (q - 1)
  let lFac : ℚ := ℓ / (ℓ - 1)
  ((1 - 1 / q) : ℚ) * (1 - √(1 - frac * lFac * δ))

/-- **ABF26 Definition 3.1, `J`.** Paper's asymptotic Johnson bound:

  `J(δ) := 1 - √(1 - δ)`

Equals the `q → ∞` limit of `J_q(δ)` and the `q, ℓ → ∞` limit of `J_{q,ℓ}(δ)`.
This is also the binary Johnson bound (q = 2, ℓ → ∞).

Distinct from the existing `JohnsonBound.J q δ`, which is the paper's `J_q(δ)`
(the q-ary limit, parametrised by `q`). To avoid renaming the existing `J`, we
name this `Jcap` (Johnson — *cap*acity). -/
noncomputable def Jcap (δ : ℝ) : ℝ := 1 - √(1 - δ)

@[simp]
lemma Jcap_zero : Jcap 0 = 0 := by simp [Jcap]

@[simp]
lemma Jcap_one : Jcap 1 = 1 := by simp [Jcap]

/-- Indexed q-ary Plotkin average-distance upper bound, with the same ordered-pair
normalisation as `JohnsonBound.d`.

This packages the simplex-embedding PSD bound from `CodeGeometry` into the
Johnson-bound denominator shape:
`2 * choose_2 M = M * (M - 1)`.

The statement is intentionally indexed by `Fin M`; the separate translation to
`Finset` images is the mechanical bridge needed by `johnson_bound_lambda_le_ell`. -/
theorem indexed_averageDist_le_plotkin
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {α : Type} [Fintype α] [DecidableEq α]
    {M : ℕ} (c : Fin M → ι → α) (hM : 1 < M) (hq : 0 < Fintype.card α) :
    (1 : ℝ) / (2 * ((choose_2 (M : ℚ)) : ℝ)) *
        (∑ i : Fin M, ∑ j ∈ Finset.univ.erase i,
          (hammingDist (c i) (c j) : ℝ)) ≤
      (M : ℝ) / ((M : ℝ) - 1) *
        (Fintype.card ι : ℝ) *
          (1 - 1 / (Fintype.card α : ℝ)) := by
  classical
  let C0 : ℝ :=
    (Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card α : ℝ))
  have htotal := CodeGeometry.sum_sum_hammingDist_le (ι := ι) (α := α) c hq
  have hoff_le_total :
      (∑ i : Fin M, ∑ j ∈ Finset.univ.erase i,
          (hammingDist (c i) (c j) : ℝ)) ≤
        (∑ i : Fin M, ∑ j : Fin M,
          (hammingDist (c i) (c j) : ℝ)) := by
    refine Finset.sum_le_sum fun i _ => ?_
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro j hj
      exact Finset.mem_univ j
    · intro j _ _
      exact_mod_cast Nat.zero_le (hammingDist (c i) (c j))
  have hoff_bound :
      (∑ i : Fin M, ∑ j ∈ Finset.univ.erase i,
          (hammingDist (c i) (c j) : ℝ)) ≤ (M : ℝ) * (M : ℝ) * C0 :=
    le_trans hoff_le_total htotal
  have hden :
      2 * (((choose_2 (M : ℚ)) : ℚ) : ℝ) = (M : ℝ) * ((M : ℝ) - 1) := by
    norm_num [choose_2]
    ring
  have hMpos : 0 < (M : ℝ) := by
    exact_mod_cast Nat.zero_lt_of_lt hM
  have hMsub_pos : 0 < (M : ℝ) - 1 := by
    exact sub_pos.mpr (by exact_mod_cast hM)
  have hden_nonneg : 0 ≤ 1 / ((M : ℝ) * ((M : ℝ) - 1)) := by
    positivity
  rw [hden]
  calc
    (1 : ℝ) / ((M : ℝ) * ((M : ℝ) - 1)) *
        (∑ i : Fin M, ∑ j ∈ Finset.univ.erase i,
          (hammingDist (c i) (c j) : ℝ))
        ≤ (1 : ℝ) / ((M : ℝ) * ((M : ℝ) - 1)) *
            ((M : ℝ) * (M : ℝ) * C0) :=
          mul_le_mul_of_nonneg_left hoff_bound hden_nonneg
    _ = (M : ℝ) / ((M : ℝ) - 1) * C0 := by
          field_simp [hMpos.ne', hMsub_pos.ne']
    _ = (M : ℝ) / ((M : ℝ) - 1) *
        (Fintype.card ι : ℝ) *
          (1 - 1 / (Fintype.card α : ℝ)) := by
          simp [C0, mul_assoc]

/-- Rewrites the indexed off-diagonal ordered-pair sum as a product-filter sum. -/
private lemma offdiag_sum_eq_product {M : ℕ} (f : Fin M → Fin M → ℝ) :
    (∑ i : Fin M, ∑ j ∈ (Finset.univ : Finset (Fin M)).erase i, f i j) =
      ∑ p ∈ (Finset.univ : Finset (Fin M × Fin M)) with p.1 ≠ p.2, f p.1 p.2 := by
  rw [Finset.sum_filter]
  rw [← Finset.univ_product_univ]
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [show (∑ y : Fin M, if (i, y).1 ≠ (i, y).2 then f (i, y).1 (i, y).2 else 0) =
      ∑ y : Fin M, if i ≠ y then f i y else 0 by rfl]
  rw [← Finset.sum_erase (s := (Finset.univ : Finset (Fin M))) (a := i)
      (f := fun y => if i ≠ y then f i y else 0) (by simp)]
  refine Finset.sum_congr rfl ?_
  intro y hy
  have hyne : i ≠ y := (Finset.mem_erase.mp hy).1.symm
  simp [hyne]

/-- Transports an indexed off-diagonal sum along `Finset.equivFin`. -/
private lemma offdiag_sum_equivFin
    {ι : Type} [Fintype ι] {α : Type} [DecidableEq α] (B : Finset (ι → α)) :
    (∑ i : Fin B.card, ∑ j ∈ (Finset.univ : Finset (Fin B.card)).erase i,
      (hammingDist ((Finset.equivFin B).symm i).1 ((Finset.equivFin B).symm j).1 : ℝ)) =
    ∑ x ∈ B ×ˢ B with x.1 ≠ x.2, (hammingDist x.1 x.2 : ℝ) := by
  rw [offdiag_sum_eq_product]
  let e : Fin B.card ≃ B := (Finset.equivFin B).symm
  let s : Finset (Fin B.card × Fin B.card) :=
    (Finset.univ : Finset (Fin B.card × Fin B.card)).filter (fun p => p.1 ≠ p.2)
  let t : Finset ((ι → α) × (ι → α)) := (B ×ˢ B).filter (fun x => x.1 ≠ x.2)
  change (∑ p ∈ s, (hammingDist (e p.1).1 (e p.2).1 : ℝ)) =
    ∑ x ∈ t, (hammingDist x.1 x.2 : ℝ)
  refine Finset.sum_bij (fun p _hp => ((e p.1).1, (e p.2).1)) ?_ ?_ ?_ ?_
  · intro p hp
    simp only [t, mem_filter, mem_product]
    have hpne : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
    refine ⟨⟨(e p.1).2, (e p.2).2⟩, ?_⟩
    intro hval
    apply hpne
    exact e.injective (Subtype.ext hval)
  · intro p _hp q _hq h
    simp only [Prod.mk.injEq] at h
    cases p with
    | mk p₁ p₂ =>
      cases q with
      | mk q₁ q₂ =>
        simp only at h
        have h₁ : p₁ = q₁ := e.injective (Subtype.ext h.1)
        have h₂ : p₂ = q₂ := e.injective (Subtype.ext h.2)
        simp [h₁, h₂]
  · intro x hx
    simp only [t, mem_filter, mem_product] at hx
    let a : B := ⟨x.1, hx.1.1⟩
    let b : B := ⟨x.2, hx.1.2⟩
    refine ⟨(e.symm a, e.symm b), ?_, ?_⟩
    · simp only [s, mem_filter, mem_univ, true_and]
      intro hidx
      apply hx.2
      have hsub : a = b := e.symm.injective hidx
      exact congrArg Subtype.val hsub
    · simp [e, a, b]
  · intro p _hp
    rfl

/-- Ordered-pair average distance for a finite family over an arbitrary finite index type.

This is `JohnsonBound.d` without the historical `Fin n` restriction. -/
noncomputable def averageDistOn
    {ι : Type} [Fintype ι] {α : Type} [DecidableEq α] (B : Finset (ι → α)) : ℚ :=
  (1 : ℚ) / (2 * choose_2 B.card) *
    ∑ x ∈ B ×ˢ B with x.1 ≠ x.2, Δ₀(x.1, x.2)

/-- Any two distinct members of a code are separated by at least `Code.minDist`. -/
lemma minDist_le_hammingDist_of_mem_ne
    {ι : Type} [Fintype ι] {α : Type} [DecidableEq α]
    {C : Set (ι → α)} {u v : ι → α}
    (hu : u ∈ C) (hv : v ∈ C) (hne : u ≠ v) :
    Code.minDist C ≤ hammingDist u v := by
  unfold Code.minDist
  apply Nat.sInf_le
  exact ⟨u, hu, v, hv, hne, rfl⟩

/-- The ordered off-diagonal pair count matches the Johnson `choose_2`
normalisation. -/
private lemma two_mul_choose_two_card_eq_offdiag_card
    {β : Type} [DecidableEq β] (B : Finset β) :
    2 * choose_2 (B.card : ℚ) = (({ x ∈ B ×ˢ B | x.1 ≠ x.2 }.card : ℕ) : ℚ) := by
  simp only [ne_eq]
  unfold choose_2
  ring_nf
  have BBcard : (B ×ˢ B).card = B.card ^ 2 := by rw [card_product, sq]
  have BBdiagcard : { x ∈ B ×ˢ B | x.1 = x.2 }.card = B.card := by simp
  have BBdisjoint : { x ∈ B ×ˢ B | x.1 = x.2 } ∩
      { x ∈ B ×ˢ B | x.1 ≠ x.2 } = ∅ := by
    grind only [= mem_inter, ← notMem_empty, = mem_filter]
  have BBunion : B ×ˢ B =
      { x ∈ B ×ˢ B | x.1 = x.2 } ∪ { x ∈ B ×ˢ B | x.1 ≠ x.2 } := by
    grind only [= mem_union, = mem_filter]
  have BBcount : { x ∈ B ×ˢ B | x.1 ≠ x.2 }.card =
      (B ×ˢ B).card - { x ∈ B ×ˢ B | x.1 = x.2 }.card := by
    grind only [usr card_filter_le, usr card_union_add_card_inter, = Finset.card_empty]
  rw [BBcount, BBcard, BBdiagcard, Nat.cast_sub]
  · grind only
  · grind only [usr card_filter_le]

/-- A finite sublist of a code has average pairwise distance at least the code
minimum distance. -/
theorem minDist_le_averageDistOn_of_subset
    {ι : Type} [Fintype ι] {α : Type} [DecidableEq α]
    {C : Set (ι → α)} {B : Finset (ι → α)}
    (hB : 1 < B.card) (hsub : ∀ x ∈ B, x ∈ C) :
    (Code.minDist C : ℚ) ≤ averageDistOn B := by
  unfold averageDistOn
  let dmin : ℚ := Code.minDist C
  have h_d : ∀ x ∈ { x ∈ B ×ˢ B | x.1 ≠ x.2 }, dmin ≤ Δ₀(x.1, x.2) := by
    intro x hx
    simp only [ne_eq, mem_filter, mem_product] at hx
    dsimp [dmin]
    exact_mod_cast minDist_le_hammingDist_of_mem_ne
      (hsub x.1 hx.1.1) (hsub x.2 hx.1.2) hx.2
  have B2_card :
      2 * choose_2 (B.card : ℚ) =
        (({ x ∈ B ×ˢ B | x.1 ≠ x.2 }.card : ℕ) : ℚ) :=
    two_mul_choose_two_card_eq_offdiag_card B
  have B2_card_pos : 0 < { x ∈ B ×ˢ B | x.1 ≠ x.2 }.card := by
    have ⟨u, hu, v, hv, huv⟩ := one_lt_card.mp hB
    have : { x ∈ B ×ˢ B | x.1 ≠ x.2 }.Nonempty := by
      use ⟨u, v⟩
      simp [hu, hv, huv]
    exact card_pos.mpr this
  have h_bound : ∑ x ∈ B ×ˢ B with x.1 ≠ x.2, dmin ≤
      ∑ x ∈ B ×ˢ B with x.1 ≠ x.2, Δ₀(x.1, x.2) :=
    by simpa [Nat.cast_sum] using sum_le_sum h_d
  have h_eq : dmin =
      1 / (2 * choose_2 (B.card : ℚ)) *
        ∑ x ∈ B ×ˢ B with x.1 ≠ x.2, dmin := by
    rw [sum_const, B2_card]
    simp only [ne_eq, one_div]
    set c := ({ x ∈ B ×ˢ B | ¬x.1 = x.2 }.card : ℚ) with hc
    have c_pos : 0 < c := by
      unfold c
      exact_mod_cast B2_card_pos
    rw [nsmul_eq_mul]
    change dmin = c⁻¹ * (c * dmin)
    field_simp [ne_of_gt c_pos]
  change dmin ≤ 1 / (2 * choose_2 (B.card : ℚ)) *
    ↑(∑ x ∈ B ×ˢ B with x.1 ≠ x.2, Δ₀(x.1, x.2))
  rw [h_eq]
  have c2_nonneg : 0 ≤ (1 / (2 * choose_2 (B.card : ℚ)) : ℚ) := by
    have c2_pos : 0 < (2 * choose_2 (B.card : ℚ) : ℚ) := by
      rw [B2_card]
      exact_mod_cast B2_card_pos
    positivity
  exact mul_le_mul_of_nonneg_left h_bound c2_nonneg

/-- Arbitrary-index q-ary Plotkin average-distance upper bound. -/
theorem averageDistOn_le_plotkin
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {α : Type} [Fintype α] [DecidableEq α]
    (B : Finset (ι → α)) (hB : 2 ≤ B.card) (hq : 0 < Fintype.card α) :
    ((averageDistOn B : ℚ) : ℝ) ≤
      (B.card : ℝ) / ((B.card : ℝ) - 1) * (Fintype.card ι : ℝ) *
        (1 - 1 / (Fintype.card α : ℝ)) := by
  let e : Fin B.card ≃ B := (Finset.equivFin B).symm
  let c : Fin B.card → ι → α := fun i => (e i).1
  have hM : 1 < B.card := by omega
  have hplot := indexed_averageDist_le_plotkin (ι := ι) (α := α)
    (M := B.card) c hM hq
  have hsum :
      (∑ i : Fin B.card, ∑ j ∈ (Finset.univ : Finset (Fin B.card)).erase i,
        (hammingDist (c i) (c j) : ℝ)) =
      ∑ x ∈ B ×ˢ B with x.1 ≠ x.2, (hammingDist x.1 x.2 : ℝ) := by
    simpa [c, e] using offdiag_sum_equivFin B
  rw [hsum] at hplot
  unfold averageDistOn
  simpa [Nat.cast_sum] using hplot

/-- Finset form of the q-ary Plotkin average-distance upper bound for
`JohnsonBound.d`.

This is the theorem needed to connect the simplex PSD development in
`CodeGeometry` to the existing Johnson-bound average-distance notation. -/
theorem averageDist_le_plotkin
    {n : ℕ} {α : Type} [Fintype α] [DecidableEq α]
    (B : Finset (Fin n → α)) (hB : 2 ≤ B.card) (hq : 0 < Fintype.card α) :
    ((d B : ℚ) : ℝ) ≤
      (B.card : ℝ) / ((B.card : ℝ) - 1) * (n : ℝ) *
        (1 - 1 / (Fintype.card α : ℝ)) := by
  let e : Fin B.card ≃ B := (Finset.equivFin B).symm
  let c : Fin B.card → Fin n → α := fun i => (e i).1
  have hM : 1 < B.card := by omega
  have hplot := indexed_averageDist_le_plotkin (ι := Fin n) (α := α)
    (M := B.card) c hM hq
  have hsum :
      (∑ i : Fin B.card, ∑ j ∈ (Finset.univ : Finset (Fin B.card)).erase i,
        (hammingDist (c i) (c j) : ℝ)) =
      ∑ x ∈ B ×ˢ B with x.1 ≠ x.2, (hammingDist x.1 x.2 : ℝ) := by
    simpa [c, e] using offdiag_sum_equivFin B
  rw [hsum] at hplot
  unfold d
  simpa [Nat.cast_sum] using hplot

/-- A violated finite `Lambda` bound produces a concrete point-list whose average
distance is controlled by the q-ary Plotkin bound.

This is the contradiction-entry bridge for `johnson_bound_lambda_le_ell`: after
assuming `ℓ < Lambda C δ`, one can work with the finite close-list around a
specific received word. -/
theorem exists_closeList_gt_and_averageDistOn_le_plotkin_of_natCast_lt_Lambda
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {α : Type} [Fintype α] [DecidableEq α]
    (C : ListDecodable.Code ι α) {δ : ℝ} {ℓ : ℕ}
    (hℓ : 1 ≤ ℓ) (hq : 0 < Fintype.card α)
    (hΛ : (ℓ : ℕ∞) < ListDecodable.Lambda C δ) :
    ∃ f : ι → α,
      ℓ < (ListDecodable.closeCodewordsRelFinset C f δ).card ∧
        ((averageDistOn (ListDecodable.closeCodewordsRelFinset C f δ) : ℚ) : ℝ) ≤
          ((ListDecodable.closeCodewordsRelFinset C f δ).card : ℝ) /
              (((ListDecodable.closeCodewordsRelFinset C f δ).card : ℝ) - 1) *
            (Fintype.card ι : ℝ) *
              (1 - 1 / (Fintype.card α : ℝ)) := by
  rcases ListDecodable.exists_closeFinset_card_gt_of_natCast_lt_Lambda hΛ with ⟨f, hf⟩
  refine ⟨f, hf, ?_⟩
  exact averageDistOn_le_plotkin (ListDecodable.closeCodewordsRelFinset C f δ)
    (by omega) hq

end JohnsonBound

namespace CodingTheory

open scoped NNReal
open ListDecodable JohnsonBound

/-- **ABF26 Theorem 3.2 [Joh62].** Johnson bound on list size. For any code
`C ⊆ Σ^n` with `|Σ| = q`,

  `|Λ(C, J_{q,ℓ}(δ_min(C)))| ≤ ℓ`

where `δ_min(C) = minDist(C) / n` is the relative minimum distance and `J_{q,ℓ}`
is the paper's q-ary ℓ-radius Johnson function. **Admitted (tagged sorry).**

**Why the in-tree `johnson_bound` does NOT reach this radius (verified, 2026-06-04).**
A prior triage suggested "plug `e/n = J_{q,ℓ}` into the in-tree `johnson_bound`; its
`JohnsonConditionStrong` then fails at the boundary, forcing `|Λ| ≤ ℓ`". This was
re-checked symbolically and is **incorrect** — there is a factor inversion that makes
the in-tree bound land at a *strictly smaller* radius. The exact computation:

Write `frac = q/(q-1)`, `t = frac·δ_min`, `L = ℓ/(ℓ-1) > 1`. The boundary identity for
`Jqℓ` is `(1 - frac·Jqℓ)² = 1 - frac·L·δ_min = 1 - L·t`. The packaged bound
[`johnson_bound`](Basic.lean) gives `B.card ≤ (frac·d/n)/Denom` with
`Denom = (1 - frac·e/n)² - (1 - frac·d/n)`. Setting `e/n = Jqℓ`, `d/n = δ_min`:
`Denom = (1 - L·t) - (1 - t) = t·(1 - L) = -t/(ℓ-1) < 0`. So `JohnsonConditionStrong`
(`Denom > 0`) is *false* and the bound is unusable — but the failure does **not** force
`|Λ| ≤ ℓ`: the raw [`johnson_bound_lemma`](Lemmas.lean), which holds unconditionally
(`n>0`, `|B|≥2`, `|F|≥2`), reads `B.card · Denom ≤ frac·d/n`, and with `Denom < 0` this
is a *negative lower* bound on `B.card` — vacuous as an upper bound.

Inverting the packaging the other way: `johnson_bound` yields `B.card ≤ ℓ` exactly when
`Denom ≥ (frac·d/n)/ℓ = t/ℓ`, i.e. `(1 - frac·e/n)² ≥ 1 - t·(ℓ-1)/ℓ = 1 - t/L`, i.e.
`e/n ≤ (1/frac)·(1 - √(1 - frac·δ_min/L))`. That radius uses the factor `1/L = (ℓ-1)/ℓ`,
the **reciprocal** of the `L = ℓ/(ℓ-1)` factor inside `Jqℓ`. Since `L > 1`, the in-tree
radius is strictly *smaller* than the paper's `Jqℓ`. The paper's larger (tight) list-of-ℓ
radius is the Plotkin-refined Johnson radius and is not reachable from the second-moment
`johnson_bound` alone.

**Exact missing ingredient (citation upgrade).** Closing T3.2 at the paper's `Jqℓ`
requires the *q-ary Plotkin average-distance upper bound*

  `d(B') ≤ frac · n · M/(M-1)`     where `M = |B'|`, `frac = q/(q-1)`,

i.e. the convex *dual* of the in-tree `almost_johnson` (which lower-bounds
`∑_α C₂(K_i(α))`; the Plotkin step instead lower-bounds `∑_α K_i(α)² ≥ M²/q` by
Cauchy–Schwarz / power-mean, giving an *upper* bound on the average distance).
The Plotkin piece is now in-tree as `indexed_averageDist_le_plotkin`,
`averageDistOn_le_plotkin`, and the `Fin n` specialization `averageDist_le_plotkin`.
Combining this bound with the remaining Johnson-radius algebra and a pointwise list
construction is the next step toward T3.2.

**Remaining mechanical gaps**:
- *Alphabet*: this statement is over a bare alphabet `α` (`Fintype + DecidableEq`, no
  `Field`), but every in-tree Johnson lemma — including `johnson_bound_alphabet_free` —
  carries `[Field F]`. The Plotkin bridge itself is alphabet-generic, but the older
  `johnson_bound_lemma` route is field-shaped.
- *List packaging*: a pointwise finite-list bound must be constructed for
  `closeCodewordsRel C f (Jqℓ q ℓ δ_min)` and then passed through
  `ListDecodable.Lambda_le_natCast_of_forall_ncard_le`.
- *Radius algebra*: the final `Jqℓ` inequality still has to be expressed in the exact
  rational/real shape consumed by the Johnson proof skeleton.

Tracked in `docs/kb/ABF26_PLAN.md` and the audit log.

**Alphabet generality.** Stated over an arbitrary alphabet `α` (not necessarily a
field), matching the paper's `Σ`. The Johnson bound is a purely combinatorial fact
about Hamming distance — it does not need field structure. -/
theorem johnson_bound_lambda_le_ell
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {α : Type} [Fintype α] [DecidableEq α]
    (C : Set (ι → α)) (ℓ : ℕ) (_hℓ_ge : 2 ≤ ℓ) :
    let q : ℚ := Fintype.card α
    let δ_min : ℚ := Code.minDist C / Fintype.card ι
    Lambda C (Jqℓ q ℓ δ_min) ≤ (ℓ : ℕ∞) := by
  -- ABF26-T3.2; external admit. The ONLY nontrivial gap is the q-ary Plotkin
  -- average-distance upper bound `d(B') ≤ frac·n·M/(M-1)` (see docstring). Four
  -- attempted in-tree routes, each blocked at a precisely-identified step:
  --
  -- SKELETON 1 (direct `johnson_bound`, the route the docstring refutes).
  --   intro q δ_min; refine iSup_le fun f => ?_;  set B' := closeCodewordsRel C f _
  --   Transport B' to a `Finset (Fin n → α)`; apply `johnson_bound` to get
  --   `B'.card ≤ (frac·d/n)/Denom`.  BLOCKED: at `e/n = Jqℓ`, `Denom = -t/(ℓ-1) < 0`,
  --   so `JohnsonConditionStrong` is false; no `B'.card ≤ ℓ` follows (factor inversion).
  --
  -- SKELETON 2 (raw `johnson_bound_lemma` + Plotkin — the CORRECT route).
  --   From `johnson_bound_lemma`: `M·Denom ≤ frac·d_avg/n`, holds unconditionally.
  --   Need: q-ary Plotkin `d_avg ≤ frac·n·M/(M-1)` ⇒ substitute and solve for M.
  --   STATUS: the Plotkin bound is now in-tree (`averageDistOn_le_plotkin` /
  --   `averageDist_le_plotkin`). Remaining work is the algebraic substitution into the
  --   Johnson skeleton and the `closeCodewordsRel`/`Lambda` packaging.
  --
  -- SKELETON 3 (`johnson_bound_alphabet_free` ⇒ `q·d·n`).
  --   `johnson_bound_alphabet_free` gives `(B ∩ ball e).card ≤ q·d·n` under
  --   `e ≤ n - √(n·(n-d))`.  BLOCKED twice: (a) the bound `q·d·n` is far weaker than `ℓ`
  --   (it is the alphabet-free coarse form, not list-of-ℓ); (b) its radius hypothesis is
  --   the `J_q` (ℓ→∞) radius, not `Jqℓ` — wrong both in tightness and in the ℓ-factor.
  --
  -- SKELETON 4 (Lambda_mono down to the in-tree reachable radius `1/L`).
  --   By the docstring, `johnson_bound` *does* give `|Λ(C, R₀)| ≤ ℓ` at
  --   `R₀ = (1/frac)(1 - √(1 - frac·δ_min/L))`.  `Lambda_mono` needs `Jqℓ ≤ R₀` to
  --   transport ℓ from `R₀` up to `Jqℓ`.  BLOCKED: `Jqℓ > R₀` (since `L > 1/L`), so
  --   monotonicity runs the WRONG way — it would only give `|Λ(C, Jqℓ)| ≥ |Λ(C, R₀)|`.
  --   This is the formal restatement of the factor inversion: the in-tree bound is
  --   strictly inside the paper's radius, and Lambda is monotone INCREASING in radius.
  --
  -- Tagged sorry until the Johnson-radius algebra and list-packaging layer land.
  sorry

/-- **ABF26 Corollary 3.3.** MDS coarse Johnson corollary. For every MDS code `C` with
rate `ρ := dim C / n` and `η > 0`:

  `|Λ(C, 1 - √ρ - η)| ≤ 1 / (2 · η · ρ)`

Derives from L2.6 (Singleton bound: MDS implies `δ_min = 1 - ρ + 1/n`, available via
the `IsMDS_iff_rate_distance` bridge) plus T3.2 (or its asymptotic version via `Jcap`).
Admitted as an external result; the path to a machine-checked proof requires the
asymptotic-Johnson form `Lambda C δ ≤ 1/(2·(Jcap δ - δ))` plus MDS rate-distance
manipulation.

**Rate derivation.** `ρ` is bound inline as `(Module.finrank F C : ℝ) / Fintype.card ι`
rather than passed as a separate parameter — this matches the upstream `IsMDS`
signature (additive Nat form, no rate parameter) and lets call sites use
`IsMDS_iff_rate_distance` to extract the rate-distance equation when needed. -/
theorem mds_johnson_lambda_le
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (C : LinearCode ι F) (η : ℝ) (_hη_pos : 0 < η)
    (_h_mds : LinearCode.IsMDS C) :
    let ρ : ℝ := (Module.finrank F C : ℝ) / Fintype.card ι
    (Lambda ((C : Set (ι → F))) (1 - Real.sqrt ρ - η) : ENNReal) ≤
      ENNReal.ofReal (1 / (2 * η * ρ)) := by
  -- ABF26-C3.3; external admit. Reduction chain (each step verified to exist in-tree):
  --   1. `IsMDS_iff_rate_distance` (Basic/LinearCode.lean) ⇒ for an MDS code,
  --      `δ_min = 1 - ρ + 1/n`, hence `Jcap δ_min = 1 - √ρ + O(1/n)` matches the
  --      `1 - √ρ - η` radius once `η` absorbs the `1/n` correction.
  --   2. The asymptotic (q,ℓ → ∞) `Jcap` form of T3.2: `Lambda C δ ≤ 1/(2·(Jcap δ - δ))`.
  -- BLOCKED: step 2 IS T3.2 in its asymptotic specialisation. The q-ary Plotkin
  -- average-distance upper bound is now available, so the remaining obstruction is
  -- the T3.2 Johnson-radius/list-packaging proof plus pure algebra on the Singleton
  -- equation. Tagged sorry until T3.2 lands at `Jqℓ`/`Jcap`.
  sorry

end CodingTheory
