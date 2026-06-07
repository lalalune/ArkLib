/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ListDecoding.CZ25DesignToLambda
import ArkLib.Data.CodingTheory.ListDecoding.CZ25SpanDimension
import Mathlib.InformationTheory.Hamming

/-!
# CZ25 dimension-count: reusable agreement-coordinate bricks (issue #93)

Reusable sub-bricks toward the greedy-chain argument of `CodingTheory.CZ25DimensionCount`
(`ListDecoding/CZ25DesignToLambda.lean:152`), the per-received-word real bound
`|closeCodewordsRel C f δ| ≤ (1 - τ(r₀))/η` against an `IsSubspaceDesign` budget.

The genuine core is the Guruswami-Wang iterative charge, which `CZ25SpanDimension.lean`
documents as having no shortcut over the design budget (the naive single-base-point witnesses
are *provably false* there). This file lands the genuinely-reusable, axiom-clean ingredients
that the greedy chain (step 1 of the issue-#93 proof architecture) consumes:

* **agreement-coordinate lower bound** — for `c ∈ closeCodewordsRel C f δ`, the number of
  block coordinates `i : ι` where `c i = f i` is at least `(1 - δ)·n`. Equivalently, the
  disagreement count is at most `δ·n`. This is the "agreement ≥ (τ(r₀)+η)·n" datum that
  the greedy chain's step-1 charge consumes.
* **recentred-difference vanishing count** — if two close codewords `c` and `c₀` both agree
  with `f` on large coordinate sets, then their difference `c - c₀` vanishes on the
  intersection of those agreement sets, giving at least `(1 - 2δ)·n` vanishing coordinates.

All results are stated for the block alphabet `Fin s → F` (so `α = Fin s → F`, not a field),
matching the subspace-design coordinate structure, and are `sorry`-free / axiom-clean
(`[propext, Classical.choice, Quot.sound]`).

## References

- [CZ25] Thm B.5 (subspace-design route to capacity list decoding).
- [GW13] Guruswami-Wang. *Linear-algebraic list decoding of folded Reed-Solomon codes.*
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace CodingTheory

open scoped NNReal
open ListDecodable

section AgreementCount

variable {ι : Type} [Fintype ι] [Nonempty ι]
variable {α : Type} [DecidableEq α]

/-- **Disagreement count as a `Finset.filter` cardinality.** The Hamming distance
`hammingDist f c = #{i | f i ≠ c i}` equals the cardinality of the filtered universe of
coordinates on which `f` and `c` disagree. This is the `Finset.filter`-form of the Mathlib
definition `hammingDist x y = #{i | x i ≠ y i}`, made explicit so downstream agreement
counts can split the universe into agreeing/disagreeing parts. -/
lemma hammingDist_eq_card_filter_ne (f c : ι → α) :
    hammingDist f c = (Finset.univ.filter (fun i => f i ≠ c i)).card := by
  classical
  rw [hammingDist]

/-- **Agreement count = `n − hammingDist`.** The number of block coordinates on which `f`
and `c` *agree* is `n − hammingDist f c`. Splits the universe of coordinates into the
agreeing and disagreeing parts. -/
lemma card_agree_eq (f c : ι → α) :
    (Finset.univ.filter (fun i => f i = c i)).card =
      Fintype.card ι - hammingDist f c := by
  classical
  rw [hammingDist_eq_card_filter_ne]
  have hsplit : (Finset.univ.filter (fun i => f i = c i)).card +
      (Finset.univ.filter (fun i => f i ≠ c i)).card = Fintype.card ι := by
    simpa [Finset.card_univ] using
      Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset ι))
        (p := fun i : ι => f i = c i)
  omega

/-- **Real-valued disagreement bound from a relative-distance radius.** If the *real* relative
Hamming distance is bounded by `δ`, i.e. `(δᵣ(f, c) : ℝ) ≤ δ`, then the disagreement count is
bounded by `δ·n`:

  `(#{i : f i ≠ c i} : ℝ) ≤ δ · n`.

This unfolds `relHammingDist = hammingDist / n` and clears the (positive) denominator `n`. -/
lemma card_disagree_le_of_relHammingDist_le
    (f c : ι → α) {δ : ℝ}
    (hδ : ((Code.relHammingDist f c : ℚ≥0) : ℝ) ≤ δ) :
    ((Finset.univ.filter (fun i => f i ≠ c i)).card : ℝ) ≤ δ * Fintype.card ι := by
  classical
  have hn_pos : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  -- `relHammingDist f c = hammingDist f c / n`, cast to ℝ.
  have hrel : ((Code.relHammingDist f c : ℚ≥0) : ℝ)
      = (hammingDist f c : ℝ) / Fintype.card ι := by
    rw [Code.relHammingDist]
    push_cast
    ring
  rw [hrel, div_le_iff₀ hn_pos] at hδ
  rw [hammingDist_eq_card_filter_ne] at hδ
  linarith

/-- **Agreement-coordinate lower bound (the greedy-chain step-1 datum).** For a codeword
`c ∈ closeCodewordsRel C f δ` (`c ∈ C` and `δᵣ(f, c) ≤ δ`), the number of block coordinates
on which `c` agrees with `f` is at least `(1 - δ)·n`:

  `(1 - δ) · n ≤ (#{i : f i = c i} : ℝ)`.

This is the per-element agreement bound that the CZ25 / Guruswami-Wang greedy chain consumes
in step 1 ("each candidate agrees with `f` on `≥ (τ(r₀)+η)·n` coordinates"): at the capacity
radius `δ = 1 - τ(r₀) - η`, the right-hand floor is `(τ(r₀)+η)·n`. Proven from the
relative-distance membership alone; no design / iterative-charge content. -/
lemma card_agree_ge_of_mem_closeCodewordsRel
    (C : Set (ι → α)) (f c : ι → α) {δ : ℝ}
    (hc : c ∈ closeCodewordsRel C f δ) :
    (1 - δ) * Fintype.card ι ≤
      ((Finset.univ.filter (fun i => f i = c i)).card : ℝ) := by
  classical
  rw [mem_closeCodewordsRel_iff_real] at hc
  have hdis := card_disagree_le_of_relHammingDist_le f c hc.2
  have hle : hammingDist f c ≤ Fintype.card ι := hammingDist_le_card_fintype
  -- `#agree = n - hammingDist`, cast to ℝ.
  have hagree : ((Finset.univ.filter (fun i => f i = c i)).card : ℝ)
      = (Fintype.card ι : ℝ) - hammingDist f c := by
    rw [card_agree_eq]
    push_cast [Nat.cast_sub hle]
    ring
  rw [hagree]
  rw [hammingDist_eq_card_filter_ne] at hle ⊢
  -- From `#disagree ≤ δ·n`, get `n - #disagree ≥ n - δ·n = (1-δ)·n`.
  nlinarith [hdis]

/-- **Double-counting / Fubini swap of the agreement table.** For a finite list `L` of
codewords, the total agreement mass — summed first over list elements `c ∈ L`, then over the
coordinates each agrees on — equals the same table summed coordinate-first:

  `∑_{c ∈ L} #{i : c i = f i} = ∑_{i} #{c ∈ L : c i = f i}`.

This swaps the order of the agreement double count. The right-hand side is exactly the
per-coordinate quantity `∑_i |{c ∈ L : c i = f i}|` that the CZ25 design half
(`sum_card_vanishing_le_design`) caps from above through the subspace-design budget; the
left-hand side is the per-element agreement the previous lemma lower-bounds. So this is the
bridge between the two halves of the dimension count. -/
lemma sum_agree_swap (f : ι → α) (L : Finset (ι → α)) :
    (∑ c ∈ L, (Finset.univ.filter (fun i => c i = f i)).card) =
      ∑ i : ι, (L.filter (fun c => c i = f i)).card := by
  classical
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]

/-- **Aggregate agreement lower bound over a list of close codewords.** If every codeword in
a finite list `L` lies in `closeCodewordsRel C f δ`, the total per-element agreement mass is
at least `|L| · (1 - δ) · n`:

  `|L| · (1 - δ) · n ≤ ∑_{c ∈ L} #{i : c i = f i}`.

Sums `card_agree_ge_of_mem_closeCodewordsRel` over the list. Combined with `sum_agree_swap`
this lower-bounds the coordinate-first agreement table `∑_i #{c ∈ L : c i = f i}` that the
design half caps — the elementary "fresh agreement mass" accounting feeding the greedy chain.
Note the order in the filter (`c i = f i`) matches `sum_agree_swap`; we use the symmetry of
equality to align with `card_agree_ge_of_mem_closeCodewordsRel`'s `f i = c i`. -/
lemma sum_agree_ge_of_subset_closeCodewordsRel
    (C : Set (ι → α)) (f : ι → α) {δ : ℝ}
    (L : Finset (ι → α)) (hL : ∀ c ∈ L, c ∈ closeCodewordsRel C f δ) :
    (L.card : ℝ) * ((1 - δ) * Fintype.card ι) ≤
      ∑ c ∈ L, ((Finset.univ.filter (fun i => c i = f i)).card : ℝ) := by
  classical
  have hper : ∀ c ∈ L, (1 - δ) * Fintype.card ι ≤
      ((Finset.univ.filter (fun i => c i = f i)).card : ℝ) := by
    intro c hc
    have h := card_agree_ge_of_mem_closeCodewordsRel C f c (hL c hc)
    -- align `f i = c i` (lemma) with `c i = f i` (here) via filter congruence.
    have hfilt : (Finset.univ.filter (fun i => f i = c i)).card
        = (Finset.univ.filter (fun i => c i = f i)).card := by
      simp only [eq_comm]
    rwa [hfilt] at h
  calc (L.card : ℝ) * ((1 - δ) * Fintype.card ι)
      = ∑ _c ∈ L, ((1 - δ) * Fintype.card ι) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ c ∈ L, ((Finset.univ.filter (fun i => c i = f i)).card : ℝ) :=
        Finset.sum_le_sum hper

end AgreementCount

section DifferenceVanish

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [DecidableEq F]

/-- **Recentred-difference vanishing count (greedy-chain step-2 input).** If two codewords
`c` and `c₀` both lie in the close list around `f` at radius `δ`, then their recentred
difference vanishes on at least `(1 - 2δ)·n` block coordinates:

  `(1 - 2δ) · n ≤ #{i : c i - c₀ i = 0}`.

Indeed, `c` agrees with `f` on at least `(1 - δ)·n` coordinates and `c₀` agrees with `f` on
at least `(1 - δ)·n` coordinates. The intersection of the two agreement sets has size at
least `(1 - 2δ)·n`, and on that intersection `c i = f i = c₀ i`, so the recentred difference
vanishes. This is the reusable input that feeds the recentred span
`span {c - c₀ | c ∈ L}` into the subspace-design vanishing budget. -/
lemma card_diff_vanish_ge_of_mem_closeCodewordsRel
    (s : ℕ) (C : Set (ι → Fin s → F)) (f c c₀ : ι → Fin s → F) {δ : ℝ}
    (hc : c ∈ closeCodewordsRel C f δ)
    (hc₀ : c₀ ∈ closeCodewordsRel C f δ) :
    (1 - 2 * δ) * Fintype.card ι ≤
      ((Finset.univ.filter (fun i => c i - c₀ i = 0)).card : ℝ) := by
  classical
  let A : Finset ι := Finset.univ.filter (fun i => f i = c i)
  let B : Finset ι := Finset.univ.filter (fun i => f i = c₀ i)
  let V : Finset ι := Finset.univ.filter (fun i => c i - c₀ i = 0)
  have hA : (1 - δ) * Fintype.card ι ≤ (A.card : ℝ) := by
    simpa [A] using card_agree_ge_of_mem_closeCodewordsRel C f c hc
  have hB : (1 - δ) * Fintype.card ι ≤ (B.card : ℝ) := by
    simpa [B] using card_agree_ge_of_mem_closeCodewordsRel C f c₀ hc₀
  have hUnion : (((A ∪ B).card : ℕ) : ℝ) ≤ Fintype.card ι := by
    exact_mod_cast Finset.card_le_univ (A ∪ B)
  have hInterEqNat : (A ∩ B).card = A.card + B.card - (A ∪ B).card := by
    have h := Finset.card_union_add_card_inter A B
    omega
  have hUnionLe : (A ∪ B).card ≤ A.card + B.card := by
    have h := Finset.card_union_add_card_inter A B
    omega
  have hInterEq : ((A ∩ B).card : ℝ) =
      (A.card : ℝ) + (B.card : ℝ) - ((A ∪ B).card : ℝ) := by
    rw [hInterEqNat, Nat.cast_sub hUnionLe]
    push_cast
    ring_nf
  have hInterLower : (1 - 2 * δ) * Fintype.card ι ≤ ((A ∩ B).card : ℝ) := by
    nlinarith [hA, hB, hUnion, hInterEq]
  have hsub : A ∩ B ⊆ V := by
    intro i hi
    simp [A, B, V] at hi ⊢
    rcases hi with ⟨hfi, hfi₀⟩
    have hcc : c i = c₀ i := by
      rw [← hfi, ← hfi₀]
    simp [hcc]
  have hcard : ((A ∩ B).card : ℝ) ≤ (V.card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  exact le_trans hInterLower hcard

end DifferenceVanish

/-! ### `#print axioms` verification anchors -/

section AxiomCheck

variable {ι : Type} [Fintype ι] [Nonempty ι]
variable {α : Type} [DecidableEq α]

example (f c : ι → α) :
    hammingDist f c = (Finset.univ.filter (fun i => f i ≠ c i)).card :=
  hammingDist_eq_card_filter_ne f c

example (C : Set (ι → α)) (f c : ι → α) {δ : ℝ}
    (hc : c ∈ closeCodewordsRel C f δ) :
    (1 - δ) * Fintype.card ι ≤
      ((Finset.univ.filter (fun i => f i = c i)).card : ℝ) :=
  card_agree_ge_of_mem_closeCodewordsRel C f c hc

example (f : ι → α) (L : Finset (ι → α)) :
    (∑ c ∈ L, (Finset.univ.filter (fun i => c i = f i)).card) =
      ∑ i : ι, (L.filter (fun c => c i = f i)).card :=
  sum_agree_swap f L

end AxiomCheck

end CodingTheory

#print axioms CodingTheory.hammingDist_eq_card_filter_ne
#print axioms CodingTheory.card_agree_eq
#print axioms CodingTheory.card_disagree_le_of_relHammingDist_le
#print axioms CodingTheory.card_agree_ge_of_mem_closeCodewordsRel
#print axioms CodingTheory.sum_agree_swap
#print axioms CodingTheory.sum_agree_ge_of_subset_closeCodewordsRel
#print axioms CodingTheory.card_diff_vanish_ge_of_mem_closeCodewordsRel
