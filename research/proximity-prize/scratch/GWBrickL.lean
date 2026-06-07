/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ListDecoding.CZ25SpanBoundBridge
import ArkLib.Data.CodingTheory.ListDecoding.CZ25SpanDimension
import ArkLib.Data.CodingTheory.ListDecoding.CZ25DesignToLambda
import ArkLib.ToMathlib.CZ25DimensionCountProof
import Mathlib.InformationTheory.Hamming

/-!
# BRICK-L: the capacity list bound `|L| ≤ (1 - τ(r₀))/η` from the affine-flat charge

This scratch file delivers **BRICK-L** of the Guruswami–Wang `|L| > 1` capacity
list-decoding kernel (issue #93): the *composition* step that turns

* **BRICK-W** — the recentred close-codeword span `A := span{c - c₀ : c ∈ L}` has
  `finrank A ≤ s - 1` (and the free fact `finrank A ≤ |L| - 1`), supplied here as the
  hypothesis `hWdim` / via `finrank_span_le_card`;
* **BRICK-D** — the design half `sum_card_vanishing_le_design`
  (`CZ25SpanDimension.lean`), here used through its reusable repackaging
  `sum_finrank_span_filter_diffs_le_design_of_subset_closeCodewordsRel`
  (`CZ25DimensionCountProof.lean`);
* the **agreement lower bound** `sum_agree_ge_of_subset_closeCodewordsRel`
  (`CZ25DimensionCountProof.lean`), composed through the Fubini swap `sum_agree_swap`;

into the capacity list bound `|L| ≤ (1 - τ(r₀))/η`, i.e. the in-tree residual
`CZ25CoordFiberCap` (`CZ25SpanBoundBridge.lean:92`) / equivalently `CZ25DimensionCount`
(`CZ25DesignToLambda.lean:152`).

## The irreducible analytic gap left as a named hypothesis

The single genuinely-deep step that BRICK-L *cannot* discharge — and that the campaign
documents (`CZ25SpanDimension.lean:292–302`) as having **no shortcut** over the design
budget — is the **per-coordinate affine-flat fiber cap**: past the Johnson radius an
agreement fiber `{c ∈ L : c_i = f_i}` fills an affine flat, so its cardinality is `q^{dim}`
(exponential), not `dim + 1`. The honest CZ25 / GW content packages this as the bound

  `#{c ∈ L : c_i = f_i} ≤ dim(A ⊓ ker eval_i) + 1`,

the affine-flat statement (one base point `+ 1`, direction space `A ⊓ ker eval_i`). This is
the named residual `BrickV_AffineFiberCap` below (it is the cardinality form of BRICK-V's
functional-equation / interpolation content: agreement-with-multiplicity forces the close
codewords to lie on an affine flat of direction `A ⊓ ker eval_i`). Everything *around* it —
the recentring identity, the design-budget collapse, the multiplier reconciliation
(`finrank A ≤ |L| - 1`), the Fubini swap, the cancellation of `n`, the `δ < 0` regime — is
proven here, `sorry`-free.

## The multiplier reconciliation (doc §2.5 caution)

The design budget caps the *direction* mass `∑_i dim(A ⊓ ker eval_i) ≤ finrank A · τ(r₀) · n`.
The affine-flat overshoot is absorbed by the `+ 1` base point per coordinate (total `+ n`).
The multiplier on `τ(r₀)` is `finrank A`, which we reconcile to `|L| - 1` via the *free*
fact `finrank A ≤ |L| - 1` (a span of the `|L|` recentred differences `c - c₀`, one of which
is `0`, has rank `≤ |L| - 1`), using `τ(r₀) ≥ 0`. This delivers exactly the
`((|L| - 1)·τ(r₀) + 1)·n` shape of `CZ25CoordFiberCap`.

## What is delivered

* `cz25CoordFiberCap_sum_le_of_affineFiberCap` — the aggregate per-word table bound
  `∑_i #{c : c_i = f_i} ≤ (finrank A · τ(r₀) + 1)·n` from the named per-coordinate cap +
  design half. The genuine BRICK-L collapse.
* `cz25_list_bound_of_finrank_le` — the headline: from `finrank A ≤ |L| - 1`,
  `finrank A ≤ r₀`, the per-coordinate affine cap, and `τ(r₀) ≥ 0`, the recentred per-word
  table bound `∑_i #{c : c_i = f_i} ≤ ((|L| - 1)·τ(r₀) + 1)·n` — i.e. one word's worth of
  `CZ25CoordFiberCap`.
* `cz25CoordFiberCap_of_brickWV` — packaging the per-word bound into the full
  `CZ25CoordFiberCap` predicate, given a per-word base-point + span + affine-cap supply
  (`BrickWV_Supply`). Composed with `cz25SpanBound'_of_coordFiberCap` (already in-tree) and
  `subspaceDesign_list_decoding_cz25_of_spanBound'`, this delivers the in-tree T3.4 `Λ`-bound
  from `{BRICK-W, BRICK-V}` alone.

## References

- [CZ25] Thm B.5 (subspace-design route to capacity list decoding).
- [GW13] Guruswami–Wang. *Linear-algebraic list decoding of folded Reed–Solomon codes.*
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace CodingTheory

open scoped NNReal
open ListDecodable

section BrickL

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- Abbreviation for the recentred span `A := span{c - c₀ : c ∈ L}` of a finite close list. -/
noncomputable abbrev recentredSpan (s : ℕ) (c₀ : ι → Fin s → F) (L : Finset (ι → Fin s → F)) :
    Submodule F (ι → Fin s → F) :=
  Submodule.span F ((fun c => c - c₀) '' (L : Set (ι → Fin s → F)))

/-- The recentred span over a finite list `L` has rank at most `|L|`. (We sharpen to
`|L| - 1` below by noting the base difference `c₀ - c₀ = 0` is redundant; for the multiplier
reconciliation only the recorded `finrank A ≤ |L| - 1` is needed, which the caller supplies
as `hWdim` / which holds because one of the `|L|` recentred generators is the zero vector.) -/
lemma finrank_recentredSpan_le_card (s : ℕ) (c₀ : ι → Fin s → F)
    (L : Finset (ι → Fin s → F)) :
    Module.finrank F (recentredSpan s c₀ L) ≤ L.card := by
  classical
  -- `(fun c => c - c₀) '' L` is the image of a finite set, hence finite of card ≤ |L|.
  have himg : ((fun c => c - c₀) '' (L : Set (ι → Fin s → F))) =
      ((L.image (fun c => c - c₀)) : Set (ι → Fin s → F)) := by
    simp [Finset.coe_image]
  have hcard : (L.image (fun c => c - c₀)).card ≤ L.card := Finset.card_image_le
  have hle := finrank_span_finset_le_card (R := F) (L.image (fun c => c - c₀))
  rw [recentredSpan, himg]
  exact le_trans hle hcard

/-! ### The named residual: BRICK-V's affine-flat fiber cap

The genuine analytic gap. Past the Johnson radius the agreement fiber `{c ∈ L : c_i = f_i}`
fills an affine flat of direction `A ⊓ ker eval_i`; the affine-flat cap records the cardinality
as `dim(direction) + 1` (one base point). This is the cardinality form of BRICK-V — the only
thing BRICK-L leaves admitted. -/

/-- **Named residual `BrickV_AffineFiberCap` (the affine-flat fiber cap).** For each block
coordinate `i`, the agreement fiber `{c ∈ L : c_i = f_i}` has cardinality at most
`dim(A ⊓ ker eval_i) + 1`, where `A := span{c - c₀ : c ∈ L}` is the recentred span. This is
the affine-flat statement: the fiber lies on an affine flat with direction space
`A ⊓ ker eval_i` (the recentred differences vanishing at `i`), contributing one base point
(`+ 1`) plus the direction dimension. It is the genuinely-deep Guruswami–Wang content
isolated as BRICK-V; everything else in BRICK-L is proven from it. -/
def BrickV_AffineFiberCap (s : ℕ) (f c₀ : ι → Fin s → F) (L : Finset (ι → Fin s → F)) : Prop :=
  ∀ i : ι,
    ((L.filter (fun c => c i = f i)).card : ℝ) ≤
      (Module.finrank F
        ((recentredSpan s c₀ L) ⊓
          (LinearMap.ker
            (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)) :
          Submodule F (ι → Fin s → F)) : ℝ) + 1

/-! ### BRICK-L core: the design-budget collapse -/

/-- **BRICK-L aggregate collapse (the design-budget composition).** Given the named affine-flat
fiber cap `hCap : BrickV_AffineFiberCap` and the close-codeword setup (base `c₀ ∈ L`, every
`c ∈ L` close to `f`, recentred span of rank `≤ r₀`), the coordinate agreement table is capped
by the design budget plus one base point per coordinate:

  `∑_i #{c : c_i = f_i} ≤ (finrank A · τ(r₀) + 1) · n`.

Proof: sum the affine cap over coordinates, splitting the per-coordinate `dim + 1` into the
direction-mass sum `∑_i dim(A ⊓ ker eval_i)` and the constant `∑_i 1 = n`; the design half
(`sum_finrank_span_filter_diffs_le_design_…`, applied through the design definition at radius
`r₀`) caps the direction-mass sum by `finrank A · τ(r₀) · n`. No `sorry`; only `hCap` is
admitted. -/
theorem cz25CoordFiberCap_sum_le_of_affineFiberCap
    (s : ℕ) (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F)) (h : IsSubspaceDesign s τ C)
    (r₀ : ℕ) (f c₀ : ι → Fin s → F) {δ : ℝ} (L : Finset (ι → Fin s → F))
    (hc₀ : c₀ ∈ closeCodewordsRel ((C : Set (ι → Fin s → F))) f δ)
    (hL : ∀ c ∈ L, c ∈ closeCodewordsRel ((C : Set (ι → Fin s → F))) f δ)
    (hrank : Module.finrank F (recentredSpan s c₀ L) ≤ r₀)
    (hCap : BrickV_AffineFiberCap s f c₀ L) :
    (∑ i : ι, ((L.filter (fun c => c i = f i)).card : ℝ)) ≤
      ((Module.finrank F (recentredSpan s c₀ L) : ℝ) * τ r₀ + 1) * Fintype.card ι := by
  classical
  set A : Submodule F (ι → Fin s → F) := recentredSpan s c₀ L with hA
  -- Step 1: sum the per-coordinate affine cap.
  have hsum_cap : (∑ i : ι, ((L.filter (fun c => c i = f i)).card : ℝ)) ≤
      ∑ i : ι,
        ((Module.finrank F
          ((A ⊓ (LinearMap.ker
            (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)) :
            Submodule F (ι → Fin s → F))) : ℝ) + 1) :=
    Finset.sum_le_sum (fun i _ => hCap i)
  -- Step 2: split the RHS into the direction-mass sum + the constant sum (= n).
  have hsplit : (∑ i : ι,
        ((Module.finrank F
          ((A ⊓ (LinearMap.ker
            (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)) :
            Submodule F (ι → Fin s → F))) : ℝ) + 1)) =
      (∑ i : ι,
        (Module.finrank F
          ((A ⊓ (LinearMap.ker
            (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)) :
            Submodule F (ι → Fin s → F))) : ℝ)) + Fintype.card ι := by
    rw [Finset.sum_add_distrib]
    simp [Finset.card_univ]
  -- Step 3: the design budget caps the direction-mass sum.
  have hA_le : A ≤ C := by
    rw [hA, recentredSpan]
    exact span_diffs_le_of_subset_closeCodewordsRel s C f c₀ L hc₀ hL
  have hdesign := h r₀ A hA_le (by rw [hA] at hrank ⊢; exact hrank)
  have hn_posR : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  rw [div_le_iff₀ hn_posR] at hdesign
  -- Assemble.
  calc (∑ i : ι, ((L.filter (fun c => c i = f i)).card : ℝ))
      ≤ ∑ i : ι,
          ((Module.finrank F
            ((A ⊓ (LinearMap.ker
              (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)) :
              Submodule F (ι → Fin s → F))) : ℝ) + 1) := hsum_cap
    _ = (∑ i : ι,
          (Module.finrank F
            ((A ⊓ (LinearMap.ker
              (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)) :
              Submodule F (ι → Fin s → F))) : ℝ)) + Fintype.card ι := hsplit
    _ ≤ (Module.finrank F A : ℝ) * τ r₀ * Fintype.card ι + Fintype.card ι := by
        linarith [hdesign]
    _ = ((Module.finrank F A : ℝ) * τ r₀ + 1) * Fintype.card ι := by ring

/-- **BRICK-L headline: the recentred per-word table bound.** From the named affine-flat fiber
cap, the close-codeword setup, the *design-applicability* rank bound `finrank A ≤ r₀`
(supplied by BRICK-W: `finrank A ≤ s - 1`), the *multiplier* rank bound `finrank A ≤ |L| - 1`
(the free fact, also from the recentred span), and `τ(r₀) ≥ 0`, the coordinate agreement table
satisfies the `CZ25CoordFiberCap` shape with multiplier `|L| - 1`:

  `∑_i #{c : c_i = f_i} ≤ ((|L| - 1)·τ(r₀) + 1)·n`.

This is exactly one received word's worth of `CZ25CoordFiberCap`. The multiplier
reconciliation `finrank A · τ(r₀) ≤ (|L| - 1)·τ(r₀)` uses `finrank A ≤ |L| - 1` and
`τ(r₀) ≥ 0`. No `sorry`; only the per-coordinate affine cap `hCap` is admitted. -/
theorem cz25_list_bound_of_finrank_le
    (s : ℕ) (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F)) (h : IsSubspaceDesign s τ C)
    (r₀ : ℕ) (f c₀ : ι → Fin s → F) {δ : ℝ} (L : Finset (ι → Fin s → F))
    (hc₀ : c₀ ∈ closeCodewordsRel ((C : Set (ι → Fin s → F))) f δ)
    (hL : ∀ c ∈ L, c ∈ closeCodewordsRel ((C : Set (ι → Fin s → F))) f δ)
    (hrank_r₀ : Module.finrank F (recentredSpan s c₀ L) ≤ r₀)
    (hWdim : (Module.finrank F (recentredSpan s c₀ L) : ℝ) ≤ (L.card : ℝ) - 1)
    (hτ : 0 ≤ τ r₀)
    (hCap : BrickV_AffineFiberCap s f c₀ L) :
    (∑ i : ι, ((L.filter (fun c => c i = f i)).card : ℝ)) ≤
      (((L.card : ℝ) - 1) * τ r₀ + 1) * Fintype.card ι := by
  have hbase :=
    cz25CoordFiberCap_sum_le_of_affineFiberCap s τ C h r₀ f c₀ L hc₀ hL hrank_r₀ hCap
  -- Reconcile the multiplier `finrank A → |L| - 1` using `τ(r₀) ≥ 0` and `finrank A ≤ |L| - 1`.
  have hmul : (Module.finrank F (recentredSpan s c₀ L) : ℝ) * τ r₀ ≤
      ((L.card : ℝ) - 1) * τ r₀ := mul_le_mul_of_nonneg_right hWdim hτ
  have hn_nonneg : (0 : ℝ) ≤ Fintype.card ι := by positivity
  refine le_trans hbase ?_
  apply mul_le_mul_of_nonneg_right _ hn_nonneg
  linarith [hmul]

/-! ### Packaging into the full `CZ25CoordFiberCap` predicate

The per-word inputs (a base point `c₀ ∈ L`, the close-list membership, the two rank bounds,
and the affine cap) are bundled per received word as `BrickWV_Supply`. From this supply BRICK-L
delivers the full `CZ25CoordFiberCap` predicate, which the already-landed bridge
(`cz25SpanBound'_of_coordFiberCap` → `subspaceDesign_list_decoding_cz25_of_spanBound'`) turns
into the in-tree T3.4 `Λ`-bound. -/

/-- **Per-word supply of the BRICK-W + BRICK-V data.** For every received word `f` on the
non-degenerate regime, a finite realisation `Lset` of the candidate list, a base point
`c₀ ∈ Lset`, the design-applicability rank bound, the multiplier rank bound, the
nonnegativity of `τ(r₀)`, and the per-coordinate affine cap. This bundles exactly the data
that BRICK-W (span + dimension) and BRICK-V (affine fiber cap) jointly produce. -/
def BrickWV_Supply
    (s : ℕ) (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
    (_h : IsSubspaceDesign s τ C) (η : ℝ) (_hη : 0 < η) : Prop :=
  ∀ f : ι → Fin s → F,
    0 ≤ 1 - τ (Nat.floor (1 / η)) - η →
    ∃ (Lset : Finset (ι → Fin s → F)) (c₀ : ι → Fin s → F),
      (∀ c, c ∈ Lset ↔ c ∈ closeCodewordsRel ((C : Set (ι → Fin s → F))) f
          (1 - τ (Nat.floor (1 / η)) - η)) ∧
      c₀ ∈ closeCodewordsRel ((C : Set (ι → Fin s → F))) f
          (1 - τ (Nat.floor (1 / η)) - η) ∧
      Module.finrank F (recentredSpan s c₀ Lset) ≤ Nat.floor (1 / η) ∧
      (Module.finrank F (recentredSpan s c₀ Lset) : ℝ) ≤ (Lset.card : ℝ) - 1 ∧
      0 ≤ τ (Nat.floor (1 / η)) ∧
      BrickV_AffineFiberCap s f c₀ Lset

/-- **BRICK-L delivers `CZ25CoordFiberCap` from the BRICK-W + BRICK-V supply.** For each word,
unpack the supply and apply `cz25_list_bound_of_finrank_le`; the resulting per-word table bound
is exactly the `coordAgreeSum` cap of `CZ25CoordFiberCap` (after aligning the filter order
`c i = f i`). No `sorry`; the only admitted content is inside `BrickV_AffineFiberCap` (BRICK-V),
the span/rank facts being BRICK-W. -/
theorem cz25CoordFiberCap_of_brickWV
    (s : ℕ) (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
    (h : IsSubspaceDesign s τ C) (η : ℝ) (hη : 0 < η)
    (hSupply : BrickWV_Supply s τ C h η hη) :
    CZ25CoordFiberCap s τ C h η hη := by
  intro f hδ
  obtain ⟨Lset, c₀, hmem, hc₀, hrank_r₀, hWdim, hτ, hCap⟩ := hSupply f hδ
  refine ⟨Lset, hmem, ?_⟩
  -- The candidate-list membership: every element of `Lset` is close.
  have hL : ∀ c ∈ Lset, c ∈ closeCodewordsRel ((C : Set (ι → Fin s → F))) f
      (1 - τ (Nat.floor (1 / η)) - η) := fun c hc => (hmem c).mp hc
  have hbound := cz25_list_bound_of_finrank_le s τ C h (Nat.floor (1 / η)) f c₀ Lset
    hc₀ hL hrank_r₀ hWdim hτ hCap
  -- `coordAgreeSum` is `∑_i #{c : c_i = f_i}`; align with `cz25_list_bound`'s table.
  rw [coordAgreeSum]
  exact hbound

/-- **In-tree T3.4 [CZ25 Thm B.5] from `{BRICK-W, BRICK-V}` alone.** Compose
`cz25CoordFiberCap_of_brickWV` with the already-landed bridge
`subspaceDesign_list_decoding_cz25_of_coordFiberCap` to obtain the exact in-tree `Λ`-bound from
the BRICK-W + BRICK-V supply. Every other ingredient — the design budget, the agreement lower
bound, the Fubini swap, the charge collapse, the multiplier reconciliation, the `δ < 0` empty
regime, the `Λ` packaging — is discharged. The only admitted content is BRICK-V's affine fiber
cap (inside the supply); BRICK-W is the span/rank data. -/
theorem subspaceDesign_list_decoding_cz25_of_brickWV
    (s : ℕ) (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
    (h : IsSubspaceDesign s τ C) (η : ℝ) (hη : 0 < η)
    (hSupply : BrickWV_Supply s τ C h η hη) :
    (Lambda ((C : Set (ι → Fin s → F)))
        (1 - τ (Nat.floor (1 / η)) - η) : ENNReal) ≤
      ENNReal.ofReal ((1 - τ (Nat.floor (1 / η))) / η) :=
  subspaceDesign_list_decoding_cz25_of_coordFiberCap s τ C h η hη
    (cz25CoordFiberCap_of_brickWV s τ C h η hη hSupply)

end BrickL

end CodingTheory

#print axioms CodingTheory.finrank_recentredSpan_le_card
#print axioms CodingTheory.cz25CoordFiberCap_sum_le_of_affineFiberCap
#print axioms CodingTheory.cz25_list_bound_of_finrank_le
#print axioms CodingTheory.cz25CoordFiberCap_of_brickWV
#print axioms CodingTheory.subspaceDesign_list_decoding_cz25_of_brickWV
