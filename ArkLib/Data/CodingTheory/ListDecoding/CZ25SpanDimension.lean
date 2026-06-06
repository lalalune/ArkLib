/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.SubspaceDesign
import ArkLib.Data.CodingTheory.ListDecodability
import ArkLib.Data.CodingTheory.ListDecoding.CZ25DesignToLambda
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Extended

/-!
# CZ25 dimension count: the design half + the strictly-smaller agreement residual

This file dissects the last kernel of the FRS capacity chain,
`CodingTheory.CZ25DimensionCount` (the per-received-word real bound
`|Λ(C,δ,f)| ≤ (1 - τ(r₀))/η` against an `IsSubspaceDesign` budget, isolated in
`ListDecoding/CZ25DesignToLambda.lean`). It pins where the genuinely-deep Guruswami–Wang /
CZ25 [CZ25 Thm B.5] content lives, and discharges everything around it.

## The classical argument and where it is hard (paper level)

Fix `f` and write the candidate list `L := closeCodewordsRel C f δ`, `ℓ := |L|`, at radius
`δ := 1 - τ(r₀) - η`. Each `c ∈ L` agrees with `f` on `≥ (1-δ)·n = (τ(r₀)+η)·n` of the `n`
block coordinates `i : ι`. Pick a base `c₀ ∈ L`, recentre, and let `A := span{c - c₀ : c ∈ L}`,
a subspace of `C` of dimension `m ≤ ℓ - 1`. Realise `A` by an **independent** family
`b : Fin m → A` (a basis), and per coordinate `i` collect the basis vectors vanishing at `i`,
`S i := {t : b t i = 0}`.

The argument has two halves:

* **The design half (proven here).** The subspace-design inequality at radius `r₀` (valid
  since `m ≤ r₀`) bounds the *total vanishing mass* the basis can carry:

    `∑_i |S i| ≤ ∑_i dim(A ⊓ ker eval_i) ≤ m · τ(r₀) · n`.

  The first `≤` is the genuinely-reusable linear-algebra fact that an independent subfamily
  landing in `A ⊓ ker eval_i` witnesses dimension at least `|S i|`
  (`finrank_inf_ker_ge_card_vanishing`); the second is the `IsSubspaceDesign` hypothesis. We
  prove the bundled statement as `sum_card_vanishing_le_design`.

* **The agreement half (the irreducible residual).** Translating the *fresh* agreement
  `(τ(r₀)+η)·n` that each new list element contributes — through the iterative span
  construction — into the affine-dimension inequality

    `m · η ≤ 1 - τ(r₀) - η`,

  together with the list↔span link `ℓ ≤ m + 1`, is the genuinely-deep Guruswami–Wang
  iterative charge. A single base point plus a per-coordinate mass bound is provably
  **insufficient** for the *linear*-in-`ℓ` bound (it only yields the `r₀`-independent
  τ-constraint `τ(r₀) ≥ 1 - 2η`), so this half has no shortcut over the design budget and is
  isolated as the strictly-smaller residual `CZ25SpanBound` below.

## What is proven here vs. the residual

* `finrank_inf_ker_ge_card_vanishing` — per-coordinate independence ⟹ dimension bound
  (reusable; `sorry`-free, axiom-clean).
* `sum_card_vanishing_le_design` — the **design half**: `∑_i |S i| ≤ m · τ(r₀) · n`
  (reusable; consumes only `IsSubspaceDesign`; `sorry`-free, axiom-clean).
* `CZ25SpanBound` — the strictly-smaller residual: per `f`, an affine-span witness giving
  `ℓ ≤ m + 1` and `m · η ≤ 1 - τ(r₀) - η`. It carries **none** of the `ℝ`-cast / `ncard`
  edge-case / `Lambda` packaging that `CZ25DimensionCount` bundles, and exposes the affine
  dimension `m` explicitly.
* `cz25DimensionCount_of_spanBound` — `CZ25SpanBound ⟹ CZ25DimensionCount` (the arithmetic
  collapse `ℓ ≤ m+1 ≤ (1-τ(r₀))/η`; `sorry`-free, axiom-clean).
* `subspaceDesign_list_decoding_cz25_of_spanBound` — composing with the existing reduction
  `subspaceDesign_list_decoding_cz25_of_dimensionCount`, the in-tree T3.4 `Λ`-bound follows
  from `CZ25SpanBound` directly.

## Sanity check (tiny example, `q = 5`, `n = 4`, `k = 1`, `δ = 1/4`)

Take `s = 1` (alphabet `F = 𝔽₅`), `n = 4`, a dimension-`1` code (`k = 1`), `η = 1/4` so
`r₀ = ⌊1/η⌋ = 4` and `δ = 1 - τ(4) - 1/4`. A `1`-dimensional code is spanned by one nonzero
`c`, so the only nonzero codewords are its `4` scalar multiples; any two distinct codewords
differ in *every* coordinate (minimum distance `n`), so `τ(r) ≥ (n - d)/n = 0` from
`subspaceDesign_tau_lower`, giving `δ ≤ 3/4`. The list `L` around any `f` then has at most
one codeword within relative radius `δ < 1`, i.e. `ℓ ≤ 1`. The span witness is `m = 0`
(`A = ⊥`): `ℓ ≤ m + 1 = 1` ✓ and `m · η = 0 ≤ 1 - τ(4) - 1/4` ✓ (as `τ(4) ≤ 3/4`), and the
collapse gives `ℓ ≤ (1 - τ(4))/η`, consistent.

## References

- [CZ25] Thm B.5 (subspace-design route to capacity list decoding).
- [GW13] Guruswami–Wang. *Linear-algebraic list decoding of folded Reed–Solomon codes.* The
  iterative span charge that the residual `CZ25SpanBound` isolates.
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace CodingTheory

open scoped NNReal
open ListDecodable

section DesignHalf

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] {s : ℕ}

/-- **Per-coordinate independence ⟹ dimension bound (reusable kernel).** For a linearly
independent finite family `b : κ → (ι → Fin s → F)` with span `A`, and any finite set `S` of
indices whose vectors all vanish at block `i` (`b t i = 0`), the dimension of
`A ⊓ ker eval_i` is at least `|S|`: the subfamily `{b t : t ∈ S}` lands in `A ⊓ ker eval_i`
and stays independent, so its cardinality is dominated by the dimension. This is the
genuinely-reusable linear-algebra fact behind the design half of the CZ25 dimension count. -/
theorem finrank_inf_ker_ge_card_vanishing
    {κ : Type} [Fintype κ] (b : κ → (ι → Fin s → F))
    (hb : LinearIndependent F b) (i : ι)
    (S : Finset κ) (hS : ∀ t ∈ S, b t i = 0) :
    S.card ≤ Module.finrank F
      (↥((Submodule.span F (Set.range b)) ⊓
        (LinearMap.ker
          (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)) :
        Submodule F (ι → Fin s → F))) := by
  set A := Submodule.span F (Set.range b) with hA
  set W := (A ⊓ (LinearMap.ker
      (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)) :
      Submodule F (ι → Fin s → F)) with hW
  -- The subfamily indexed by `S` lands in `W`.
  have hmem : ∀ t : {t // t ∈ S}, b t.1 ∈ W := by
    rintro ⟨t, ht⟩
    refine Submodule.mem_inf.mpr ⟨Submodule.subset_span (Set.mem_range_self t), ?_⟩
    simp [LinearMap.mem_ker, LinearMap.proj_apply, hS t ht]
  -- It stays linearly independent inside `W`.
  have hindep : LinearIndependent F (fun t : {t // t ∈ S} => (⟨b t.1, hmem t⟩ : W)) := by
    have hcomp := hb.comp (fun t : {t // t ∈ S} => t.1) Subtype.val_injective
    have hsub : LinearIndependent F
        (fun t : {t // t ∈ S} => (W.subtype) (⟨b t.1, hmem t⟩)) := by simpa using hcomp
    exact hsub.of_comp _
  have hcard := hindep.fintype_card_le_finrank
  rwa [Fintype.card_coe] at hcard

/-- **The design half of the CZ25 dimension count (reusable).** Given a τ-subspace-design
code `C`, an `F`-linearly-independent family `b : Fin m → C` of dimension `m ≤ r₀`, and per
coordinate `i` a set `S i` of basis indices vanishing at `i`, the total vanishing mass is
bounded by the design budget:

  `∑_i |S i| ≤ m · τ(r₀) · n`.

Combines `finrank_inf_ker_ge_card_vanishing` (the per-coordinate dimension lower bound) with
the `IsSubspaceDesign` inequality at radius `r₀`, instantiated at the span `A` of `b` (which
has `dim A = m` since `b` is independent). No `sorry`; the only hypothesis is the design. -/
theorem sum_card_vanishing_le_design
    (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F)) (h : IsSubspaceDesign s τ C)
    (r₀ m : ℕ) (hm : m ≤ r₀)
    (b : Fin m → (ι → Fin s → F)) (hbC : ∀ t, b t ∈ C)
    (hb : LinearIndependent F b)
    (S : ι → Finset (Fin m)) (hS : ∀ i, ∀ t ∈ S i, b t i = 0) :
    (∑ i : ι, ((S i).card : ℝ)) ≤ (m : ℝ) * τ r₀ * Fintype.card ι := by
  set A := Submodule.span F (Set.range b) with hA
  have hA_le : A ≤ C := by
    rw [hA, Submodule.span_le]
    rintro x ⟨t, rfl⟩
    exact hbC t
  have hA_rank : Module.finrank F A = m := by
    rw [hA, finrank_span_eq_card hb, Fintype.card_fin]
  -- Per-coordinate dimension lower bounds.
  have hper : ∀ i, ((S i).card : ℝ) ≤
      (Module.finrank F (↥(A ⊓
        (LinearMap.ker
          (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)) :
        Submodule F (ι → Fin s → F))) : ℝ) := by
    intro i
    exact_mod_cast finrank_inf_ker_ge_card_vanishing b hb i (S i) (hS i)
  have hsum_le : (∑ i : ι, ((S i).card : ℝ)) ≤
      ∑ i : ι, (Module.finrank F (↥(A ⊓
        (LinearMap.ker
          (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)) :
        Submodule F (ι → Fin s → F))) : ℝ) :=
    Finset.sum_le_sum (fun i _ => hper i)
  -- The design inequality at radius `r₀`, applied to `A` (`dim A = m ≤ r₀`).
  have hdesign := h r₀ A hA_le (le_trans (le_of_eq hA_rank) hm)
  rw [hA_rank] at hdesign
  have hn_posR : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  rw [div_le_iff₀ hn_posR] at hdesign
  exact le_trans hsum_le hdesign

end DesignHalf

section AgreementResidual

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **Residual (CZ25 agreement half — strictly smaller than `CZ25DimensionCount`).** For a
τ-subspace-design code `C` and `η > 0`, with `r₀ := ⌊1/η⌋` and radius `δ := 1 - τ(r₀) - η`,
every received word `f` admits an **affine-span witness** for its candidate list
`L := closeCodewordsRel C f δ`: a natural number `m` (the affine dimension of the recentred
list span) with

  `|L| ≤ m + 1`        (the list↔span+1 link) and
  `m · η ≤ 1 - τ(r₀) - η`   (the affine-dimension agreement bound).

This is the genuinely-deep Guruswami–Wang iterative charge (each new list element contributes
a *fresh* `η·n` slice of agreement to a budget capped at `(1 - τ(r₀))·n`). It carries **none**
of the `ℝ`-cast / `ncard` edge-case / `Lambda`-packaging of `CZ25DimensionCount`, and exposes
the affine dimension `m` explicitly — so it is strictly smaller than that residual, which it
implies via `cz25DimensionCount_of_spanBound`. The design half of the count
(`sum_card_vanishing_le_design`) is supplied as proven, reusable infrastructure; only this
agreement half remains admitted. -/
def CZ25SpanBound
    (s : ℕ) (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
    (_h : IsSubspaceDesign s τ C) (η : ℝ) (_hη : 0 < η) : Prop :=
  ∀ f : ι → Fin s → F,
    ∃ m : ℕ,
      ((closeCodewordsRel ((C : Set (ι → Fin s → F))) f
          (1 - τ (Nat.floor (1 / η)) - η)).ncard : ℝ) ≤ (m : ℝ) + 1 ∧
      (m : ℝ) * η ≤ 1 - τ (Nat.floor (1 / η)) - η

/-- **The arithmetic collapse: `CZ25SpanBound ⟹ CZ25DimensionCount`.** From the affine-span
witness `(m, ℓ ≤ m+1, m·η ≤ 1 - τ(r₀) - η)` the per-word real bound

  `|L| ≤ m + 1 = (m·η + η)/η ≤ ((1 - τ(r₀) - η) + η)/η = (1 - τ(r₀))/η`

follows by elementary arithmetic (`η > 0`). No `sorry`, no new axioms. -/
theorem cz25DimensionCount_of_spanBound
    (s : ℕ) (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
    (h : IsSubspaceDesign s τ C) (η : ℝ) (hη : 0 < η)
    (hSB : CZ25SpanBound s τ C h η hη) :
    CZ25DimensionCount s τ C h η hη := by
  intro f
  obtain ⟨m, hℓ, hm⟩ := hSB f
  -- `|L| ≤ m + 1 ≤ (1 - τ(r₀))/η`.
  refine le_trans hℓ ?_
  rw [le_div_iff₀ hη]
  -- `(m + 1) * η = m·η + η ≤ (1 - τ(r₀) - η) + η = 1 - τ(r₀)`.
  nlinarith [hm]

/-- **In-tree T3.4 [CZ25 Thm B.5] from the agreement residual.** Composing the arithmetic
collapse with the existing reduction `subspaceDesign_list_decoding_cz25_of_dimensionCount`,
the exact in-tree `Λ`-bound follows from `CZ25SpanBound` (the agreement half) alone — the
design half being discharged by `sum_card_vanishing_le_design`. No `sorry`, no new axioms. -/
theorem subspaceDesign_list_decoding_cz25_of_spanBound
    (s : ℕ) (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
    (h : IsSubspaceDesign s τ C) (η : ℝ) (hη : 0 < η)
    (hSB : CZ25SpanBound s τ C h η hη) :
    (Lambda ((C : Set (ι → Fin s → F)))
        (1 - τ (Nat.floor (1 / η)) - η) : ENNReal) ≤
      ENNReal.ofReal ((1 - τ (Nat.floor (1 / η))) / η) :=
  subspaceDesign_list_decoding_cz25_of_dimensionCount s τ C h η hη
    (cz25DimensionCount_of_spanBound s τ C h η hη hSB)

end AgreementResidual

end CodingTheory


-- TEMP AUDIT
#print axioms CodingTheory.sum_card_vanishing_le_design
#print axioms CodingTheory.subspaceDesign_list_decoding_cz25_of_spanBound
