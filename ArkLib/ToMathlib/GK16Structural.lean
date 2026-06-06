/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ToMathlib.GK16Claim16Witness
import ArkLib.Data.CodingTheory.ReedSolomon.Folded
import Mathlib.FieldTheory.Finiteness

/-!
# GK16 Claim 16: structural encoder-isomorphism + adapted-basis transport (proven)

This file discharges the last structural residual of GK16 Claim 16 — the
*encoder-isomorphism + adapted-basis* transport that `GK16Claim16StructuralData`
(in `SubspaceDesign.lean`) packages — under the genuine, documented side conditions.

The core pieces are:

* `exists_adapted_basis` — a generic linear-algebra brick: any subspace `W` of a
  finite-dimensional space `V` admits a `Fin (finrank V)`-indexed basis of `V` together
  with a `finrank W`-element index set whose basis vectors lie in `W` (extend a basis of
  `W` to a basis of `V`).
* `exists_recombination_of_bases` — two `Fin n`-bases of a submodule `A'` of `F[X]` are
  related by an *invertible* `F`-linear recombination of polynomials (`bQ l = ∑ c l m • bP m`,
  `det c ≠ 0`).
* `gk16_realizing_family` — the encoder-isomorphism transport: for `A ≤ frsCode` and the
  encoder injective, a basis of the polynomial pre-image subspace `A' ≤ degreeLT F k` gives
  an independent realizing family `P : Fin (dim A) → F[X]` of degrees `< k`.
* `gk16Claim16StructuralData_at` — assembles the per-coordinate adapted recombination with
  its `dim A_i`-element orbit-vanishing index set (under `dim A ≤ s`), i.e. the body of
  `GK16Claim16StructuralData` for a single `A`.

The two side conditions are exactly the ones documented on `frs_is_subspaceDesign_gk16`:
encoder injectivity (`h_encoder_inj`, the `dim_frsCode` hypothesis) and the design-range
bound `dim A ≤ s` (so the `dim A` dilation exponents are genuine fold indices `< s`).
The `ω`-degree-separation admissibility (`hω_sep`) is threaded through as the third
conjunct of the structural data; the multiplicity-counting engine itself
(`claim16_rootMultiplicity_ge`) and Lemma 12 are already proven.

Everything here is `sorry`/axiom-clean.
-/

open Submodule Module Polynomial Matrix

namespace ArkLib.FRS.GK16

/-! ## Generic linear-algebra bricks -/

section LinearAlgebra

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]

/-- **Extend a subspace basis to an adapted basis of the whole space.** For a subspace
`W ≤ V` of a finite-dimensional space, there is a `Fin (finrank V)`-indexed basis `b` of `V`
and a `finrank W`-element index set `T` with every `b l` (`l ∈ T`) lying in `W`. This is the
"extend a basis of `W` to a basis of `V`" fact, packaged with the `Fin`-reindexing and the
distinguished index set that the GK16 adapted-basis transport consumes. -/
theorem exists_adapted_basis (W : Submodule F V) :
    ∃ (b : Basis (Fin (finrank F V)) F V) (T : Finset (Fin (finrank F V))),
      T.card = finrank F W ∧ (∀ l ∈ T, b l ∈ W) := by
  classical
  set d := finrank F W with hd
  let bW : Basis (Fin d) F W := finBasis F W
  set wv : Fin d → V := fun i => (bW i : V) with hwv
  have hwv_inj : Function.Injective wv := fun a c h => bW.injective (Subtype.ext h)
  have hwv_indep : LinearIndependent F wv := bW.linearIndependent.map' W.subtype (by simp)
  set s : Set V := Set.range wv with hs_def
  have hsW : s ⊆ (W : Set V) := by
    rintro x ⟨i, rfl⟩; exact (bW i).2
  have hs : LinearIndepOn F id s := (linearIndepOn_id_range_iff hwv_inj).mpr hwv_indep
  have hs_card : s.toFinset.card = d := by
    rw [Set.toFinset_range, Finset.card_image_of_injective _ hwv_inj, Finset.card_univ,
      Fintype.card_fin]
  let E := hs.extend (Set.subset_univ s)
  let B : Basis (↥E) F V := Basis.extend hs
  have hBself : ∀ x : ↥E, B x = (x : V) := Basis.extend_apply_self hs
  have hfin : Fintype.card (↥E) = finrank F V := by rw [← Module.finrank_eq_card_basis B]
  let e : (↥E) ≃ Fin (finrank F V) := Fintype.equivFinOfCardEq hfin
  let b : Basis (Fin (finrank F V)) F V := B.reindex e
  have hsE : s ⊆ E := hs.subset_extend _
  have hb_apply : ∀ l, b l = ((e.symm l : ↥E) : V) := by
    intro l; rw [Basis.reindex_apply, hBself]
  have hs_range : s ⊆ Set.range b := by
    intro x hx
    refine ⟨e ⟨x, hsE hx⟩, ?_⟩
    rw [hb_apply]; simp
  refine ⟨b, Finset.univ.filter (fun l => b l ∈ s), ?_, ?_⟩
  · refine Eq.trans ?_ hs_card
    apply Finset.card_bij (fun l _ => b l)
    · intro l hl; rw [Finset.mem_filter] at hl; simpa using hl.2
    · intro l1 h1 l2 h2 heq; exact b.injective heq
    · intro x hx
      rw [Set.mem_toFinset] at hx
      obtain ⟨l, rfl⟩ := hs_range hx
      exact ⟨l, by rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hx⟩, rfl⟩
  · intro l hl
    rw [Finset.mem_filter] at hl
    exact hsW hl.2

end LinearAlgebra

/-! ## Recombination of two bases of a polynomial submodule -/

variable {F : Type*} [Field F]

/-- **Two bases of a polynomial submodule are an invertible recombination.** Given two
`Fin n`-indexed bases `bP`, `bQ` of a submodule `A' ≤ F[X]`, the change of coordinates
expressing `bQ` in `bP` is an *invertible* `F`-linear recombination of the underlying
polynomials: `bQ l = ∑ m, c l m • bP m` with `det c ≠ 0`. -/
theorem exists_recombination_of_bases {n : ℕ} (A' : Submodule F (Polynomial F))
    (bP bQ : Basis (Fin n) F A') :
    ∃ c : Fin n → Fin n → F, (Matrix.of c).det ≠ 0 ∧
      (∀ l, ((bQ l : Polynomial F)) = ∑ m, c l m • ((bP m : Polynomial F))) := by
  classical
  refine ⟨fun l m => bP.repr (bQ l) m, ?_, ?_⟩
  · have heq : (Matrix.of (fun l m => bP.repr (bQ l) m))
        = (bP.toMatrix (fun l => (bQ l : A')))ᵀ := by
      ext l m
      simp [Basis.toMatrix_apply]
    rw [heq, Matrix.det_transpose]
    apply Matrix.det_ne_zero_of_left_inverse (B := bQ.toMatrix ⇑bP)
    rw [Basis.toMatrix_mul_toMatrix, Basis.toMatrix_self]
  · intro l
    have hsum : (∑ m, (bP.repr (bQ l) m) • (bP m)) = bQ l := bP.sum_repr (bQ l)
    have h2 := congrArg (Submodule.subtype A') hsum
    rw [map_sum] at h2
    simp only [map_smul, Submodule.subtype_apply] at h2
    exact h2.symm

end ArkLib.FRS.GK16
