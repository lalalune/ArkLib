/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Hab25CurveCellProduction
import ArkLib.Data.CodingTheory.ProximityGap.Hab25CurveCellStrictExtraction

/-!
# Cell cover and heavy-cell attribution for a GIVEN decode family (#304, SK4 brick)

`exists_curve_cell_production` decomposes the bad scalars into cells for a decode family
of its OWN choosing.  The share-form residual (`StrictCoeffPolysShareResidual`) quantifies
over an ARBITRARY decoded family `P`, so the production shape cannot feed it directly.
This file closes that gap at the `McaDecodeCurve` interface:

* `exists_curve_cell_cover_of_given_family` — the cell decomposition for a GIVEN scalar
  set `G` and a GIVEN family `P` witnessed by decodes (`d.P = P γ`): `≤ #factors(Q₀) + 1`
  cells covering `G`, each cell inside `G`, one degenerate cell of size `≤ T`, and a
  single irreducible factor of `Q₀` per remaining cell with
  `(X − C (P γ)) ∣ R|_{Z:=γ}` — for THIS `P`.  The chosen-family production is the special
  case `G := bad`, `P := the chosen decodes`; the proof is the same attribution argument
  (`mcaDecodeCurve_matching_dvd` + prime-into-product factor assignment), with the choice
  step deleted.
* `exists_heavy_factor_cell_of_given_family` — composed with the SK2 pigeonhole
  (`exists_heavy_factor_cell`): whenever `T < |G|`, some irreducible factor `R` of `Q₀`
  carries a `1/#factors(Q₀)` share of `G`:
  `|G| ≤ T + #factors(Q₀)·|G′|` with `G′ ⊆ G` and the per-`γ` divisibility for the GIVEN
  family on all of `G′`.

This is the `∀ P` attribution package the share producer needs: what remains between this
and `StrictCoeffPolysShareResidual` is the per-rich-cell surface supply
(`(Y − C w) ∣ R` with degree bounds — the S10-converse lane), the heavy-coordinate
matching sets, and the `L`-ary Z-degree-bounded interpolant budget for `T`.

Axiom-clean: `[propext, Classical.choice, Quot.sound]` (audited at end of file).
-/

set_option linter.unusedSectionVars false

namespace CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

open Polynomial Polynomial.Bivariate Finset
open GuruswamiSudan.OverRatFunc
open _root_.ProximityGap Code
open scoped NNReal ENNReal

attribute [local instance] Classical.propDecidable

variable {F₀ : Type} [Field F₀] [Fintype F₀] [DecidableEq F₀]

/-- **The cell decomposition for a GIVEN decode family.**  Mirror of
`exists_curve_cell_production` with the scalar set `G` and the decoded family `P` given as
inputs (each `γ ∈ G` witnessed by a decode with `d.P = P γ`): the cells cover `G`, live
inside `G`, the degenerate cell has size `≤ T`, and each factor cell carries one
irreducible factor of `Q₀` dividing at the GIVEN family's values. -/
theorem exists_curve_cell_cover_of_given_family {n k m L : ℕ} [NeZero n]
    (domain : Fin n ↪ F₀)
    (u : WordStack F₀ (Fin L) (Fin n)) (δ : ℝ≥0) (T : ℕ)
    {Q : (RatFunc F₀)[X][Y]} {dd : F₀[X]} {Q₀ : (F₀[X])[X][Y]}
    (hQ : GuruswamiSudan.Conditions k m (gs_degree_bound k n m)
      (liftedDomain domain) (curveFold (fun j i => u j i)) Q)
    (hrep : Q₀.map (Polynomial.mapRingHom (algebraMap F₀[X] (RatFunc F₀))) =
      Polynomial.C (Polynomial.C (algebraMap F₀[X] (RatFunc F₀) dd)) * Q)
    (hQ₀0 : Q₀ ≠ 0)
    (hkn : k + 1 ≤ n) (hm : 1 ≤ m)
    (hδ1 : δ ≤ 1) (hδJ : (δ : ℝ) < gs_johnson k n m)
    (hbadz : ∀ S : Finset F₀,
      (∀ z ∈ S, Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) = 0) →
      S.card ≤ T)
    (G : Finset F₀) (P : F₀ → F₀[X])
    (hPdec : ∀ γ ∈ G, ∃ d : McaDecodeCurve domain k δ u γ, d.P = P γ) :
    ∃ (Index : Finset (Option ((F₀[X])[X][Y])))
      (Ecell : Option ((F₀[X])[X][Y]) → Finset F₀),
      Index.card ≤ (UniqueFactorizationMonoid.factors Q₀).toFinset.card + 1 ∧
      (∀ γ ∈ G, ∃ ij ∈ Index, γ ∈ Ecell ij) ∧
      (∀ ij, Ecell ij ⊆ G) ∧
      none ∈ Index ∧ (Ecell none).card ≤ T ∧
      (∀ R : (F₀[X])[X][Y], some R ∈ Index →
        R ∈ (UniqueFactorizationMonoid.factors Q₀).toFinset ∧
        ∀ γ ∈ Ecell (some R),
          Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)) ≠ 0 ∧
          (Polynomial.X - Polynomial.C (P γ)) ∣
            R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ))) := by
  classical
  -- the factor assignment for the non-degenerate scalars, at the GIVEN family
  have hassign : ∀ γ ∈ G,
      Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)) ≠ 0 →
      ∃ R ∈ (UniqueFactorizationMonoid.factors Q₀).toFinset,
        (Polynomial.X - Polynomial.C (P γ)) ∣
          R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)) := by
    intro γ hγ hz
    obtain ⟨d, hd⟩ := hPdec γ hγ
    have hdvd : (Polynomial.X - Polynomial.C (P γ)) ∣
        Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)) := by
      rw [← hd]
      exact mcaDecodeCurve_matching_dvd domain hQ hrep hkn hm hδ1 hδJ d hz
    obtain ⟨R, hRmem, hRd⟩ :=
      exists_integral_factor_assignment_multiset hQ₀0 γ (P γ) hdvd
    exact ⟨R, Multiset.mem_toFinset.mpr hRmem, hRd⟩
  -- the cells: `none` is the degenerate cell, `some R` the factor cells
  have hex2 : ∀ γ : F₀, ∃ ij : Option ((F₀[X])[X][Y]),
      ((γ ∈ G ∧ Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)) ≠ 0) →
        ∃ R ∈ (UniqueFactorizationMonoid.factors Q₀).toFinset, ij = some R ∧
          (Polynomial.X - Polynomial.C (P γ)) ∣
            R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ))) ∧
      (¬ (γ ∈ G ∧ Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)) ≠ 0) →
        ij = none) := by
    intro γ
    by_cases h : γ ∈ G ∧
        Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)) ≠ 0
    · obtain ⟨R, hR, hdvd⟩ := hassign γ h.1 h.2
      exact ⟨some R, fun _ => ⟨R, hR, rfl, hdvd⟩, fun hc => absurd h hc⟩
    · exact ⟨none, fun hc => absurd hc h, fun _ => rfl⟩
  choose assign hassignpos hassignneg using hex2
  set Index : Finset (Option ((F₀[X])[X][Y])) :=
    insert none ((UniqueFactorizationMonoid.factors Q₀).toFinset.image some) with hIndex
  set Ecell : Option ((F₀[X])[X][Y]) → Finset F₀ :=
    fun ij => G.filter (fun γ => assign γ = ij) with hEcell
  refine ⟨Index, Ecell, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- index count
    simp only [hIndex]
    refine le_trans (Finset.card_insert_le _ _) ?_
    have h := Finset.card_image_le
      (s := (UniqueFactorizationMonoid.factors Q₀).toFinset) (f := Option.some)
    omega
  · -- cover
    intro γ hγ
    refine ⟨assign γ, ?_, ?_⟩
    · simp only [hIndex]
      by_cases h : γ ∈ G ∧
          Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)) ≠ 0
      · obtain ⟨R, hR, hEq, _⟩ := hassignpos γ h
        rw [hEq]
        exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hR)
      · rw [hassignneg γ h]
        exact Finset.mem_insert_self _ _
    · exact Finset.mem_filter.mpr ⟨hγ, rfl⟩
  · -- every cell lives inside `G`
    intro ij
    exact Finset.filter_subset _ _
  · -- the degenerate cell is indexed
    simp only [hIndex]
    exact Finset.mem_insert_self _ _
  · -- the degenerate cell is small: its members specialize `Q₀` to zero
    refine hbadz (Ecell none) ?_
    intro γ hγ
    have hγ' : γ ∈ G.filter (fun γ' => assign γ' = none) := hγ
    obtain ⟨hγG, hass⟩ := Finset.mem_filter.mp hγ'
    by_contra hz
    obtain ⟨R, _, hEq, _⟩ := hassignpos γ ⟨hγG, hz⟩
    rw [hass] at hEq
    exact absurd hEq.symm (Option.some_ne_none _)
  · -- every factor cell carries its irreducible factor of `Q₀`, nondegenerately
    intro R hRIndex
    simp only [hIndex, Finset.mem_insert] at hRIndex
    rcases hRIndex with h | h
    · exact absurd h (Option.some_ne_none R)
    · obtain ⟨R', hR', hEq⟩ := Finset.mem_image.mp h
      obtain rfl : R' = R := Option.some.inj hEq
      refine ⟨hR', ?_⟩
      intro γ hγ
      have hγ' : γ ∈ G.filter (fun γ' => assign γ' = some R') := hγ
      obtain ⟨hγG, hass⟩ := Finset.mem_filter.mp hγ'
      by_cases hz : Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)) ≠ 0
      · obtain ⟨R'', hR'', hEq2, hdvd⟩ := hassignpos γ ⟨hγG, hz⟩
        rw [hass] at hEq2
        exact ⟨hz, by rwa [← Option.some.inj hEq2] at hdvd⟩
      · rw [hassignneg γ (fun hc => hz hc.2)] at hass
        exact absurd hass.symm (Option.some_ne_none _)

omit [DecidableEq F₀] in
/-- Instance-free (membership-form) wrapper of the SK2 cell pigeonhole
`exists_heavy_factor_cell`. -/
theorem exists_heavy_factor_cell_mem {Idx : Type} (G : Finset F₀)
    (Index : Finset (Option Idx)) (Ecell : Option Idx → Finset F₀) {ℓ T : ℕ}
    (hIdx : Index.card ≤ ℓ + 1) (hnone : none ∈ Index)
    (hcover : ∀ γ ∈ G, ∃ ij ∈ Index, γ ∈ Ecell ij)
    (hnoneCard : (Ecell none).card ≤ T) (hbig : T < G.card) :
    ∃ R : Idx, some R ∈ Index ∧ G.card ≤ T + ℓ * (Ecell (some R)).card := by
  classical
  refine BCIKS20.CurveCellStrictExtraction.exists_heavy_factor_cell G Index Ecell
    hIdx hnone ?_ hnoneCard hbig
  intro γ hγ
  obtain ⟨ij, h1, h2⟩ := hcover γ hγ
  exact Finset.mem_biUnion.mpr ⟨ij, h1, h2⟩

/-- **The heavy-cell attribution for a GIVEN decode family** (the `∀ P` share package):
whenever `T < |G|`, some irreducible factor `R` of `Q₀` carries a `1/#factors(Q₀)` share
of `G` — a subset `G′ ⊆ G` with `|G| ≤ T + #factors(Q₀)·|G′|` on which the GIVEN family
divides `R`'s specializations.  This is exactly the input shape of the SK1/SK2 strict
extraction (`strict_coeffPolys_of_cell`) and the conclusion shape of
`StrictCoeffPolysShareResidual` (share `ℓ = #factors(Q₀)`, budget `T`). -/
theorem exists_heavy_factor_cell_of_given_family {n k m L : ℕ} [NeZero n]
    (domain : Fin n ↪ F₀)
    (u : WordStack F₀ (Fin L) (Fin n)) (δ : ℝ≥0) (T : ℕ)
    {Q : (RatFunc F₀)[X][Y]} {dd : F₀[X]} {Q₀ : (F₀[X])[X][Y]}
    (hQ : GuruswamiSudan.Conditions k m (gs_degree_bound k n m)
      (liftedDomain domain) (curveFold (fun j i => u j i)) Q)
    (hrep : Q₀.map (Polynomial.mapRingHom (algebraMap F₀[X] (RatFunc F₀))) =
      Polynomial.C (Polynomial.C (algebraMap F₀[X] (RatFunc F₀) dd)) * Q)
    (hQ₀0 : Q₀ ≠ 0)
    (hkn : k + 1 ≤ n) (hm : 1 ≤ m)
    (hδ1 : δ ≤ 1) (hδJ : (δ : ℝ) < gs_johnson k n m)
    (hbadz : ∀ S : Finset F₀,
      (∀ z ∈ S, Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) = 0) →
      S.card ≤ T)
    (G : Finset F₀) (P : F₀ → F₀[X])
    (hPdec : ∀ γ ∈ G, ∃ d : McaDecodeCurve domain k δ u γ, d.P = P γ)
    (hbig : T < G.card) :
    ∃ R : (F₀[X])[X][Y],
      R ∈ (UniqueFactorizationMonoid.factors Q₀).toFinset ∧
      Irreducible R ∧
      ∃ G' : Finset F₀,
        G' ⊆ G ∧
        G.card ≤ T + (UniqueFactorizationMonoid.factors Q₀).toFinset.card * G'.card ∧
        ∀ γ ∈ G',
          Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)) ≠ 0 ∧
          (Polynomial.X - Polynomial.C (P γ)) ∣
            R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)) := by
  classical
  obtain ⟨Index, Ecell, hcardI, hcover, hsubG, hnone, hbadcell, hfactor⟩ :=
    exists_curve_cell_cover_of_given_family domain u δ T hQ hrep hQ₀0 hkn hm hδ1 hδJ
      hbadz G P hPdec
  obtain ⟨R, hRIdx, hRcount⟩ :=
    exists_heavy_factor_cell_mem G Index Ecell hcardI hnone hcover hbadcell hbig
  obtain ⟨hRmem, hRdvd⟩ := hfactor R hRIdx
  exact ⟨R, hRmem,
    UniqueFactorizationMonoid.irreducible_of_factor R
      (Multiset.mem_toFinset.mp hRmem),
    Ecell (some R), hsubG _, hRcount, hRdvd⟩

end CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

/-! ## Axiom audit — all kernel-clean. -/
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms exists_curve_cell_cover_of_given_family
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms exists_heavy_factor_cell_mem
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms exists_heavy_factor_cell_of_given_family
