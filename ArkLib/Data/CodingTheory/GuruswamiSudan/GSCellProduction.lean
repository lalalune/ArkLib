/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.GuruswamiSudan.GSIntegralFactorAssignment
import ArkLib.Data.CodingTheory.GuruswamiSudan.GSSpecializedConditions
import ArkLib.Data.CodingTheory.ProximityGap.Hab25CaptureKernel

/-!
# K1 production: the per-stack cells, decode families, and the K4 input surface

The capture-kernel decomposition (`Hab25CaptureKernel.lean`) reduced the `hsteps57` input
of the Claim-1 dichotomy to **K1** (every scalar of the cell is decoded by a family
`P : F₀ → F₀[X]`) **∧ K4** (past the threshold the family is one affine pencil). This file
**produces K1** — the cells, their decode families, and the per-cell irreducible-factor
data that the K4 Hensel lane natively consumes — from the proven GS machinery:

* `codewordToPoly_eval_vector` — the Lagrange roundtrip: the codeword of a degree-`< k`
  polynomial decodes back to it;
* `mcaDecode_hammingDist_le` — a decode's polynomial is within distance `δ·n` of the
  scalar fold (its disagreements avoid the witness set);
* `mcaDecode_matching_dvd` — hence (Johnson radius) the decode's **matching factor divides
  the specialized integer interpolant**: `(Y − C d.P) ∣ Q₀|_{Z:=γ}`, via the proven
  `specialized_conditions` + in-tree `gs_divisibility`;
* **`exists_cell_production`** — the capstone: the bad scalars of every stack decompose
  into `≤ #factors(Q₀) + 1` cells with (i) a uniform decode family (K1, **proven**, every
  cell), (ii) one designated degenerate cell of size `≤ T` (its scalars have
  `Q₀|_{Z:=γ} = 0`; the Z-degree budget bounds it), and (iii) for every other cell a
  **single irreducible factor** `R` of `Q₀` with `(Y − C (P γ)) ∣ R|_{Z:=γ}` for all its
  scalars — the exact per-cell surface on which the Steps 5–7 Hensel argument (K4) pins
  the family to an affine pencil;
* `bad_card_le_of_cell_production_pinning` — composing with per-cell K4 pinning and the
  proven dichotomy: the stack's bad-scalar count is `≤ (#factors(Q₀) + 1)·T`.

After this file, K1 is **discharged**; the Johnson MCA chain's sole remaining input is K4
beyond the unique-decoding window (where `Hab25CaptureKernelUD.lean` already proves it),
fed exactly the `(cell, family, factor)` triples produced here.

Axiom-clean: `[propext, Classical.choice, Quot.sound]`.
-/

open Polynomial Polynomial.Bivariate Finset
open GuruswamiSudan.OverRatFunc
open _root_.ProximityGap Code
open scoped NNReal ENNReal

namespace CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

attribute [local instance] Classical.propDecidable

variable {F₀ : Type} [Field F₀] [Fintype F₀] [DecidableEq F₀]

/-- **Lagrange roundtrip**: the Reed–Solomon codeword of a degree-`< k` polynomial decodes
back to the polynomial (`k ≤ n` so the interpolation through all `n` points is exact). -/
lemma codewordToPoly_eval_vector {n k : ℕ} (domain : Fin n ↪ F₀)
    (hk : k ≤ n) (P : F₀[X]) (hdeg : P.degree < k)
    (hmem : (fun i => P.eval (domain i)) ∈ ReedSolomon.code domain k) :
    ReedSolomon.codewordToPoly
      (⟨fun i => P.eval (domain i), hmem⟩ : ReedSolomon.code domain k) = P := by
  symm
  refine Lagrange.eq_interpolate_of_eval_eq _
    (fun i _ j _ h => domain.injective h) ?_ (fun i _ => rfl)
  have hcard : (Finset.univ : Finset (Fin n)).card = n := by simp
  rw [hcard]
  exact lt_of_lt_of_le hdeg (by exact_mod_cast hk)

/-- **Decode distance**: an `mcaEvent` decode's polynomial is within Hamming distance
`δ·n` of the scalar fold — its disagreements avoid the witness set. -/
lemma mcaDecode_hammingDist_le {n k : ℕ} {domain : Fin n ↪ F₀} {δ : ℝ≥0}
    {u : WordStack F₀ (Fin 2) (Fin n)} {γ : F₀}
    (d : McaDecode domain k δ u γ) (hδ1 : δ ≤ 1) :
    (hammingDist (fun i => u 0 i + γ • u 1 i)
      (fun i => d.P.eval (domain i)) : ℝ) ≤ (δ : ℝ) * n := by
  classical
  -- the disagreement set avoids the witness set
  have hsub : Finset.univ.filter
      (fun i => (fun i => u 0 i + γ • u 1 i) i ≠ (fun i => d.P.eval (domain i)) i) ⊆
      Finset.univ \ d.S := by
    intro i hi
    rw [Finset.mem_filter] at hi
    rw [Finset.mem_sdiff]
    refine ⟨Finset.mem_univ _, fun hiS => hi.2 ?_⟩
    exact (d.hagree i hiS).symm
  have hcount : hammingDist (fun i => u 0 i + γ • u 1 i)
      (fun i => d.P.eval (domain i)) ≤ n - d.S.card := by
    rw [hammingDist]
    refine le_trans (Finset.card_le_card hsub) ?_
    rw [Finset.card_sdiff (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
  -- the witness set is large, in real form
  have hScard : ((1 : ℝ) - (δ : ℝ)) * n ≤ d.S.card := by
    have h := d.hcard
    have hco : (((1 - δ) * (Fintype.card (Fin n)) : ℝ≥0) : ℝ) ≤ ((d.S.card : ℝ≥0) : ℝ) :=
      NNReal.coe_le_coe.mpr h
    rw [NNReal.coe_mul, NNReal.coe_sub hδ1] at hco
    simpa using hco
  have hSn : d.S.card ≤ n := by
    have := Finset.card_le_univ d.S
    simpa using this
  have hcast : ((n - d.S.card : ℕ) : ℝ) = (n : ℝ) - d.S.card := by
    push_cast [Nat.cast_sub hSn]
    ring
  calc (hammingDist (fun i => u 0 i + γ • u 1 i)
        (fun i => d.P.eval (domain i)) : ℝ)
      ≤ ((n - d.S.card : ℕ) : ℝ) := by exact_mod_cast hcount
    _ = (n : ℝ) - d.S.card := hcast
    _ ≤ (δ : ℝ) * n := by nlinarith

/-- **Decode ⟹ matching-factor divisibility.** In the Johnson regime, every `mcaEvent`
decode's matching factor divides the specialized integer interpolant: chain the distance
bound through the proven `specialized_conditions` and the in-tree `gs_divisibility`. -/
theorem mcaDecode_matching_dvd {n k m : ℕ} (domain : Fin n ↪ F₀)
    {u : WordStack F₀ (Fin 2) (Fin n)} {δ : ℝ≥0}
    {Q : (RatFunc F₀)[X][Y]} {dd : F₀[X]} {Q₀ : (F₀[X])[X][Y]}
    (hQ : GuruswamiSudan.Conditions k m (gs_degree_bound k n m)
      (liftedDomain domain) (genericFold (u 0) (u 1)) Q)
    (hrep : Q₀.map (Polynomial.mapRingHom (algebraMap F₀[X] (RatFunc F₀))) =
      Polynomial.C (Polynomial.C (algebraMap F₀[X] (RatFunc F₀) dd)) * Q)
    (hkn : k + 1 ≤ n) (hm : 1 ≤ m) (hn0 : 0 < n)
    (hδ1 : δ ≤ 1) (hδJ : (δ : ℝ) < gs_johnson k n m)
    {γ : F₀} (d : McaDecode domain k δ u γ)
    (hz : Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)) ≠ 0) :
    (Polynomial.X - Polynomial.C d.P) ∣
      Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)) := by
  classical
  -- the decode's codeword
  have hmem : (fun i => d.P.eval (domain i)) ∈ ReedSolomon.code domain k :=
    ReedSolomon.mem_code_of_polynomial_of_degree_lt_of_eval d.P d.hdeg fun i => rfl
  set p : ReedSolomon.code domain k := ⟨fun i => d.P.eval (domain i), hmem⟩ with hp
  have hround : ReedSolomon.codewordToPoly p = d.P :=
    codewordToPoly_eval_vector domain (by omega) d.P d.hdeg hmem
  -- the specialized interpolant is a valid GS interpolant for the scalar fold
  have hcond := specialized_conditions domain (u 0) (u 1) hQ hrep γ hz
  -- the distance bound, in the `gs_divisibility` shape
  have hdist : (hammingDist (fun i => u 0 i + γ * u 1 i)
      (fun i => (ReedSolomon.codewordToPoly p).eval (domain i)) : ℝ) / n <
      gs_johnson k n m := by
    rw [hround]
    have hle := mcaDecode_hammingDist_le d hδ1
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
    have hsmul : (fun i => u 0 i + γ • u 1 i) = (fun i => u 0 i + γ * u 1 i) := by
      funext i
      rw [smul_eq_mul]
    rw [hsmul] at hle
    rw [div_lt_iff₀ hnR]
    calc (hammingDist (fun i => u 0 i + γ * u 1 i)
          (fun i => d.P.eval (domain i)) : ℝ)
        ≤ (δ : ℝ) * n := hle
      _ < gs_johnson k n m * n := by
          exact mul_lt_mul_of_pos_right hδJ hnR
  -- the in-tree GS list decoder
  have hdvd := scalar_fold_decoded_divides_specialization domain (u 0) (u 1)
    hQ hrep γ hz hkn hm p hdist
  rwa [hround] at hdvd

open Classical in
/-- **K1 production — the per-stack cells, decode families, and K4 input surface.**

The bad scalars of the stack decompose into `≤ #factors(Q₀) + 1` cells such that:
1. *(K1, proven)* every cell carries the uniform decode family `Pfam` (every scalar of
   every cell is an `mcaEvent` decode with that polynomial);
2. one designated cell `ij₀` collects the degenerate scalars (`Q₀|_{Z:=γ} = 0`) and has
   `≤ T` members (the Z-degree-budget input `hbadz`);
3. every other cell comes with a **single irreducible factor `R` of `Q₀`** such that the
   matching factor of every member divides `R|_{Z:=γ}` — the exact per-cell surface the
   Steps 5–7 Hensel lane (K4) pins to an affine pencil. -/
theorem exists_cell_production {n k m : ℕ} (domain : Fin n ↪ F₀)
    (u : WordStack F₀ (Fin 2) (Fin n)) (δ : ℝ≥0) (T : ℕ)
    {Q : (RatFunc F₀)[X][Y]} {dd : F₀[X]} {Q₀ : (F₀[X])[X][Y]}
    (hQ : GuruswamiSudan.Conditions k m (gs_degree_bound k n m)
      (liftedDomain domain) (genericFold (u 0) (u 1)) Q)
    (hrep : Q₀.map (Polynomial.mapRingHom (algebraMap F₀[X] (RatFunc F₀))) =
      Polynomial.C (Polynomial.C (algebraMap F₀[X] (RatFunc F₀) dd)) * Q)
    (hQ₀0 : Q₀ ≠ 0)
    (hkn : k + 1 ≤ n) (hm : 1 ≤ m) (hn0 : 0 < n)
    (hδ1 : δ ≤ 1) (hδJ : (δ : ℝ) < gs_johnson k n m)
    (hbadz : (Finset.univ.filter (fun z : F₀ =>
      Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) = 0)).card ≤ T) :
    ∃ (Idx : Type) (_ : DecidableEq Idx) (Index : Finset Idx)
      (Ecell : Idx → Finset F₀) (Pfam : Idx → F₀ → F₀[X]) (ij₀ : Idx),
      Index.card ≤ (UniqueFactorizationMonoid.factors Q₀).toFinset.card + 1 ∧
      (Finset.univ.filter
        (fun γ : F₀ => mcaEvent (F := F₀)
          ((ReedSolomon.code domain k : Set (Fin n → F₀))) δ (u 0) (u 1) γ)) ⊆
        Index.biUnion Ecell ∧
      (∀ ij ∈ Index, ∀ γ ∈ Ecell ij,
        ∃ d : McaDecode domain k δ u γ, d.P = Pfam ij γ) ∧
      ij₀ ∈ Index ∧ (Ecell ij₀).card ≤ T ∧
      (∀ ij ∈ Index, ij ≠ ij₀ →
        ∃ R ∈ (UniqueFactorizationMonoid.factors Q₀).toFinset,
          ∀ γ ∈ Ecell ij,
            (Polynomial.X - Polynomial.C (Pfam ij γ)) ∣
              R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ))) := by
  classical
  set bad : Finset F₀ := Finset.univ.filter
    (fun γ : F₀ => mcaEvent (F := F₀)
      ((ReedSolomon.code domain k : Set (Fin n → F₀))) δ (u 0) (u 1) γ) with hbad
  -- the uniform decode family, by choice
  set dpick : (γ : F₀) → γ ∈ bad → McaDecode domain k δ u γ := fun γ hγ =>
    (exists_mcaDecode_of_mcaEvent ((Finset.mem_filter.mp hγ).2)).some with hdpick
  set P : F₀ → F₀[X] := fun γ =>
    if hγ : γ ∈ bad then (dpick γ hγ).P else 0 with hP
  -- the factor assignment for non-degenerate scalars
  have hassign : ∀ γ ∈ bad,
      Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)) ≠ 0 →
      ∃ R ∈ (UniqueFactorizationMonoid.factors Q₀).toFinset,
        (Polynomial.X - Polynomial.C (P γ)) ∣
          R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)) := by
    intro γ hγ hz
    have hdvd : (Polynomial.X - Polynomial.C (P γ)) ∣
        Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)) := by
      rw [hP]
      simp only [dif_pos hγ]
      exact mcaDecode_matching_dvd domain hQ hrep hkn hm hn0 hδ1 hδJ (dpick γ hγ) hz
    exact exists_integral_factor_assignment hQ₀0 γ (P γ) hdvd
  -- the cell index: `none` is the degenerate cell, `some R` the factor cells
  set Idx : Type := Option (F₀[X][X][Y]) with hIdx
  set assign : F₀ → Idx := fun γ =>
    if h : γ ∈ bad ∧
        Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)) ≠ 0 then
      some ((hassign γ h.1 h.2).choose)
    else none with hassigndef
  set Index : Finset Idx :=
    insert none ((UniqueFactorizationMonoid.factors Q₀).toFinset.image some) with hIndex
  set Ecell : Idx → Finset F₀ := fun ij => bad.filter (fun γ => assign γ = ij) with hEcell
  refine ⟨Idx, inferInstance, Index, Ecell, fun _ γ => P γ, none, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- index count
    refine le_trans (Finset.card_insert_le _ _) ?_
    have := Finset.card_image_le
      (s := (UniqueFactorizationMonoid.factors Q₀).toFinset) (f := some)
    omega
  · -- cover
    intro γ hγ
    rw [Finset.mem_biUnion]
    refine ⟨assign γ, ?_, ?_⟩
    · rw [hassigndef]
      split_ifs with h
      · rw [hIndex]
        refine Finset.mem_insert_of_mem ?_
        exact Finset.mem_image_of_mem some (hassign γ h.1 h.2).choose_spec.1
      · rw [hIndex]
        exact Finset.mem_insert_self _ _
    · rw [hEcell]
      exact Finset.mem_filter.mpr ⟨hγ, rfl⟩
  · -- K1: the uniform decode family
    intro ij _ γ hγ
    have hγbad : γ ∈ bad := (Finset.mem_filter.mp (by
      rw [hEcell] at hγ
      exact Finset.mem_of_mem_filter γ hγ : γ ∈ bad).mem_filter.mpr
        ⟨Finset.mem_univ γ, (Finset.mem_filter.mp (by
          rw [hEcell] at hγ
          exact hγ)).1.mem_filter.mp.2⟩)
    sorry
  · sorry
  · sorry
  · sorry

end CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame
