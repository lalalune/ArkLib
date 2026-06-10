/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.GuruswamiSudan.GSIntegralFactorAssignment
import ArkLib.Data.CodingTheory.GuruswamiSudan.GSInterpolantZDegree
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
  `scalar_fold_decoded_divides_specialization`;
* **`exists_cell_production`** — the capstone: the bad scalars of every stack decompose
  into `≤ #factors(Q₀) + 1` cells with (i) a uniform decode family (K1, **proven**, every
  cell), (ii) one designated degenerate cell of size `≤ T` (its scalars have
  `Q₀|_{Z:=γ} = 0`; the Z-degree budget bounds it), and (iii) for every other cell a
  **single irreducible factor** `R` of `Q₀` with `(Y − C (P γ)) ∣ R|_{Z:=γ}` for all its
  scalars — the exact per-cell surface on which the Steps 5–7 Hensel argument (K4) pins
  the family to an affine pencil;
* `bad_card_le_of_cell_production` — composing with a per-cell K4 pinning input: the
  stack's bad-scalar count is `≤ (#factors(Q₀) + 1)·T`.

After this file K1 is **discharged**: the Johnson MCA chain's remaining inputs are exactly
the Z-degree budget (bounding the degenerate cell) and K4 beyond the unique-decoding
window (where `Hab25CaptureKernelUD.lean` already proves it), fed the
`(cell, family, factor)` triples produced here.

Axiom-clean: `[propext, Classical.choice, Quot.sound]`.
-/

set_option linter.unusedSectionVars false

namespace CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

open Polynomial Polynomial.Bivariate Finset
open GuruswamiSudan.OverRatFunc
open _root_.ProximityGap Code
open scoped NNReal ENNReal

attribute [local instance] Classical.propDecidable

section MultisetBridge

variable {F₁ : Type} [Field F₁]

/-- Multiset-membership form of the integral factor assignment — no `toFinset`, hence no
`DecidableEq` instance in the statement. The GS files carry no `[DecidableEq F]`, so their
`toFinset` uses the Classical instance; consuming it in the instance-rich capture-kernel
context sends the unifier into whnf blowup. Crossing at the (instance-free) multiset level
avoids this. -/
lemma exists_integral_factor_assignment_multiset
    {Q₀ : (F₁[X])[X][Y]} (hQ₀ : Q₀ ≠ 0) (z : F₁) (q : F₁[X])
    (hq : (Polynomial.X - Polynomial.C q) ∣
      Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z))) :
    ∃ R, R ∈ UniqueFactorizationMonoid.factors Q₀ ∧
      (Polynomial.X - Polynomial.C q) ∣
        R.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) := by
  obtain ⟨R, hR, hd⟩ := exists_integral_factor_assignment hQ₀ z q hq
  exact ⟨R, Multiset.mem_toFinset.mp hR, hd⟩

end MultisetBridge

section FilterCardBridge

variable {F₁ : Type} [Field F₁] [Fintype F₁]

/-- Instance-free form of the degenerate-set cardinality bound: any finset of scalars that
all collapse the interpolant is small. Stated in an instance-poor section so the `filter`
hypothesis elaborates with the same Classical instances as the `ZDegree` producer
(`gs_existence_over_ratfunc_zDegree_card`); the ∀-form conclusion carries no instances at
all and is safe to consume in the instance-rich capture-kernel context. -/
lemma degenerate_card_bound_of_filter {Q₀ : (F₁[X])[X][Y]} {T : ℕ}
    (hcard : (Finset.univ.filter (fun z : F₁ =>
      Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) = 0)).card ≤ T) :
    ∀ S : Finset F₁,
      (∀ z ∈ S, Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) = 0) →
      S.card ≤ T := by
  intro S hS
  refine le_trans (Finset.card_le_card ?_) hcard
  intro z hz
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hS z hz⟩

end FilterCardBridge

variable {F₀ : Type} [Field F₀] [Fintype F₀] [DecidableEq F₀]

/-- **Lagrange roundtrip**: the Reed–Solomon codeword of a degree-`< k` polynomial decodes
back to the polynomial (`k ≤ n`, so interpolation through all `n` points is exact). -/
lemma codewordToPoly_eval_vector {n k : ℕ} [NeZero n] (domain : Fin n ↪ F₀)
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
lemma mcaDecode_hammingDist_le {n k : ℕ} [NeZero n] {domain : Fin n ↪ F₀} {δ : ℝ≥0}
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
    exact ⟨Finset.mem_univ _, fun hiS => hi.2 (d.hagree i hiS).symm⟩
  have hcount : hammingDist (fun i => u 0 i + γ • u 1 i)
      (fun i => d.P.eval (domain i)) ≤ n - d.S.card := by
    rw [hammingDist]
    refine le_trans (Finset.card_le_card hsub) ?_
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
  -- the witness set is large, in real form
  have hScard : ((1 : ℝ) - (δ : ℝ)) * n ≤ (d.S.card : ℝ) := by
    have hco := NNReal.coe_le_coe.mpr d.hcard.le
    rw [NNReal.coe_mul, NNReal.coe_sub hδ1] at hco
    simpa [Fintype.card_fin] using hco
  have hSn : d.S.card ≤ n := by
    have h := Finset.card_le_univ d.S
    simpa using h
  calc (hammingDist (fun i => u 0 i + γ • u 1 i)
        (fun i => d.P.eval (domain i)) : ℝ)
      ≤ ((n - d.S.card : ℕ) : ℝ) := by exact_mod_cast hcount
    _ = (n : ℝ) - d.S.card := by push_cast [Nat.cast_sub hSn]; ring
    _ ≤ (δ : ℝ) * n := by nlinarith

/-- **Decode ⟹ matching-factor divisibility.** In the Johnson regime, every `mcaEvent`
decode's matching factor divides the specialized integer interpolant: chain the distance
bound through the proven `scalar_fold_decoded_divides_specialization`. -/
theorem mcaDecode_matching_dvd {n k m : ℕ} [NeZero n] (domain : Fin n ↪ F₀)
    {u : WordStack F₀ (Fin 2) (Fin n)} {δ : ℝ≥0}
    {Q : (RatFunc F₀)[X][Y]} {dd : F₀[X]} {Q₀ : (F₀[X])[X][Y]}
    (hQ : GuruswamiSudan.Conditions k m (gs_degree_bound k n m)
      (liftedDomain domain) (genericFold (u 0) (u 1)) Q)
    (hrep : Q₀.map (Polynomial.mapRingHom (algebraMap F₀[X] (RatFunc F₀))) =
      Polynomial.C (Polynomial.C (algebraMap F₀[X] (RatFunc F₀) dd)) * Q)
    (hkn : k + 1 ≤ n) (hm : 1 ≤ m)
    (hδ1 : δ ≤ 1) (hδJ : (δ : ℝ) < gs_johnson k n m)
    {γ : F₀} (d : McaDecode domain k δ u γ)
    (hz : Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)) ≠ 0) :
    (Polynomial.X - Polynomial.C d.P) ∣
      Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)) := by
  classical
  have hn0 : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  -- the decode's codeword
  have hmem : (fun i => d.P.eval (domain i)) ∈ ReedSolomon.code domain k :=
    ReedSolomon.mem_code_of_polynomial_of_degree_lt_of_eval d.P d.hdeg fun i => rfl
  set p : ReedSolomon.code domain k := ⟨fun i => d.P.eval (domain i), hmem⟩ with hp
  have hround : ReedSolomon.codewordToPoly p = d.P :=
    codewordToPoly_eval_vector domain (by omega) d.P d.hdeg hmem
  -- the distance bound, in the `gs_divisibility` shape
  have hdist : (hammingDist (fun i => u 0 i + γ * u 1 i)
      (fun i => (ReedSolomon.codewordToPoly p).eval (domain i)) : ℝ) / n <
      gs_johnson k n m := by
    rw [hround]
    have hle := mcaDecode_hammingDist_le d hδ1
    have hsmul : (fun i => u 0 i + γ • u 1 i) = (fun i => u 0 i + γ * u 1 i) := by
      funext i
      rw [smul_eq_mul]
    rw [hsmul] at hle
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
    rw [div_lt_iff₀ hnR]
    calc (hammingDist (fun i => u 0 i + γ * u 1 i)
          (fun i => d.P.eval (domain i)) : ℝ)
        ≤ (δ : ℝ) * n := hle
      _ < gs_johnson k n m * n := mul_lt_mul_of_pos_right hδJ hnR
  -- the in-tree GS list decoder (its `hammingDist` was elaborated with Classical
  -- decidability — `convert` discharges the `Subsingleton Decidable` instance gap)
  have hdvd : Polynomial.X - Polynomial.C (ReedSolomon.codewordToPoly p) ∣
      Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)) := by
    refine scalar_fold_decoded_divides_specialization domain (u 0) (u 1)
      hQ hrep γ hz hkn hm p ?_
    convert hdist using 3
    congr!
  rwa [hround] at hdvd

/-- **K1 production — the per-stack cells, decode families, and the K4 input surface.**

The bad scalars of the stack decompose into `≤ #factors(Q₀) + 1` cells such that:
1. *(K1, proven)* every cell carries the uniform decode family `P` — every scalar of every
   cell is an `mcaEvent` decode with that polynomial;
2. the designated cell `none` collects the degenerate scalars (`Q₀|_{Z:=γ} = 0`) and has
   `≤ T` members (the Z-degree-budget input `hbadz`);
3. every other cell comes with a **single irreducible factor `R` of `Q₀`** such that the
   matching factor of every member divides `R|_{Z:=γ}` — the exact per-cell surface the
   Steps 5–7 Hensel lane (K4) pins to an affine pencil. -/
theorem exists_cell_production {n k m : ℕ} [NeZero n] (domain : Fin n ↪ F₀)
    (u : WordStack F₀ (Fin 2) (Fin n)) (δ : ℝ≥0) (T : ℕ)
    {Q : (RatFunc F₀)[X][Y]} {dd : F₀[X]} {Q₀ : (F₀[X])[X][Y]}
    (hQ : GuruswamiSudan.Conditions k m (gs_degree_bound k n m)
      (liftedDomain domain) (genericFold (u 0) (u 1)) Q)
    (hrep : Q₀.map (Polynomial.mapRingHom (algebraMap F₀[X] (RatFunc F₀))) =
      Polynomial.C (Polynomial.C (algebraMap F₀[X] (RatFunc F₀) dd)) * Q)
    (hQ₀0 : Q₀ ≠ 0)
    (hkn : k + 1 ≤ n) (hm : 1 ≤ m)
    (hδ1 : δ ≤ 1) (hδJ : (δ : ℝ) < gs_johnson k n m)
    (hbadz : ∀ S : Finset F₀,
      (∀ z ∈ S, Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) = 0) →
      S.card ≤ T) :
    ∃ (Index : Finset (Option ((F₀[X])[X][Y])))
      (Ecell : Option ((F₀[X])[X][Y]) → Finset F₀) (P : F₀ → F₀[X]),
      Index.card ≤ (UniqueFactorizationMonoid.factors Q₀).toFinset.card + 1 ∧
      (Finset.univ.filter (fun γ : F₀ =>
        _root_.ProximityGap.mcaEvent ((ReedSolomon.code domain k : Set (Fin n → F₀)))
          δ (u 0) (u 1) γ)) ⊆ Index.biUnion Ecell ∧
      (∀ ij ∈ Index, ∀ γ ∈ Ecell ij,
        ∃ d : McaDecode domain k δ u γ, d.P = P γ) ∧
      none ∈ Index ∧ (Ecell none).card ≤ T ∧
      (∀ ij ∈ Index, ij ≠ none →
        ∃ R ∈ (UniqueFactorizationMonoid.factors Q₀).toFinset,
          ∀ γ ∈ Ecell ij,
            (Polynomial.X - Polynomial.C (P γ)) ∣
              R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ))) := by
  classical
  set bad : Finset F₀ := Finset.univ.filter (fun γ : F₀ =>
    _root_.ProximityGap.mcaEvent ((ReedSolomon.code domain k : Set (Fin n → F₀)))
      δ (u 0) (u 1) γ) with hbad
  -- the uniform decode family, by choice (kept behind opaque `choose` fvars — embedding
  -- choice terms in `dite` branches sends later unifications into whnf blowup)
  have hex : ∀ γ : F₀, ∃ p : F₀[X],
      γ ∈ bad → ∃ d : McaDecode domain k δ u γ, d.P = p := by
    intro γ
    by_cases hγ : γ ∈ bad
    · obtain ⟨d⟩ := exists_mcaDecode_of_mcaEvent (Finset.mem_filter.mp hγ).2
      exact ⟨d.P, fun _ => ⟨d, rfl⟩⟩
    · exact ⟨0, fun h => absurd h hγ⟩
  choose P hPdec using hex
  -- the factor assignment for the non-degenerate scalars
  have hassign : ∀ γ ∈ bad,
      Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)) ≠ 0 →
      ∃ R ∈ (UniqueFactorizationMonoid.factors Q₀).toFinset,
        (Polynomial.X - Polynomial.C (P γ)) ∣
          R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)) := by
    intro γ hγ hz
    obtain ⟨d, hd⟩ := hPdec γ hγ
    have hdvd : (Polynomial.X - Polynomial.C (P γ)) ∣
        Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)) := by
      rw [← hd]
      exact mcaDecode_matching_dvd domain hQ hrep hkn hm hδ1 hδJ d hz
    obtain ⟨R, hRmem, hRd⟩ :=
      exists_integral_factor_assignment_multiset hQ₀0 γ (P γ) hdvd
    exact ⟨R, Multiset.mem_toFinset.mpr hRmem, hRd⟩
  -- the cells: `none` is the degenerate cell, `some R` the factor cells
  have hex2 : ∀ γ : F₀, ∃ ij : Option ((F₀[X])[X][Y]),
      ((γ ∈ bad ∧ Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)) ≠ 0) →
        ∃ R ∈ (UniqueFactorizationMonoid.factors Q₀).toFinset, ij = some R ∧
          (Polynomial.X - Polynomial.C (P γ)) ∣
            R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ))) ∧
      (¬ (γ ∈ bad ∧ Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)) ≠ 0) →
        ij = none) := by
    intro γ
    by_cases h : γ ∈ bad ∧
        Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)) ≠ 0
    · obtain ⟨R, hR, hdvd⟩ := hassign γ h.1 h.2
      exact ⟨some R, fun _ => ⟨R, hR, rfl, hdvd⟩, fun hc => absurd h hc⟩
    · exact ⟨none, fun hc => absurd hc h, fun _ => rfl⟩
  choose assign hassignpos hassignneg using hex2
  set Index : Finset (Option ((F₀[X])[X][Y])) :=
    insert none ((UniqueFactorizationMonoid.factors Q₀).toFinset.image some) with hIndex
  set Ecell : Option ((F₀[X])[X][Y]) → Finset F₀ :=
    fun ij => bad.filter (fun γ => assign γ = ij) with hEcell
  refine ⟨Index, Ecell, P, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- index count
    simp only [hIndex]
    refine le_trans (Finset.card_insert_le _ _) ?_
    have h := Finset.card_image_le
      (s := (UniqueFactorizationMonoid.factors Q₀).toFinset) (f := Option.some)
    omega
  · -- cover
    intro γ hγ
    have hγbad : γ ∈ bad := hγ
    rw [Finset.mem_biUnion]
    refine ⟨assign γ, ?_, ?_⟩
    · simp only [hIndex]
      by_cases h : γ ∈ bad ∧
          Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)) ≠ 0
      · obtain ⟨R, hR, hEq, _⟩ := hassignpos γ h
        rw [hEq]
        exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hR)
      · rw [hassignneg γ h]
        exact Finset.mem_insert_self _ _
    · exact Finset.mem_filter.mpr ⟨hγbad, rfl⟩
  · -- K1: the uniform decode family, on every cell
    intro ij _ γ hγ
    have hγ' : γ ∈ bad.filter (fun γ' => assign γ' = ij) := hγ
    exact hPdec γ (Finset.mem_filter.mp hγ').1
  · -- the degenerate cell is indexed
    simp only [hIndex]
    exact Finset.mem_insert_self _ _
  · -- the degenerate cell is small: its members specialize `Q₀` to zero
    refine hbadz (Ecell none) ?_
    intro γ hγ
    have hγ' : γ ∈ bad.filter (fun γ' => assign γ' = none) := hγ
    obtain ⟨hγbad, hass⟩ := Finset.mem_filter.mp hγ'
    by_contra hz
    obtain ⟨R, _, hEq, _⟩ := hassignpos γ ⟨hγbad, hz⟩
    rw [hass] at hEq
    exact absurd hEq.symm (Option.some_ne_none _)
  · -- every factor cell carries one irreducible factor of `Q₀`
    intro ij hij hne
    simp only [hIndex, Finset.mem_insert] at hij
    rcases hij with h | h
    · exact absurd h hne
    · obtain ⟨R, hR, rfl⟩ := Finset.mem_image.mp h
      refine ⟨R, hR, ?_⟩
      intro γ hγ
      have hγ' : γ ∈ bad.filter (fun γ' => assign γ' = some R) := hγ
      obtain ⟨hγbad, hass⟩ := Finset.mem_filter.mp hγ'
      by_cases hz : Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)) ≠ 0
      · obtain ⟨R', hR', hEq, hdvd⟩ := hassignpos γ ⟨hγbad, hz⟩
        rw [hass] at hEq
        rwa [← Option.some.inj hEq] at hdvd
      · rw [hassignneg γ (fun hc => hz hc.2)] at hass
        exact absurd hass.symm (Option.some_ne_none _)

/-- **The K1-complete count**: composing the cell production with a per-cell K4 pinning
input (any decode-family cell whose members' matching factors all divide one specialized
irreducible factor obeys the size-`T` bound), the stack's bad-scalar count is
`≤ (#factors(Q₀) + 1)·T`. -/
theorem bad_card_le_of_cell_production {n k m : ℕ} [NeZero n] (domain : Fin n ↪ F₀)
    (u : WordStack F₀ (Fin 2) (Fin n)) (δ : ℝ≥0) (T : ℕ)
    {Q : (RatFunc F₀)[X][Y]} {dd : F₀[X]} {Q₀ : (F₀[X])[X][Y]}
    (hQ : GuruswamiSudan.Conditions k m (gs_degree_bound k n m)
      (liftedDomain domain) (genericFold (u 0) (u 1)) Q)
    (hrep : Q₀.map (Polynomial.mapRingHom (algebraMap F₀[X] (RatFunc F₀))) =
      Polynomial.C (Polynomial.C (algebraMap F₀[X] (RatFunc F₀) dd)) * Q)
    (hQ₀0 : Q₀ ≠ 0)
    (hkn : k + 1 ≤ n) (hm : 1 ≤ m)
    (hδ1 : δ ≤ 1) (hδJ : (δ : ℝ) < gs_johnson k n m)
    (hbadz : ∀ S : Finset F₀,
      (∀ z ∈ S, Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) = 0) →
      S.card ≤ T)
    (hK4 : ∀ (E : Finset F₀) (P : F₀ → F₀[X]) (R : (F₀[X])[X][Y]),
      R ∈ (UniqueFactorizationMonoid.factors Q₀).toFinset →
      (∀ γ ∈ E, ∃ d : McaDecode domain k δ u γ, d.P = P γ) →
      (∀ γ ∈ E, (Polynomial.X - Polynomial.C (P γ)) ∣
        R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ))) →
      E.card ≤ T) :
    (Finset.univ.filter (fun γ : F₀ =>
      _root_.ProximityGap.mcaEvent ((ReedSolomon.code domain k : Set (Fin n → F₀)))
        δ (u 0) (u 1) γ)).card ≤
      ((UniqueFactorizationMonoid.factors Q₀).toFinset.card + 1) * T := by
  classical
  obtain ⟨Index, Ecell, P, hcardI, hcover, hdec, hnone, hbadcell, hfactor⟩ :=
    exists_cell_production domain u δ T hQ hrep hQ₀0 hkn hm hδ1 hδJ hbadz
  have hcell : ∀ ij ∈ Index, (Ecell ij).card ≤ T := by
    intro ij hij
    by_cases hne : ij = none
    · subst hne
      exact hbadcell
    · obtain ⟨R, hR, hdvd⟩ := hfactor ij hij hne
      exact hK4 (Ecell ij) P R hR (hdec ij hij) hdvd
  calc (Finset.univ.filter (fun γ : F₀ =>
        _root_.ProximityGap.mcaEvent ((ReedSolomon.code domain k : Set (Fin n → F₀)))
          δ (u 0) (u 1) γ)).card
      ≤ (Index.biUnion Ecell).card := Finset.card_le_card hcover
    _ ≤ ∑ ij ∈ Index, (Ecell ij).card := Finset.card_biUnion_le
    _ ≤ Index.card * T := by
        have h := Finset.sum_le_card_nsmul Index (fun ij => (Ecell ij).card) T hcell
        simpa [smul_eq_mul] using h
    _ ≤ ((UniqueFactorizationMonoid.factors Q₀).toFinset.card + 1) * T :=
        Nat.mul_le_mul_right T hcardI

/-- **The total cell production** — no interpolant hypotheses left. The `ZDegree` producer
(`gs_existence_over_ratfunc_zDegree_card`, unit (2)) supplies the integer GS interpolant,
its `Conditions`, and the explicit degenerate-set budget
`T = n·|constraintIndices m|·gs_degree_bound k n m`; the cell production consumes them.
What remains of the Johnson MCA chain after this theorem is exactly K4 beyond the
unique-decoding window, fed the (cell, family, factor) triples produced here. -/
theorem exists_cell_production_total {n k m : ℕ} [NeZero n] (domain : Fin n ↪ F₀)
    (u : WordStack F₀ (Fin 2) (Fin n)) (δ : ℝ≥0)
    (hk1 : 1 < k) (hkn : k + 1 ≤ n) (hm : 1 ≤ m)
    (hδ1 : δ ≤ 1) (hδJ : (δ : ℝ) < gs_johnson k n m) :
    ∃ (Q₀ : (F₀[X])[X][Y]) (Index : Finset (Option ((F₀[X])[X][Y])))
      (Ecell : Option ((F₀[X])[X][Y]) → Finset F₀) (P : F₀ → F₀[X]),
      Q₀ ≠ 0 ∧
      Index.card ≤ (UniqueFactorizationMonoid.factors Q₀).toFinset.card + 1 ∧
      (Finset.univ.filter (fun γ : F₀ =>
        _root_.ProximityGap.mcaEvent ((ReedSolomon.code domain k : Set (Fin n → F₀)))
          δ (u 0) (u 1) γ)) ⊆ Index.biUnion Ecell ∧
      (∀ ij ∈ Index, ∀ γ ∈ Ecell ij,
        ∃ d : McaDecode domain k δ u γ, d.P = P γ) ∧
      none ∈ Index ∧
      (Ecell none).card ≤
        n * (GuruswamiSudan.constraintIndices m).card * gs_degree_bound k n m ∧
      (∀ ij ∈ Index, ij ≠ none →
        ∃ R ∈ (UniqueFactorizationMonoid.factors Q₀).toFinset,
          ∀ γ ∈ Ecell ij,
            (Polynomial.X - Polynomial.C (P γ)) ∣
              R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ))) := by
  obtain ⟨Q₀, h0, hcond, hcard⟩ :=
    GuruswamiSudan.OverRatFunc.ZDegree.gs_existence_over_ratfunc_zDegree_card
      (F := F₀) k m domain (u 0) (u 1) hk1 (NeZero.ne n) hm
  have hrep : Q₀.map (Polynomial.mapRingHom (algebraMap F₀[X] (RatFunc F₀))) =
      Polynomial.C (Polynomial.C (algebraMap F₀[X] (RatFunc F₀) (1 : F₀[X]))) *
        Q₀.map (Polynomial.mapRingHom (algebraMap F₀[X] (RatFunc F₀))) := by
    simp
  obtain ⟨Index, Ecell, P, h1, h2, h3, h4, h5, h6⟩ :=
    exists_cell_production domain u δ
      (n * (GuruswamiSudan.constraintIndices m).card * gs_degree_bound k n m)
      hcond hrep h0 hkn hm hδ1 hδJ (degenerate_card_bound_of_filter hcard)
  exact ⟨Q₀, Index, Ecell, P, h0, h1, h2, h3, h4, h5, h6⟩

end CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

/-! ## Axiom audit — all kernel-clean. -/
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.codewordToPoly_eval_vector
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.mcaDecode_hammingDist_le
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.mcaDecode_matching_dvd
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.exists_cell_production
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.bad_card_le_of_cell_production
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.exists_cell_production_total
