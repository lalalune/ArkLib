/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Hab25CoordinateUpgradeWeld

/-!
# The elementary per-cell strict extraction (#304, SK1)

**The strict Johnson coefficient-polynomial extraction, per section-linked cell, by plain
counting** — no Hensel lifting, no `𝒪`-ring, no `Λ`-weights, no characteristic hypothesis.
At a cell of the (curve) GS production — an irreducible factor `R` of the interpolant with
a uniform decode family `P` and the surface divisibility `(Y − C w) ∣ R` — the §5 Steps
5–7 machinery collapses:

* `decode_eq_surface_map` — **the decode IS the surface's specialization**:
  `P γ = w.map (evalRingHom γ)` (irreducibility makes `R` an associate of the surface
  factor; the fiber strips to a unit times `X − C (w(γ))`; monic-linear divisibility in a
  domain pins the root);
* `foldSection_eq_of_heavy` — at a coordinate carrying `> max(B_w, k)` agreeing cell
  scalars, the surface's coordinate section **is** the degree-`≤ k` fold section
  (one root count);
* `surface_coeff_natDegree_le` — with `> deg w` such coordinates, every coefficient of
  `w` has `Z`-degree `≤ k` (a second root count on the coefficient slices);
* **`strict_coeffPolys_of_cell`** — the capstone: the coefficient polynomials demanded by
  `StrictCoeffPolysResidual` exist on the cell, and they are **literally the coefficients
  of the surface**: `B j := w.coeff j`, `natDegree < k + 1`, and
  `(P γ).coeff j = (B j).eval γ` for every cell scalar (by `coeff_map`).

Char-uniformity (SA5): no `CharZero`/`CharP`/separability hypothesis appears — the
extraction is field-uniform at the cell level, removing BCIKS20 App. C from this layer.

What this does NOT give (honest scope): the GLOBAL single-`B` family across the whole
good set demanded by the literal `StrictCoeffPolysResidual` — the paper's own Prop 5.5
yields a SUBSET (`|S′| ≥ |S|/2D_Y`) on one curve, and the global form is the Step-8 /
uniqueness layer (SK3 audit on the issue).  Composed with
`exists_curve_cell_production_total` + pigeonhole, this brick yields the Prop-5.5-faithful
subset form (SK2).

Axiom-clean: `[propext, Classical.choice, Quot.sound]` (audited at end of file).
-/

set_option linter.unusedSectionVars false

namespace BCIKS20.CurveCellStrictExtraction

open Polynomial Polynomial.Bivariate Finset
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame
open _root_.ProximityGap Code

attribute [local instance] Classical.propDecidable

variable {F₀ : Type} [Field F₀]

/-! ## The decode is the surface's specialization -/

/-- **The decode IS the surface's specialization** (the map form of the section link,
arity-generic): cell irreducibility + the surface divisibility pin every cell decode to
`w.map (evalRingHom γ)`. -/
theorem decode_eq_surface_map {R : (F₀[X])[X][Y]}
    (hRirr : Irreducible R) {w : F₀[X][Y]}
    (hwdvd : (Polynomial.X - Polynomial.C w) ∣ R)
    (γ : F₀) (P : F₀[X])
    (hdvdP : (Polynomial.X - Polynomial.C P) ∣
      R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ))) :
    P = w.map (Polynomial.evalRingHom γ) := by
  classical
  have hXw_nu : ¬ IsUnit (Polynomial.X - Polynomial.C w) := by
    intro hu
    have h1 := Polynomial.natDegree_eq_zero_of_isUnit hu
    rw [Polynomial.natDegree_X_sub_C] at h1
    exact one_ne_zero h1
  obtain ⟨c, hc⟩ := hwdvd
  have hcu : IsUnit c := (hRirr.isUnit_or_isUnit hc).resolve_left hXw_nu
  set φ : (F₀[X])[X] →+* F₀[X] := Polynomial.mapRingHom (Polynomial.evalRingHom γ) with hφ
  set wγ : F₀[X] := w.map (Polynomial.evalRingHom γ) with hwγ
  have hfiber : R.map φ = (Polynomial.X - Polynomial.C wγ) * c.map φ := by
    rw [hc, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    rfl
  have hcuγ : IsUnit (c.map φ) := hcu.map (Polynomial.mapRingHom φ)
  have hdvd2 : (Polynomial.X - Polynomial.C P) ∣ (Polynomial.X - Polynomial.C wγ) := by
    have h := hdvdP
    rw [hfiber] at h
    exact (IsUnit.dvd_mul_right hcuγ).mp h
  obtain ⟨q, hq⟩ := hdvd2
  have hXw0 : (Polynomial.X - Polynomial.C wγ : F₀[X][Y]) ≠ 0 :=
    Polynomial.X_sub_C_ne_zero wγ
  have hq0 : q ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hq
    exact hXw0 hq
  have hdegq : q.natDegree = 0 := by
    have hdegs := congrArg Polynomial.natDegree hq
    rw [Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero P) hq0,
      Polynomial.natDegree_X_sub_C, Polynomial.natDegree_X_sub_C] at hdegs
    omega
  have ha1 : q.leadingCoeff = 1 := by
    have hlc := congrArg Polynomial.leadingCoeff hq
    rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_X_sub_C,
      Polynomial.leadingCoeff_X_sub_C, one_mul] at hlc
    exact hlc.symm
  have hq1 : q = 1 := by
    have hC := Polynomial.eq_C_of_natDegree_eq_zero hdegq
    rw [hC] at ha1 ⊢
    rw [Polynomial.leadingCoeff_C] at ha1
    rw [ha1, Polynomial.C_1]
  rw [hq1, mul_one] at hq
  exact (Polynomial.C_injective (sub_right_inj.mp hq)).symm

/-! ## The eval swap and the coordinate section -/

/-- Outer-evaluation at a constant commutes with inner specialization:
`(w.eval (C a)).eval z = (w.map (evalRingHom z)).eval a`. -/
theorem eval_C_eval_eq_map_eval (w : F₀[X][Y]) (a z : F₀) :
    (w.eval (Polynomial.C a)).eval z
      = (w.map (Polynomial.evalRingHom z)).eval a := by
  have h := ArkLib.FactorKill.eval_section_specializes w (Polynomial.C a) z
  rw [h, Polynomial.eval_C]

/-- The coordinate section's degree is bounded by the surface's flat coefficient budget. -/
theorem eval_C_natDegree_le (w : F₀[X][Y]) (a : F₀) {Bw : ℕ}
    (hB : ∀ i, (w.coeff i).natDegree ≤ Bw) :
    (w.eval (Polynomial.C a)).natDegree ≤ Bw := by
  rw [Polynomial.eval_eq_sum_range]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
  refine le_trans Polynomial.natDegree_mul_le ?_
  have h1 := hB i
  have h2 : ((Polynomial.C a : F₀[X]) ^ i).natDegree = 0 := by
    rw [← Polynomial.C_pow, Polynomial.natDegree_C]
  omega

/-- The `m`-th inner coefficient of the coordinate section is the evaluation of the
coefficient slice: `(w.eval (C a)).coeff m = ∑ i, (w.coeff i).coeff m · aⁱ`. -/
theorem eval_C_coeff (w : F₀[X][Y]) (a : F₀) (m : ℕ) :
    (w.eval (Polynomial.C a)).coeff m
      = ∑ i ∈ Finset.range (w.natDegree + 1), (w.coeff i).coeff m * a ^ i := by
  rw [Polynomial.eval_eq_sum_range, Polynomial.finset_sum_coeff]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Polynomial.C_pow, Polynomial.coeff_mul_C]

/-- **The fold-section identification (one root count)**: a coordinate section agreeing
with the degree-`≤ k` fold section at more than `max(B_w, k)` scalars IS the fold
section. -/
theorem foldSection_eq_of_heavy {n L : ℕ} {u : WordStack F₀ (Fin L) (Fin n)}
    {w : F₀[X][Y]} {Bw k : ℕ} (hLk : L - 1 ≤ k)
    (hB : ∀ i, (w.coeff i).natDegree ≤ Bw)
    (a : F₀) (t : Fin n) (S : Finset F₀)
    (hcard : max Bw k < S.card)
    (hagree : ∀ z ∈ S, (w.eval (Polynomial.C a)).eval z = (foldSectionAt u t).eval z) :
    w.eval (Polynomial.C a) = foldSectionAt u t := by
  classical
  by_contra hne
  have hsub0 : w.eval (Polynomial.C a) - foldSectionAt u t ≠ 0 := sub_ne_zero.mpr hne
  have hdeg : (w.eval (Polynomial.C a) - foldSectionAt u t).natDegree ≤ max Bw k := by
    refine le_trans (Polynomial.natDegree_sub_le _ _) ?_
    refine max_le_max (eval_C_natDegree_le w a hB) ?_
    exact le_trans (foldSectionAt_natDegree_le u t) hLk
  have hroots : S ⊆ (w.eval (Polynomial.C a) - foldSectionAt u t).roots.toFinset := by
    intro z hz
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hsub0]
    show (w.eval (Polynomial.C a) - foldSectionAt u t).eval z = 0
    rw [Polynomial.eval_sub, hagree z hz, sub_self]
  have hle : S.card ≤ max Bw k :=
    le_trans (Finset.card_le_card hroots)
      (le_trans (Multiset.toFinset_card_le _)
        (le_trans (Polynomial.card_roots' _) hdeg))
  omega

/-! ## The coefficient slices vanish above degree `k` -/

/-- **The Z-degree collapse (the second root count)**: with more than `deg w` coordinates
each identifying the section with the fold, every coefficient of the surface has inner
degree `≤ k`. -/
theorem surface_coeff_natDegree_le {n L : ℕ} {domain : Fin n ↪ F₀}
    {u : WordStack F₀ (Fin L) (Fin n)}
    {w : F₀[X][Y]} {Bw k : ℕ} (hLk : L - 1 ≤ k)
    (hB : ∀ i, (w.coeff i).natDegree ≤ Bw)
    (T : Finset (Fin n)) (hT : w.natDegree < T.card)
    (S : Fin n → Finset F₀)
    (hcard : ∀ t ∈ T, max Bw k < (S t).card)
    (hagree : ∀ t ∈ T, ∀ z ∈ S t,
      (w.eval (Polynomial.C (domain t))).eval z = (foldSectionAt u t).eval z) :
    ∀ j, (w.coeff j).natDegree ≤ k := by
  classical
  -- each chosen coordinate's section IS the fold section
  have hsec : ∀ t ∈ T, w.eval (Polynomial.C (domain t)) = foldSectionAt u t :=
    fun t ht => foldSection_eq_of_heavy hLk hB (domain t) t (S t) (hcard t ht)
      (hagree t ht)
  -- hence each section has inner degree ≤ k
  have hsecdeg : ∀ t ∈ T, (w.eval (Polynomial.C (domain t))).natDegree ≤ k := by
    intro t ht
    rw [hsec t ht]
    exact le_trans (foldSectionAt_natDegree_le u t) hLk
  -- the coefficient slice at inner index m > k
  intro j
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro m hm
  -- the slice polynomial: X-coefficients are the m-th inner coefficients of w's coeffs
  set cm : F₀[X] := ∑ i ∈ Finset.range (w.natDegree + 1),
    Polynomial.monomial i ((w.coeff i).coeff m) with hcm
  have hcmdeg : cm.natDegree ≤ w.natDegree := by
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
    refine le_trans (Polynomial.natDegree_monomial_le _) ?_
    rw [Finset.mem_range] at hi
    omega
  have hcmeval : ∀ a : F₀, cm.eval a = (w.eval (Polynomial.C a)).coeff m := by
    intro a
    rw [eval_C_coeff, hcm, Polynomial.eval_finset_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Polynomial.eval_monomial]
  -- the slice vanishes at every chosen coordinate point (the section has degree ≤ k < m)
  have hvanish : ∀ t ∈ T, cm.eval (domain t) = 0 := by
    intro t ht
    rw [hcmeval]
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hsecdeg t ht) hm)
  -- more roots than the degree: the slice is zero
  have hcm0 : cm = 0 := by
    by_contra hne
    have hroots : T.image (fun t => domain t) ⊆ cm.roots.toFinset := by
      intro a ha
      rw [Finset.mem_image] at ha
      obtain ⟨t, ht, rfl⟩ := ha
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hne]
      exact hvanish t ht
    have hinj : (T.image (fun t => domain t)).card = T.card :=
      Finset.card_image_of_injective T domain.injective
    have hle : T.card ≤ w.natDegree := by
      calc T.card = (T.image (fun t => domain t)).card := hinj.symm
        _ ≤ cm.roots.toFinset.card := Finset.card_le_card hroots
        _ ≤ cm.roots.card := Multiset.toFinset_card_le _
        _ ≤ cm.natDegree := Polynomial.card_roots' _
        _ ≤ w.natDegree := hcmdeg
    omega
  -- extract the coefficient: the slice's j-th X-coefficient is (w.coeff j).coeff m
  have hcoeff : cm.coeff j = (w.coeff j).coeff m := by
    rw [hcm, Polynomial.finset_sum_coeff]
    rcases lt_or_ge j (w.natDegree + 1) with hj | hj
    · rw [Finset.sum_eq_single j
        (fun i _ hij => by rw [Polynomial.coeff_monomial, if_neg hij])
        (fun h => absurd (Finset.mem_range.mpr hj) h)]
      rw [Polynomial.coeff_monomial, if_pos rfl]
    · -- past the degree: both sides vanish
      have hwj : w.coeff j = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      rw [hwj, Polynomial.coeff_zero]
      refine Finset.sum_eq_zero fun i hi => ?_
      rw [Finset.mem_range] at hi
      rw [Polynomial.coeff_monomial, if_neg (by omega)]
  rw [← hcoeff, hcm0, Polynomial.coeff_zero]

/-! ## The capstone: the strict coefficient polynomials on the cell -/

/-- **THE ELEMENTARY PER-CELL STRICT EXTRACTION (#304, SK1).**  On a section-linked cell
of the curve GS production, the coefficient polynomials demanded by the strict Johnson
extraction exist, with the residual's exact degree bound — and they are **literally the
coefficients of the surface** (`B j := w.coeff j`).  No Hensel lifting, no `𝒪`-ring, no
`Λ`-weights, no characteristic hypothesis. -/
theorem strict_coeffPolys_of_cell {n L : ℕ} {domain : Fin n ↪ F₀}
    {u : WordStack F₀ (Fin L) (Fin n)}
    {R : (F₀[X])[X][Y]} (hRirr : Irreducible R)
    {w : F₀[X][Y]} (hwdvd : (Polynomial.X - Polynomial.C w) ∣ R)
    {Bw k : ℕ} (hLk : L - 1 ≤ k)
    (hB : ∀ i, (w.coeff i).natDegree ≤ Bw)
    (E : Finset F₀) (P : F₀ → F₀[X])
    (hdvdP : ∀ γ ∈ E, (Polynomial.X - Polynomial.C (P γ)) ∣
      R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)))
    -- the heavy coordinates: more than `deg w` of them, each with more than
    -- `max(B_w, k)` cell scalars whose decode agrees with the fold there
    (T : Finset (Fin n)) (hT : w.natDegree < T.card)
    (S : Fin n → Finset F₀) (hSE : ∀ t ∈ T, S t ⊆ E)
    (hcard : ∀ t ∈ T, max Bw k < (S t).card)
    (hagree : ∀ t ∈ T, ∀ z ∈ S t,
      (P z).eval (domain t) = (foldSectionAt u t).eval z) :
    ∃ B : ℕ → F₀[X],
      (∀ j, (B j).natDegree < k + 1) ∧
      ∀ γ ∈ E, ∀ j, (P γ).coeff j = (B j).eval γ := by
  classical
  -- the surface's coordinate sections satisfy the heavy agreement
  have hagree' : ∀ t ∈ T, ∀ z ∈ S t,
      (w.eval (Polynomial.C (domain t))).eval z = (foldSectionAt u t).eval z := by
    intro t ht z hz
    rw [eval_C_eval_eq_map_eval,
      ← decode_eq_surface_map hRirr hwdvd z (P z) (hdvdP z (hSE t ht hz))]
    exact hagree t ht z hz
  -- the Z-degree collapse
  have hdeg := surface_coeff_natDegree_le (domain := domain) (u := u) hLk hB T hT S
    hcard hagree'
  -- the coefficient polynomials are the surface's coefficients
  refine ⟨fun j => w.coeff j, fun j => Nat.lt_succ_of_le (hdeg j), fun γ hγ j => ?_⟩
  rw [decode_eq_surface_map hRirr hwdvd γ (P γ) (hdvdP γ hγ), Polynomial.coeff_map]
  rfl

end BCIKS20.CurveCellStrictExtraction

/-! ## Axiom audit — all kernel-clean. -/
#print axioms BCIKS20.CurveCellStrictExtraction.decode_eq_surface_map
#print axioms BCIKS20.CurveCellStrictExtraction.foldSection_eq_of_heavy
#print axioms BCIKS20.CurveCellStrictExtraction.surface_coeff_natDegree_le
#print axioms BCIKS20.CurveCellStrictExtraction.strict_coeffPolys_of_cell
