/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Katerina Hristova, Frantisek Silvasi, Julian Sutherland,
         Ilia Vlasov, Chung Thai Nguyen
-/

import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.Curves
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.ListDecoding.Agreement
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.ListDecoding.Guruswami

-- This bridge exposes paper-aligned theorem names that exceed the style line limit.
set_option linter.style.longLine false

namespace ProximityGap

open NNReal Finset Function ProbabilityTheory
open scoped BigOperators LinearCode ProbabilityTheory ENNReal
open Code

section BCIKS20ProximityGapSection5To6Bridge

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

omit [Field F] [Fintype F] [DecidableEq F] [NeZero n] in
/-- Every two-row word stack is definitionally the stack made from its two rows. -/
lemma wordStack_fin_two_eq_finMapTwoWords (u : WordStack F (Fin 2) (Fin n)) :
    u = Code.finMapTwoWords (u 0) (u 1) := by
  funext rowIdx
  match rowIdx with
  | 0 => rfl
  | 1 => rfl

/-- For degree-one curves through two words, the §6 close-parameter set is the
same set as the §5 affine-line close-proximity set. -/
theorem coeffs_of_close_proximity_curve_finMapTwoWords_eq_close_proximity
    {k : ℕ} {ωs : Fin n ↪ F} (δ : ℚ≥0) (u₀ u₁ : Fin n → F) :
    coeffs_of_close_proximity_curve (F := F) (n := n) (l := 2)
        δ (Code.finMapTwoWords u₀ u₁) (ReedSolomon.toFinset ωs (k + 1)) =
      coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) u₀ u₁ := by
  classical
  apply Finset.ext
  intro z
  simp only [coeffs_of_close_proximity_curve, coeffs_of_close_proximity,
    ReedSolomon.toFinset, ReedSolomon.RScodeSet, Set.mem_toFinset, Set.mem_setOf_eq,
    polynomialCurveEval_eq_sum_smul]
  rw [sum_finMapTwoWords_eq]
  constructor
  · intro hz
    have hz' :
        δᵣ(u₀ + z • u₁,
            (↑(Set.toFinset (ReedSolomon.code ωs (k + 1) : Set (Fin n → F))) :
              Set (Fin n → F))) ≤ ((δ : ℝ≥0) : ENNReal) := by
      simpa [ENNReal.coe_nnratCast] using hz
    obtain ⟨v, hv_mem, hv_close⟩ :=
      (relCloseToCode_iff_relCloseToCodeword_of_minDist
        (C := (↑(Set.toFinset (ReedSolomon.code ωs (k + 1) : Set (Fin n → F))) :
          Set (Fin n → F)))
        (u := u₀ + z • u₁) (δ := (δ : ℝ≥0))).mp hz'
    have hv_code : v ∈ ReedSolomon.code ωs (k + 1) := by
      simpa using hv_mem
    exact ⟨⟨v, hv_code⟩, by simpa [ENNReal.coe_nnratCast] using hv_close⟩
  · rintro ⟨v, hv_close⟩
    have hv_fin :
        (v : Fin n → F) ∈
          (↑(Set.toFinset (ReedSolomon.code ωs (k + 1) : Set (Fin n → F))) :
            Set (Fin n → F)) := by
      simp
    have hclose :
        δᵣ(u₀ + z • u₁,
            (↑(Set.toFinset (ReedSolomon.code ωs (k + 1) : Set (Fin n → F))) :
              Set (Fin n → F))) ≤ ((δ : ℝ≥0) : ENNReal) :=
      (relCloseToCode_iff_relCloseToCodeword_of_minDist
        (C := (↑(Set.toFinset (ReedSolomon.code ωs (k + 1) : Set (Fin n → F))) :
          Set (Fin n → F)))
        (u := u₀ + z • u₁) (δ := (δ : ℝ≥0))).mpr
        ⟨v, hv_fin, by simpa [ENNReal.coe_nnratCast] using hv_close⟩
    simpa [ENNReal.coe_nnratCast] using hclose

/-- Direct §5-to-§6 specialization: the affine-line close-proximity set from
the list-decoding section is exactly the degree-one `RS_goodCoeffsCurve` set. -/
theorem coeffs_of_close_proximity_eq_goodCoeffsCurve_finMapTwoWords
    {k : ℕ} {ωs : Fin n ↪ F} (δ : ℚ≥0) (u₀ u₁ : Fin n → F) :
    coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) u₀ u₁ =
      RS_goodCoeffsCurve (k := 1) (deg := k + 1) (domain := ωs)
        (Code.finMapTwoWords u₀ u₁) (δ : ℝ≥0) := by
  rw [← coeffs_of_close_proximity_curve_finMapTwoWords_eq_close_proximity
    (F := F) (n := n) (k := k) (ωs := ωs) δ u₀ u₁]
  exact coeffs_of_close_proximity_curve_RS_toFinset_eq_goodCoeffsCurve
    (F := F) (n := n) (k := 1) (deg := k + 1) (domain := ωs) δ
    (Code.finMapTwoWords u₀ u₁)

/-- Membership form of
`coeffs_of_close_proximity_eq_goodCoeffsCurve_finMapTwoWords`. -/
theorem coeffs_of_close_proximity_mem_iff_goodCoeffsCurve_finMapTwoWords
    {k : ℕ} {ωs : Fin n ↪ F} (δ : ℚ≥0) (u₀ u₁ : Fin n → F) (z : F) :
    z ∈ coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) u₀ u₁ ↔
      z ∈ RS_goodCoeffsCurve (k := 1) (deg := k + 1) (domain := ωs)
        (Code.finMapTwoWords u₀ u₁) (δ : ℝ≥0) := by
  rw [coeffs_of_close_proximity_eq_goodCoeffsCurve_finMapTwoWords
    (F := F) (n := n) (k := k) (ωs := ωs) δ u₀ u₁]

/-- Cardinality form of
`coeffs_of_close_proximity_eq_goodCoeffsCurve_finMapTwoWords`. -/
theorem coeffs_of_close_proximity_card_eq_goodCoeffsCurve_finMapTwoWords
    {k : ℕ} {ωs : Fin n ↪ F} (δ : ℚ≥0) (u₀ u₁ : Fin n → F) :
    (coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) u₀ u₁).card =
      (RS_goodCoeffsCurve (k := 1) (deg := k + 1) (domain := ωs)
        (Code.finMapTwoWords u₀ u₁) (δ : ℝ≥0)).card := by
  rw [coeffs_of_close_proximity_eq_goodCoeffsCurve_finMapTwoWords
    (F := F) (n := n) (k := k) (ωs := ωs) δ u₀ u₁]

open Polynomial in
/-- The §5 canonical `PzFamily` package in the exact canonical-evaluation
shape consumed by the strict §6 curve front doors, specialized to degree-one
curves `Code.finMapTwoWords`.

The hypotheses are the remaining §5 assembly inputs: every close parameter is
in every coordinate matching set, and decoded representatives are unique on the
§5 close set. -/
theorem PzFamily_exists_canonical_eval_polys_goodCoeffsCurve_finMapTwoWords
    {m k : ℕ} {ωs : Fin n ↪ F} {Q : F[Z][X][Y]}
    (δ : ℚ≥0) (u₀ u₁ : Fin n → F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hsubset : ∀ x : Fin n,
      coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) u₀ u₁ ⊆
        matching_set_at_x k (δ : ℚ) h_gs x)
    (hunique : ∀ P : F → F[X],
      (∀ z ∈ coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) u₀ u₁,
        (P z).natDegree < k + 1 ∧ δᵣ(u₀ + z • u₁, (P z).eval ∘ ωs) ≤ (δ : ℚ)) →
      ∀ z ∈ coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) u₀ u₁,
        P z = PzFamily (F := F) (n := n) (δ : ℚ) u₀ u₁ ωs k z) :
    ∃ P₀ : F → F[X],
      (∀ z ∈ RS_goodCoeffsCurve (k := 1) (deg := k + 1) (domain := ωs)
          (Code.finMapTwoWords u₀ u₁) (δ : ℝ≥0),
        (P₀ z).natDegree < k + 1 ∧
          δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • Code.finMapTwoWords u₀ u₁ t,
            (P₀ z).eval ∘ ωs) ≤ (δ : ℝ≥0)) ∧
      (∃ E : Fin n → F[X],
        (∀ x, (E x).natDegree < 1 + 1) ∧
          ∀ z ∈ RS_goodCoeffsCurve (k := 1) (deg := k + 1) (domain := ωs)
              (Code.finMapTwoWords u₀ u₁) (δ : ℝ≥0),
            ∀ x : Fin n, (P₀ z).eval (ωs x) = (E x).eval z) ∧
      ∀ P : F → F[X],
        (∀ z ∈ RS_goodCoeffsCurve (k := 1) (deg := k + 1) (domain := ωs)
            (Code.finMapTwoWords u₀ u₁) (δ : ℝ≥0),
          (P z).natDegree < k + 1 ∧
            δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • Code.finMapTwoWords u₀ u₁ t,
              (P z).eval ∘ ωs) ≤ (δ : ℝ≥0)) →
        ∀ z ∈ RS_goodCoeffsCurve (k := 1) (deg := k + 1) (domain := ωs)
            (Code.finMapTwoWords u₀ u₁) (δ : ℝ≥0),
          P z = P₀ z := by
  classical
  refine ⟨PzFamily (F := F) (n := n) (δ : ℚ) u₀ u₁ ωs k, ?_, ?_, ?_⟩
  · intro z hz
    have hz_close :
        z ∈ coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) u₀ u₁ := by
      exact (coeffs_of_close_proximity_mem_iff_goodCoeffsCurve_finMapTwoWords
        (F := F) (n := n) (k := k) (ωs := ωs) δ u₀ u₁ z).mpr hz
    have hdecoded :=
      PzFamily_decoded_on_close_set
        (F := F) (n := n) (k := k) (δ := (δ : ℚ)) (u₀ := u₀) (u₁ := u₁)
        (ωs := ωs) z hz_close
    exact ⟨hdecoded.1, by
      simpa [sum_finMapTwoWords_eq, ENNReal.coe_nnratCast] using hdecoded.2⟩
  · refine ⟨lineValuePolynomialFamily (F := F) (n := n) u₀ u₁, ?_, ?_⟩
    · intro x
      simpa [lineValuePolynomialFamily] using
        lineValuePolynomial_natDegree_lt_succ_succ (F := F) (n := n) u₀ u₁ x
    · intro z hz x
      have hz_close :
          z ∈ coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) u₀ u₁ := by
        exact (coeffs_of_close_proximity_mem_iff_goodCoeffsCurve_finMapTwoWords
          (F := F) (n := n) (k := k) (ωs := ωs) δ u₀ u₁ z).mpr hz
      exact PzFamily_eval_eq_lineValuePolynomial_eval_of_mem_matching_set_at_x
        (F := F) (m := m) (n := n) (k := k) (Q := Q) h_gs
        (hsubset x hz_close)
  · intro P hP z hz
    have hz_close :
        z ∈ coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) u₀ u₁ := by
      exact (coeffs_of_close_proximity_mem_iff_goodCoeffsCurve_finMapTwoWords
        (F := F) (n := n) (k := k) (ωs := ωs) δ u₀ u₁ z).mpr hz
    exact hunique P (by
      intro w hw
      have hw_good :
          w ∈ RS_goodCoeffsCurve (k := 1) (deg := k + 1) (domain := ωs)
            (Code.finMapTwoWords u₀ u₁) (δ : ℝ≥0) := by
        exact (coeffs_of_close_proximity_mem_iff_goodCoeffsCurve_finMapTwoWords
          (F := F) (n := n) (k := k) (ωs := ωs) δ u₀ u₁ w).mp hw
      have hwP := hP w hw_good
      exact ⟨hwP.1, by
        simpa [sum_finMapTwoWords_eq, ENNReal.coe_nnratCast] using hwP.2⟩) z hz_close

open Polynomial in
/-- Selected-domain coefficient-polynomial witness for the §6 strict-Johnson
front door, specialized to the §5 affine-line setup.

Claim 5.11 naturally selects only `k + 1` coordinates.  Since decoded
polynomials have degree `< k + 1`, interpolation on that selected domain is
enough to recover every coefficient as a degree-one polynomial in the curve
parameter. -/
theorem hcoeffPoly_goodCoeffsCurve_finMapTwoWords_of_selected_matching_domain
    {m k : ℕ} {ωs : Fin n ↪ F} {Q : F[Z][X][Y]}
    (δ : ℚ≥0) (u₀ u₁ : Fin n → F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (Dtop : Finset (Fin n))
    (hDtop_card : Dtop.card = k + 1)
    (hsubset : ∀ x ∈ Dtop,
      coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) u₀ u₁ ⊆
        matching_set_at_x k (δ : ℚ) h_gs x)
    (hunique : ∀ P : F → F[X],
      (∀ z ∈ coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) u₀ u₁,
        (P z).natDegree < k + 1 ∧ δᵣ(u₀ + z • u₁, (P z).eval ∘ ωs) ≤ (δ : ℚ)) →
      ∀ z ∈ coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) u₀ u₁,
        P z = PzFamily (F := F) (n := n) (δ : ℚ) u₀ u₁ ωs k z) :
    ∀ P : F → F[X],
      (∀ z ∈ RS_goodCoeffsCurve (k := 1) (deg := k + 1) (domain := ωs)
          (Code.finMapTwoWords u₀ u₁) (δ : ℝ≥0),
        (P z).natDegree < k + 1 ∧
          δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • Code.finMapTwoWords u₀ u₁ t,
            (P z).eval ∘ ωs) ≤ (δ : ℝ≥0)) →
        ∃ B : ℕ → F[X],
          (∀ j < k + 1, (B j).natDegree < 1 + 1) ∧
            ∀ z ∈ RS_goodCoeffsCurve (k := 1) (deg := k + 1) (domain := ωs)
                (Code.finMapTwoWords u₀ u₁) (δ : ℝ≥0),
              ∀ j < k + 1, (P z).coeff j = (B j).eval z := by
  classical
  intro P hP
  let P₀ : F → F[X] := PzFamily (F := F) (n := n) (δ : ℚ) u₀ u₁ ωs k
  have hP_close :
      ∀ z ∈ coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) u₀ u₁,
        (P z).natDegree < k + 1 ∧ δᵣ(u₀ + z • u₁, (P z).eval ∘ ωs) ≤ (δ : ℚ) := by
    intro z hz
    have hz_good :
        z ∈ RS_goodCoeffsCurve (k := 1) (deg := k + 1) (domain := ωs)
          (Code.finMapTwoWords u₀ u₁) (δ : ℝ≥0) := by
      exact (coeffs_of_close_proximity_mem_iff_goodCoeffsCurve_finMapTwoWords
        (F := F) (n := n) (k := k) (ωs := ωs) δ u₀ u₁ z).mp hz
    have hzP := hP z hz_good
    exact ⟨hzP.1, by
      simpa [sum_finMapTwoWords_eq, ENNReal.coe_nnratCast] using hzP.2⟩
  have hP_eq : ∀ z ∈ coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) u₀ u₁,
      P z = P₀ z := by
    intro z hz
    exact hunique P hP_close z hz
  obtain ⟨B, hBdeg, hBcoeff₀⟩ :=
    coeff_polys_of_eval_polys_on_finset_domain
      (F := F) (ι := Fin n) (k := 1) (deg := k + 1) (domain := ωs)
      (S := RS_goodCoeffsCurve (k := 1) (deg := k + 1) (domain := ωs)
        (Code.finMapTwoWords u₀ u₁) (δ : ℝ≥0))
      (D := Dtop) (P := P₀)
      (by simp [hDtop_card])
      (by
        intro z hz
        have hz_close :
            z ∈ coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) u₀ u₁ := by
          exact (coeffs_of_close_proximity_mem_iff_goodCoeffsCurve_finMapTwoWords
            (F := F) (n := n) (k := k) (ωs := ωs) δ u₀ u₁ z).mpr hz
        exact (PzFamily_decoded_on_close_set
          (F := F) (n := n) (k := k) (δ := (δ : ℚ)) (u₀ := u₀) (u₁ := u₁)
          (ωs := ωs) z hz_close).1)
      (fun x => lineValuePolynomialFamily (F := F) (n := n) u₀ u₁ x.1)
      (by
        intro x
        simpa [lineValuePolynomialFamily] using
          lineValuePolynomial_natDegree_lt_succ_succ (F := F) (n := n) u₀ u₁ x.1)
      (by
        intro z hz x
        have hz_close :
            z ∈ coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) u₀ u₁ := by
          exact (coeffs_of_close_proximity_mem_iff_goodCoeffsCurve_finMapTwoWords
            (F := F) (n := n) (k := k) (ωs := ωs) δ u₀ u₁ z).mpr hz
        exact PzFamily_eval_eq_lineValuePolynomialFamily_eval_of_mem_matching_set_at_x
          (F := F) (m := m) (n := n) (k := k) (Q := Q) h_gs
          (hsubset x.1 x.2 hz_close))
  refine ⟨B, hBdeg, ?_⟩
  intro z hz j hj
  have hz_close :
      z ∈ coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) u₀ u₁ := by
    exact (coeffs_of_close_proximity_mem_iff_goodCoeffsCurve_finMapTwoWords
      (F := F) (n := n) (k := k) (ωs := ωs) δ u₀ u₁ z).mpr hz
  rw [hP_eq z hz_close]
  exact hBcoeff₀ z hz j hj

open Polynomial in
/-- Canonical coefficient-polynomial package for `PzFamily` on a selected
matching domain, in the exact shape consumed by the strict §6 canonical
coefficient front doors. -/
theorem PzFamily_exists_canonical_coeff_polys_goodCoeffsCurve_finMapTwoWords_of_selected_domain
    {m k : ℕ} {ωs : Fin n ↪ F} {Q : F[Z][X][Y]}
    (δ : ℚ≥0) (u₀ u₁ : Fin n → F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (Dtop : Finset (Fin n))
    (hDtop_card : Dtop.card = k + 1)
    (hsubset : ∀ x ∈ Dtop,
      coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) u₀ u₁ ⊆
        matching_set_at_x k (δ : ℚ) h_gs x)
    (hunique : ∀ P : F → F[X],
      (∀ z ∈ coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) u₀ u₁,
        (P z).natDegree < k + 1 ∧ δᵣ(u₀ + z • u₁, (P z).eval ∘ ωs) ≤ (δ : ℚ)) →
      ∀ z ∈ coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) u₀ u₁,
        P z = PzFamily (F := F) (n := n) (δ : ℚ) u₀ u₁ ωs k z) :
    ∃ P₀ : F → F[X],
      (∃ B : ℕ → F[X],
        (∀ j < k + 1, (B j).natDegree < 1 + 1) ∧
          ∀ z ∈ RS_goodCoeffsCurve (k := 1) (deg := k + 1) (domain := ωs)
              (Code.finMapTwoWords u₀ u₁) (δ : ℝ≥0),
            ∀ j < k + 1, (P₀ z).coeff j = (B j).eval z) ∧
      ∀ P : F → F[X],
        (∀ z ∈ RS_goodCoeffsCurve (k := 1) (deg := k + 1) (domain := ωs)
            (Code.finMapTwoWords u₀ u₁) (δ : ℝ≥0),
          (P z).natDegree < k + 1 ∧
            δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • Code.finMapTwoWords u₀ u₁ t,
              (P z).eval ∘ ωs) ≤ (δ : ℝ≥0)) →
        ∀ z ∈ RS_goodCoeffsCurve (k := 1) (deg := k + 1) (domain := ωs)
            (Code.finMapTwoWords u₀ u₁) (δ : ℝ≥0),
          P z = P₀ z := by
  classical
  let P₀ : F → F[X] := PzFamily (F := F) (n := n) (δ : ℚ) u₀ u₁ ωs k
  refine ⟨P₀, ?_, ?_⟩
  · refine hcoeffPoly_goodCoeffsCurve_finMapTwoWords_of_selected_matching_domain
      (F := F) (n := n) (m := m) (k := k) (ωs := ωs) (Q := Q)
      δ u₀ u₁ h_gs Dtop hDtop_card hsubset hunique P₀ ?_
    intro z hz
    have hz_close :
        z ∈ coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) u₀ u₁ := by
      exact (coeffs_of_close_proximity_mem_iff_goodCoeffsCurve_finMapTwoWords
        (F := F) (n := n) (k := k) (ωs := ωs) δ u₀ u₁ z).mpr hz
    have hdecoded :=
      PzFamily_decoded_on_close_set
        (F := F) (n := n) (k := k) (δ := (δ : ℚ)) (u₀ := u₀) (u₁ := u₁)
        (ωs := ωs) z hz_close
    exact ⟨hdecoded.1, by
      simpa [P₀, sum_finMapTwoWords_eq, ENNReal.coe_nnratCast] using hdecoded.2⟩
  · intro P hP z hz
    have hz_close :
        z ∈ coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) u₀ u₁ := by
      exact (coeffs_of_close_proximity_mem_iff_goodCoeffsCurve_finMapTwoWords
        (F := F) (n := n) (k := k) (ωs := ωs) δ u₀ u₁ z).mpr hz
    exact hunique P (by
      intro w hw
      have hw_good :
          w ∈ RS_goodCoeffsCurve (k := 1) (deg := k + 1) (domain := ωs)
            (Code.finMapTwoWords u₀ u₁) (δ : ℝ≥0) := by
        exact (coeffs_of_close_proximity_mem_iff_goodCoeffsCurve_finMapTwoWords
          (F := F) (n := n) (k := k) (ωs := ωs) δ u₀ u₁ w).mp hw
      have hwP := hP w hw_good
      exact ⟨hwP.1, by
        simpa [sum_finMapTwoWords_eq, ENNReal.coe_nnratCast] using hwP.2⟩) z hz_close

/-- Strict Johnson §6 joint-agreement front door specialized to the §5
affine-line setup, using only the Claim-5.11 selected coordinate domain. -/
theorem RS_jointAgreement_finMapTwoWords_of_prob_gt_strict_johnson_and_selected_matching_domain
    {m k : ℕ} {ωs : Fin n ↪ F} {Q : F[Z][X][Y]}
    (δ : ℚ≥0) (u₀ u₁ : Fin n → F)
    (hprob :
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • Code.finMapTwoWords u₀ u₁ t,
          ReedSolomon.code ωs (k + 1)) ≤ (δ : ℝ≥0)] >
        (((1 : ℕ) : ENNReal) * (errorBound (δ : ℝ≥0) (k + 1) ωs : ENNReal)))
    (hJ : (1 - (LinearCode.rate (ReedSolomon.code ωs (k + 1)) : ℝ≥0)) / 2 <
      (δ : ℝ≥0))
    (hδ : (δ : ℝ≥0) < 1 - ReedSolomon.sqrtRate (k + 1) ωs)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (Dtop : Finset (Fin n))
    (hDtop_card : Dtop.card = k + 1)
    (hsubset : ∀ x ∈ Dtop,
      coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) u₀ u₁ ⊆
        matching_set_at_x k (δ : ℚ) h_gs x)
    (hunique : ∀ P : F → Polynomial F,
      (∀ z ∈ coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) u₀ u₁,
        (P z).natDegree < k + 1 ∧ δᵣ(u₀ + z • u₁, (P z).eval ∘ ωs) ≤ (δ : ℚ)) →
      ∀ z ∈ coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) u₀ u₁,
        P z = PzFamily (F := F) (n := n) (δ : ℚ) u₀ u₁ ωs k z) :
    jointAgreement (C := ReedSolomon.code ωs (k + 1)) (δ := (δ : ℝ≥0))
      (W := Code.finMapTwoWords u₀ u₁) := by
  classical
  obtain ⟨P₀, hCoeff₀, huniq⟩ :=
    PzFamily_exists_canonical_coeff_polys_goodCoeffsCurve_finMapTwoWords_of_selected_domain
      (F := F) (n := n) (m := m) (k := k) (ωs := ωs) (Q := Q)
      δ u₀ u₁ h_gs Dtop hDtop_card hsubset hunique
  exact RS_jointAgreement_of_prob_gt_strict_johnson_and_canonical_coeff_polys
    (deg := k + 1) (domain := ωs) (δ := (δ : ℝ≥0))
    (hk := Nat.zero_lt_succ 0) (u := Code.finMapTwoWords u₀ u₁)
    hprob hJ hδ P₀ hCoeff₀ huniq

/-- Strict Johnson §6 joint-agreement front door specialized to the §5
affine-line setup, with the selected coordinate domain produced from any
uniform integer bad-coordinate bound `E`.

This is the same bridge as the nat-ceil wrapper below, but it keeps the
bad-coordinate bound abstract.  The nat-ceil version is recovered by taking
`E = ⌈δ * n⌉₊`. -/
theorem RS_jointAgreement_finMapTwoWords_of_prob_gt_strict_johnson_and_delta_nonmatching_bound
    {m k : ℕ} {ωs : Fin n ↪ F} {Q : F[Z][X][Y]} {x₀ : F}
    [DecidableEq (RatFunc F)]
    (δ : ℚ≥0) (u₀ u₁ : Fin n → F)
    (hprob :
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • Code.finMapTwoWords u₀ u₁ t,
          ReedSolomon.code ωs (k + 1)) ≤ (δ : ℝ≥0)] >
        (((1 : ℕ) : ENNReal) * (errorBound (δ : ℝ≥0) (k + 1) ωs : ENNReal)))
    (hJ : (1 - (LinearCode.rate (ReedSolomon.code ωs (k + 1)) : ℝ≥0)) / 2 <
      (δ : ℝ≥0))
    (hδ : (δ : ℝ≥0) < 1 - ReedSolomon.sqrtRate (k + 1) ωs)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    {D E t : ℕ}
    (hE : (δ : ℚ) * (n : ℚ) ≤ E)
    (hcover :
      (coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) u₀ u₁).card - 1 ≤
        (2 * k + 1)
          * (Polynomial.Bivariate.natDegreeY <| H k (δ : ℚ) x₀ h_gs)
          * (Polynomial.Bivariate.natDegreeY <| R k (δ : ℚ) x₀ h_gs)
          * D)
    (hthreshold :
      (2 * k + 1)
        * (Polynomial.Bivariate.natDegreeY <| H k (δ : ℚ) x₀ h_gs)
        * (Polynomial.Bivariate.natDegreeY <| R k (δ : ℚ) x₀ h_gs)
        * D + t ≤ #(coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) u₀ u₁))
    (hsmall :
      E * #(coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) u₀ u₁) <
        (n - k) * t)
    (hunique : ∀ P : F → Polynomial F,
      (∀ z ∈ coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) u₀ u₁,
        (P z).natDegree < k + 1 ∧ δᵣ(u₀ + z • u₁, (P z).eval ∘ ωs) ≤ (δ : ℚ)) →
      ∀ z ∈ coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) u₀ u₁,
        P z = PzFamily (F := F) (n := n) (δ : ℚ) u₀ u₁ ωs k z) :
    jointAgreement (C := ReedSolomon.code ωs (k + 1)) (δ := (δ : ℝ≥0))
      (W := Code.finMapTwoWords u₀ u₁) := by
  classical
  obtain ⟨Dtop, hDtop_card, hsubset⟩ :=
    exists_points_with_close_subset_matching_set_of_delta_nonmatching_bound
      (F := F) (m := m) (n := n) (k := k) (Q := Q) (δ := (δ : ℚ)) (x₀ := x₀)
      h_gs (D := D) (E := E) (t := t) hE hcover hthreshold hsmall
  exact RS_jointAgreement_finMapTwoWords_of_prob_gt_strict_johnson_and_selected_matching_domain
    (F := F) (n := n) (m := m) (k := k) (ωs := ωs) (Q := Q)
    δ u₀ u₁ hprob hJ hδ h_gs Dtop hDtop_card hsubset hunique

/-- Strict Johnson §6 joint-agreement front door specialized to the §5
affine-line setup, with the selected coordinate domain produced by the
nat-ceil nonmatching-coordinate form of Claim 5.11. -/
theorem RS_jointAgreement_finMapTwoWords_of_prob_gt_strict_johnson_and_natCeil_nonmatching_bound
    {m k : ℕ} {ωs : Fin n ↪ F} {Q : F[Z][X][Y]} {x₀ : F}
    [DecidableEq (RatFunc F)]
    (δ : ℚ≥0) (u₀ u₁ : Fin n → F)
    (hprob :
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • Code.finMapTwoWords u₀ u₁ t,
          ReedSolomon.code ωs (k + 1)) ≤ (δ : ℝ≥0)] >
        (((1 : ℕ) : ENNReal) * (errorBound (δ : ℝ≥0) (k + 1) ωs : ENNReal)))
    (hJ : (1 - (LinearCode.rate (ReedSolomon.code ωs (k + 1)) : ℝ≥0)) / 2 <
      (δ : ℝ≥0))
    (hδ : (δ : ℝ≥0) < 1 - ReedSolomon.sqrtRate (k + 1) ωs)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    {D t : ℕ}
    (hcover :
      (coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) u₀ u₁).card - 1 ≤
        (2 * k + 1)
          * (Polynomial.Bivariate.natDegreeY <| H k (δ : ℚ) x₀ h_gs)
          * (Polynomial.Bivariate.natDegreeY <| R k (δ : ℚ) x₀ h_gs)
          * D)
    (hthreshold :
      (2 * k + 1)
        * (Polynomial.Bivariate.natDegreeY <| H k (δ : ℚ) x₀ h_gs)
        * (Polynomial.Bivariate.natDegreeY <| R k (δ : ℚ) x₀ h_gs)
        * D + t ≤ #(coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) u₀ u₁))
    (hsmall :
      ⌈(δ : ℚ) * (n : ℚ)⌉₊ *
          #(coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) u₀ u₁) <
        (n - k) * t)
    (hunique : ∀ P : F → Polynomial F,
      (∀ z ∈ coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) u₀ u₁,
        (P z).natDegree < k + 1 ∧ δᵣ(u₀ + z • u₁, (P z).eval ∘ ωs) ≤ (δ : ℚ)) →
      ∀ z ∈ coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) u₀ u₁,
        P z = PzFamily (F := F) (n := n) (δ : ℚ) u₀ u₁ ωs k z) :
    jointAgreement (C := ReedSolomon.code ωs (k + 1)) (δ := (δ : ℝ≥0))
      (W := Code.finMapTwoWords u₀ u₁) := by
  classical
  exact RS_jointAgreement_finMapTwoWords_of_prob_gt_strict_johnson_and_delta_nonmatching_bound
    (F := F) (n := n) (m := m) (k := k) (ωs := ωs) (Q := Q)
    (x₀ := x₀) δ u₀ u₁ hprob hJ hδ h_gs
    (D := D) (E := ⌈(δ : ℚ) * (n : ℚ)⌉₊) (t := t)
    (Nat.le_ceil _) hcover hthreshold hsmall hunique

/-- Strict Johnson §6 joint-agreement front door specialized to the §5
affine-line setup, with the `ModifiedGuruswami` solution produced by Claim
5.4 and the selected coordinate domain produced by the nat-ceil Claim-5.11
counting package for that chosen solution. -/
theorem RS_jointAgreement_finMapTwoWords_of_prob_gt_strict_johnson_and_exists_natCeil_counting
    {m k : ℕ} (hk : 0 < k) {ωs : Fin n ↪ F}
    [DecidableEq (RatFunc F)]
    (δ : ℚ≥0) (u₀ u₁ : Fin n → F)
    (hDx : ((gsDpg n m k : ℕ) : ℝ) < D_X ((k + 1) / (n : ℚ)) n m)
    (hYZ : ((gsDpg n m k + gsZCap n m k : ℕ) : ℝ) ≤
      n * (m + 1 / (2 : ℚ)) ^ 3 / (6 * Real.sqrt ((k + 1) / n)))
    (hprob :
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • Code.finMapTwoWords u₀ u₁ t,
          ReedSolomon.code ωs (k + 1)) ≤ (δ : ℝ≥0)] >
        (((1 : ℕ) : ENNReal) * (errorBound (δ : ℝ≥0) (k + 1) ωs : ENNReal)))
    (hJ : (1 - (LinearCode.rate (ReedSolomon.code ωs (k + 1)) : ℝ≥0)) / 2 <
      (δ : ℝ≥0))
    (hδ : (δ : ℝ≥0) < 1 - ReedSolomon.sqrtRate (k + 1) ωs)
    (hcounting : ∀ {Q : F[Z][X][Y]} (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁),
      ∃ (x₀ : F) (D t : ℕ),
        (coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) u₀ u₁).card - 1 ≤
          (2 * k + 1)
            * (Polynomial.Bivariate.natDegreeY <| H k (δ : ℚ) x₀ h_gs)
            * (Polynomial.Bivariate.natDegreeY <| R k (δ : ℚ) x₀ h_gs)
            * D ∧
        (2 * k + 1)
          * (Polynomial.Bivariate.natDegreeY <| H k (δ : ℚ) x₀ h_gs)
          * (Polynomial.Bivariate.natDegreeY <| R k (δ : ℚ) x₀ h_gs)
          * D + t ≤ #(coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) u₀ u₁) ∧
        ⌈(δ : ℚ) * (n : ℚ)⌉₊ *
            #(coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) u₀ u₁) <
          (n - k) * t)
    (hunique : ∀ {Q : F[Z][X][Y]} (_h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
      (P : F → Polynomial F),
      (∀ z ∈ coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) u₀ u₁,
        (P z).natDegree < k + 1 ∧ δᵣ(u₀ + z • u₁, (P z).eval ∘ ωs) ≤ (δ : ℚ)) →
      ∀ z ∈ coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) u₀ u₁,
        P z = PzFamily (F := F) (n := n) (δ : ℚ) u₀ u₁ ωs k z) :
    jointAgreement (C := ReedSolomon.code ωs (k + 1)) (δ := (δ : ℝ≥0))
      (W := Code.finMapTwoWords u₀ u₁) := by
  classical
  obtain ⟨Q, h_gs⟩ :=
    modified_guruswami_has_a_solution (F := F) (m := m) (n := n) (k := k)
      (Nat.pos_of_neZero n) hk (ωs := ωs) (u₀ := u₀) (u₁ := u₁) hDx hYZ
  obtain ⟨x₀, D, t, hcover, hthreshold, hsmall⟩ := hcounting h_gs
  exact RS_jointAgreement_finMapTwoWords_of_prob_gt_strict_johnson_and_natCeil_nonmatching_bound
    (F := F) (n := n) (m := m) (k := k) (ωs := ωs) (Q := Q) (x₀ := x₀)
    δ u₀ u₁ hprob hJ hδ h_gs
    (D := D) (t := t) hcover hthreshold hsmall (hunique h_gs)

/-- Strict square-root-radius degree-one correlated-agreement capstone in the
native §5 affine-line language, with Claim-5.11 supplied in its nat-ceil
counting form for every affine line.

This is the strict-radius analogue of the `PzFamily` capstone below, but it
uses only the selected-domain coefficient-polynomial bridge; callers no longer
need matching-set coverage at every coordinate. -/
theorem correlatedAgreement_affine_lines_of_strict_exists_natCeil_counting
    {m k : ℕ} (hk : 0 < k) {ωs : Fin n ↪ F}
    [DecidableEq (RatFunc F)]
    (δ : ℚ≥0)
    (hδ : (δ : ℝ≥0) < 1 - ReedSolomon.sqrtRate (k + 1) ωs)
    (hDx : ((gsDpg n m k : ℕ) : ℝ) < D_X ((k + 1) / (n : ℚ)) n m)
    (hYZ : ((gsDpg n m k + gsZCap n m k : ℕ) : ℝ) ≤
      n * (m + 1 / (2 : ℚ)) ^ 3 / (6 * Real.sqrt ((k + 1) / n)))
    (hcounting : ∀ (u₀ u₁ : Fin n → F) {Q : F[Z][X][Y]}
      (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁),
      ∃ (x₀ : F) (D t : ℕ),
        (coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) u₀ u₁).card - 1 ≤
          (2 * k + 1)
            * (Polynomial.Bivariate.natDegreeY <| H k (δ : ℚ) x₀ h_gs)
            * (Polynomial.Bivariate.natDegreeY <| R k (δ : ℚ) x₀ h_gs)
            * D ∧
        (2 * k + 1)
          * (Polynomial.Bivariate.natDegreeY <| H k (δ : ℚ) x₀ h_gs)
          * (Polynomial.Bivariate.natDegreeY <| R k (δ : ℚ) x₀ h_gs)
          * D + t ≤ #(coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) u₀ u₁) ∧
        ⌈(δ : ℚ) * (n : ℚ)⌉₊ *
            #(coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) u₀ u₁) <
          (n - k) * t)
    (hunique : ∀ (u₀ u₁ : Fin n → F) {Q : F[Z][X][Y]}
      (_h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁) (P : F → Polynomial F),
      (∀ z ∈ coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) u₀ u₁,
        (P z).natDegree < k + 1 ∧ δᵣ(u₀ + z • u₁, (P z).eval ∘ ωs) ≤ (δ : ℚ)) →
      ∀ z ∈ coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) u₀ u₁,
        P z = PzFamily (F := F) (n := n) (δ : ℚ) u₀ u₁ ωs k z) :
    δ_ε_correlatedAgreementCurves (k := 1) (A := F) (F := F) (ι := Fin n)
      (C := ReedSolomon.code ωs (k + 1)) (δ := (δ : ℝ≥0))
      (ε := errorBound (δ : ℝ≥0) (k + 1) ωs) := by
  classical
  refine correlatedAgreement_affine_curves_of_uniform_strict_coeff_polys
    (k := 1) (deg := k + 1) (domain := ωs) (δ := (δ : ℝ≥0)) hδ ?_
  intro u P hP
  have h_u_eq := wordStack_fin_two_eq_finMapTwoWords (F := F) (n := n) u
  rw [h_u_eq] at hP ⊢
  obtain ⟨Q, h_gs⟩ :=
    modified_guruswami_has_a_solution (F := F) (m := m) (n := n) (k := k)
      (Nat.pos_of_neZero n) hk (ωs := ωs) (u₀ := u 0) (u₁ := u 1) hDx hYZ
  obtain ⟨x₀, D, t, hcover, hthreshold, hsmall⟩ := hcounting (u 0) (u 1) h_gs
  obtain ⟨Dtop, hDtop_card, hsubset⟩ :=
    exists_points_with_close_subset_matching_set_of_natCeil_delta_nonmatching_bound
      (F := F) (m := m) (n := n) (k := k) (Q := Q) (δ := (δ : ℚ)) (x₀ := x₀)
      h_gs (D := D) (t := t) hcover hthreshold hsmall
  exact hcoeffPoly_goodCoeffsCurve_finMapTwoWords_of_selected_matching_domain
    (F := F) (n := n) (m := m) (k := k) (ωs := ωs) (Q := Q)
    δ (u 0) (u 1) h_gs Dtop hDtop_card hsubset (hunique (u 0) (u 1) h_gs) P hP

/-- Strict Johnson §6 joint-agreement front door specialized to the §5
degree-one affine-line setup.  The remaining hypotheses are exactly the §5
matching-set coverage and uniqueness data needed to build the canonical
`PzFamily` package. -/
theorem RS_jointAgreement_finMapTwoWords_of_prob_gt_strict_johnson_and_PzFamily
    {m k : ℕ} {ωs : Fin n ↪ F} {Q : F[Z][X][Y]}
    (δ : ℚ≥0) (u₀ u₁ : Fin n → F)
    (hprob :
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • Code.finMapTwoWords u₀ u₁ t,
          ReedSolomon.code ωs (k + 1)) ≤ (δ : ℝ≥0)] >
        (((1 : ℕ) : ENNReal) * (errorBound (δ : ℝ≥0) (k + 1) ωs : ENNReal)))
    (hJ : (1 - (LinearCode.rate (ReedSolomon.code ωs (k + 1)) : ℝ≥0)) / 2 <
      (δ : ℝ≥0))
    (hδ : (δ : ℝ≥0) < 1 - ReedSolomon.sqrtRate (k + 1) ωs)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hsubset : ∀ x : Fin n,
      coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) u₀ u₁ ⊆
        matching_set_at_x k (δ : ℚ) h_gs x)
    (hunique : ∀ P : F → Polynomial F,
      (∀ z ∈ coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) u₀ u₁,
        (P z).natDegree < k + 1 ∧ δᵣ(u₀ + z • u₁, (P z).eval ∘ ωs) ≤ (δ : ℚ)) →
      ∀ z ∈ coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) u₀ u₁,
        P z = PzFamily (F := F) (n := n) (δ : ℚ) u₀ u₁ ωs k z) :
    jointAgreement (C := ReedSolomon.code ωs (k + 1)) (δ := (δ : ℝ≥0))
      (W := Code.finMapTwoWords u₀ u₁) := by
  classical
  obtain ⟨P₀, hP₀, hEval₀, huniq⟩ :=
    PzFamily_exists_canonical_eval_polys_goodCoeffsCurve_finMapTwoWords
      (F := F) (n := n) (m := m) (k := k) (ωs := ωs) (Q := Q)
      δ u₀ u₁ h_gs hsubset hunique
  exact RS_jointAgreement_of_prob_gt_strict_johnson_and_canonical_eval_polys
    (deg := k + 1) (domain := ωs) (δ := (δ : ℝ≥0))
    (hk := Nat.zero_lt_succ 0) (u := Code.finMapTwoWords u₀ u₁)
    hprob hJ hδ P₀ hEval₀ huniq

/-- Strict Johnson §6 joint-agreement front door specialized to the §5
degree-one affine-line setup, with the `ModifiedGuruswami` solution produced
by Claim 5.4's current constructive existence theorem.

The remaining caller obligations are the regime side conditions for the
Guruswami-Sudan construction and the matching-set/uniqueness facts for the
chosen solution. -/
theorem RS_jointAgreement_finMapTwoWords_of_prob_gt_strict_johnson_and_exists_PzFamily
    {m k : ℕ} (hk : 0 < k) {ωs : Fin n ↪ F}
    (δ : ℚ≥0) (u₀ u₁ : Fin n → F)
    (hDx : ((gsDpg n m k : ℕ) : ℝ) < D_X ((k + 1) / (n : ℚ)) n m)
    (hYZ : ((gsDpg n m k + gsZCap n m k : ℕ) : ℝ) ≤
      n * (m + 1 / (2 : ℚ)) ^ 3 / (6 * Real.sqrt ((k + 1) / n)))
    (hprob :
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • Code.finMapTwoWords u₀ u₁ t,
          ReedSolomon.code ωs (k + 1)) ≤ (δ : ℝ≥0)] >
        (((1 : ℕ) : ENNReal) * (errorBound (δ : ℝ≥0) (k + 1) ωs : ENNReal)))
    (hJ : (1 - (LinearCode.rate (ReedSolomon.code ωs (k + 1)) : ℝ≥0)) / 2 <
      (δ : ℝ≥0))
    (hδ : (δ : ℝ≥0) < 1 - ReedSolomon.sqrtRate (k + 1) ωs)
    (hsubset : ∀ {Q : F[Z][X][Y]}
      (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁) (x : Fin n),
        coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) u₀ u₁ ⊆
          matching_set_at_x k (δ : ℚ) h_gs x)
    (hunique : ∀ P : F → Polynomial F,
        (∀ z ∈ coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) u₀ u₁,
          (P z).natDegree < k + 1 ∧ δᵣ(u₀ + z • u₁, (P z).eval ∘ ωs) ≤ (δ : ℚ)) →
        ∀ z ∈ coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) u₀ u₁,
          P z = PzFamily (F := F) (n := n) (δ : ℚ) u₀ u₁ ωs k z) :
    jointAgreement (C := ReedSolomon.code ωs (k + 1)) (δ := (δ : ℝ≥0))
      (W := Code.finMapTwoWords u₀ u₁) := by
  classical
  obtain ⟨Q, h_gs⟩ :=
    modified_guruswami_has_a_solution (F := F) (m := m) (n := n) (k := k)
      (Nat.pos_of_neZero n) hk (ωs := ωs) (u₀ := u₀) (u₁ := u₁) hDx hYZ
  exact RS_jointAgreement_finMapTwoWords_of_prob_gt_strict_johnson_and_PzFamily
    (F := F) (n := n) (m := m) (k := k) (ωs := ωs) (Q := Q)
    δ u₀ u₁ hprob hJ hδ h_gs
    (fun x => hsubset h_gs x)
    hunique

set_option linter.style.longLine false in
/-- Degree-one correlated-agreement capstone in the native §5 affine-line
language, using the nat-ceil Claim-5.11 counting package for the strict branch
and a boundary-card obligation for the closed square-root boundary. -/
theorem correlatedAgreement_affine_lines_of_strict_exists_natCeil_counting_and_boundary_card
    {m k : ℕ} (hk : 0 < k) {ωs : Fin n ↪ F}
    [DecidableEq (RatFunc F)]
    (δ : ℚ≥0)
    (hδ : (δ : ℝ≥0) ≤ 1 - ReedSolomon.sqrtRate (k + 1) ωs)
    (hDx : ((gsDpg n m k : ℕ) : ℝ) < D_X ((k + 1) / (n : ℚ)) n m)
    (hYZ : ((gsDpg n m k + gsZCap n m k : ℕ) : ℝ) ≤
      n * (m + 1 / (2 : ℚ)) ^ 3 / (6 * Real.sqrt ((k + 1) / n)))
    (hcounting : ∀ (u₀ u₁ : Fin n → F) {Q : F[Z][X][Y]}
      (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁),
      ∃ (x₀ : F) (D t : ℕ),
        (coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) u₀ u₁).card - 1 ≤
          (2 * k + 1)
            * (Polynomial.Bivariate.natDegreeY <| H k (δ : ℚ) x₀ h_gs)
            * (Polynomial.Bivariate.natDegreeY <| R k (δ : ℚ) x₀ h_gs)
            * D ∧
        (2 * k + 1)
          * (Polynomial.Bivariate.natDegreeY <| H k (δ : ℚ) x₀ h_gs)
          * (Polynomial.Bivariate.natDegreeY <| R k (δ : ℚ) x₀ h_gs)
          * D + t ≤ #(coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) u₀ u₁) ∧
        ⌈(δ : ℚ) * (n : ℚ)⌉₊ *
            #(coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) u₀ u₁) <
          (n - k) * t)
    (hunique : ∀ (u₀ u₁ : Fin n → F) {Q : F[Z][X][Y]}
      (_h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁) (P : F → Polynomial F),
      (∀ z ∈ coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) u₀ u₁,
        (P z).natDegree < k + 1 ∧ δᵣ(u₀ + z • u₁, (P z).eval ∘ ωs) ≤ (δ : ℚ)) →
      ∀ z ∈ coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) u₀ u₁,
        P z = PzFamily (F := F) (n := n) (δ : ℚ) u₀ u₁ ωs k z)
    (hBoundaryCard : ∀ u₀ u₁ : Fin n → F,
      (δ : ℝ≥0) = 1 - ReedSolomon.sqrtRate (k + 1) ωs →
      0 < (coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) u₀ u₁).card →
      jointAgreement (C := ReedSolomon.code ωs (k + 1)) (δ := (δ : ℝ≥0))
        (W := Code.finMapTwoWords u₀ u₁)) :
    δ_ε_correlatedAgreementCurves (k := 1) (A := F) (F := F) (ι := Fin n)
      (C := ReedSolomon.code ωs (k + 1)) (δ := (δ : ℝ≥0))
      (ε := errorBound (δ : ℝ≥0) (k + 1) ωs) := by
  classical
  refine correlatedAgreement_affine_curves_of_uniform_strict_coeff_polys_and_boundary_card
    (k := 1) (deg := k + 1) (domain := ωs) (δ := (δ : ℝ≥0)) hδ ?_ ?_
  · intro u P hP
    have h_u_eq := wordStack_fin_two_eq_finMapTwoWords (F := F) (n := n) u
    rw [h_u_eq] at hP ⊢
    obtain ⟨Q, h_gs⟩ :=
      modified_guruswami_has_a_solution (F := F) (m := m) (n := n) (k := k)
        (Nat.pos_of_neZero n) hk (ωs := ωs) (u₀ := u 0) (u₁ := u 1) hDx hYZ
    obtain ⟨x₀, D, t, hcover, hthreshold, hsmall⟩ :=
      hcounting (u 0) (u 1) h_gs
    obtain ⟨Dtop, hDtop_card, hsubset⟩ :=
      exists_points_with_close_subset_matching_set_of_natCeil_delta_nonmatching_bound
        (F := F) (m := m) (n := n) (k := k) (Q := Q) (δ := (δ : ℚ)) (x₀ := x₀)
        h_gs (D := D) (t := t) hcover hthreshold hsmall
    exact hcoeffPoly_goodCoeffsCurve_finMapTwoWords_of_selected_matching_domain
      (F := F) (n := n) (m := m) (k := k) (ωs := ωs) (Q := Q)
      δ (u 0) (u 1) h_gs Dtop hDtop_card hsubset
      (hunique (u 0) (u 1) h_gs) P hP
  · intro _hk u hδeq hcard
    have h_u_eq := wordStack_fin_two_eq_finMapTwoWords (F := F) (n := n) u
    have hcard_close :
        0 < (coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) (u 0) (u 1)).card := by
      rw [coeffs_of_close_proximity_card_eq_goodCoeffsCurve_finMapTwoWords
        (F := F) (n := n) (k := k) (ωs := ωs) δ (u 0) (u 1)]
      rw [h_u_eq] at hcard
      exact hcard
    rw [h_u_eq]
    exact hBoundaryCard (u 0) (u 1) hδeq hcard_close

/-- Degree-one correlated-agreement capstone in the native §5 affine-line
language, exposing the strict branch as one canonical coefficient-polynomial
`PzFamily` package per received word stack.  The selected coordinate domain is
produced from the nat-ceil Claim-5.11 counting package. -/
theorem correlatedAgreement_affine_lines_of_strict_exists_natCeil_counting_canonical_coeff
    {m k : ℕ} (hk : 0 < k) {ωs : Fin n ↪ F}
    [DecidableEq (RatFunc F)]
    (δ : ℚ≥0)
    (hδ : (δ : ℝ≥0) ≤ 1 - ReedSolomon.sqrtRate (k + 1) ωs)
    (hDx : ((gsDpg n m k : ℕ) : ℝ) < D_X ((k + 1) / (n : ℚ)) n m)
    (hYZ : ((gsDpg n m k + gsZCap n m k : ℕ) : ℝ) ≤
      n * (m + 1 / (2 : ℚ)) ^ 3 / (6 * Real.sqrt ((k + 1) / n)))
    (hcounting : ∀ (u₀ u₁ : Fin n → F) {Q : F[Z][X][Y]}
      (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁),
      ∃ (x₀ : F) (D t : ℕ),
        (coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) u₀ u₁).card - 1 ≤
          (2 * k + 1)
            * (Polynomial.Bivariate.natDegreeY <| H k (δ : ℚ) x₀ h_gs)
            * (Polynomial.Bivariate.natDegreeY <| R k (δ : ℚ) x₀ h_gs)
            * D ∧
        (2 * k + 1)
          * (Polynomial.Bivariate.natDegreeY <| H k (δ : ℚ) x₀ h_gs)
          * (Polynomial.Bivariate.natDegreeY <| R k (δ : ℚ) x₀ h_gs)
          * D + t ≤ #(coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) u₀ u₁) ∧
        ⌈(δ : ℚ) * (n : ℚ)⌉₊ *
            #(coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) u₀ u₁) <
          (n - k) * t)
    (hunique : ∀ (u₀ u₁ : Fin n → F) {Q : F[Z][X][Y]}
      (_h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁) (P : F → Polynomial F),
      (∀ z ∈ coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) u₀ u₁,
        (P z).natDegree < k + 1 ∧ δᵣ(u₀ + z • u₁, (P z).eval ∘ ωs) ≤ (δ : ℚ)) →
      ∀ z ∈ coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) u₀ u₁,
        P z = PzFamily (F := F) (n := n) (δ : ℚ) u₀ u₁ ωs k z)
    (hBoundaryCard : ∀ u₀ u₁ : Fin n → F,
      (δ : ℝ≥0) = 1 - ReedSolomon.sqrtRate (k + 1) ωs →
      0 < (coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) u₀ u₁).card →
      jointAgreement (C := ReedSolomon.code ωs (k + 1)) (δ := (δ : ℝ≥0))
        (W := Code.finMapTwoWords u₀ u₁)) :
    δ_ε_correlatedAgreementCurves (k := 1) (A := F) (F := F) (ι := Fin n)
      (C := ReedSolomon.code ωs (k + 1)) (δ := (δ : ℝ≥0))
      (ε := errorBound (δ : ℝ≥0) (k + 1) ωs) := by
  classical
  refine correlatedAgreement_affine_curves_of_uniform_strict_canonical_coeff_polys_and_boundary_card
    (k := 1) (deg := k + 1) (domain := ωs) (δ := (δ : ℝ≥0)) hδ ?_ ?_
  · intro u
    have h_u_eq := wordStack_fin_two_eq_finMapTwoWords (F := F) (n := n) u
    rw [h_u_eq]
    obtain ⟨Q, h_gs⟩ :=
      modified_guruswami_has_a_solution (F := F) (m := m) (n := n) (k := k)
        (Nat.pos_of_neZero n) hk (ωs := ωs) (u₀ := u 0) (u₁ := u 1) hDx hYZ
    obtain ⟨x₀, D, t, hcover, hthreshold, hsmall⟩ :=
      hcounting (u 0) (u 1) h_gs
    obtain ⟨Dtop, hDtop_card, hsubset⟩ :=
      exists_points_with_close_subset_matching_set_of_natCeil_delta_nonmatching_bound
        (F := F) (m := m) (n := n) (k := k) (Q := Q) (δ := (δ : ℚ)) (x₀ := x₀)
        h_gs (D := D) (t := t) hcover hthreshold hsmall
    exact PzFamily_exists_canonical_coeff_polys_goodCoeffsCurve_finMapTwoWords_of_selected_domain
      (F := F) (n := n) (m := m) (k := k) (ωs := ωs) (Q := Q)
      δ (u 0) (u 1) h_gs Dtop hDtop_card hsubset
      (hunique (u 0) (u 1) h_gs)
  · intro _hk u hδeq hcard
    have h_u_eq := wordStack_fin_two_eq_finMapTwoWords (F := F) (n := n) u
    have hcard_close :
        0 < (coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) (u 0) (u 1)).card := by
      rw [coeffs_of_close_proximity_card_eq_goodCoeffsCurve_finMapTwoWords
        (F := F) (n := n) (k := k) (ωs := ωs) δ (u 0) (u 1)]
      rw [h_u_eq] at hcard
      exact hcard
    rw [h_u_eq]
    exact hBoundaryCard (u 0) (u 1) hδeq hcard_close

/-- Degree-one correlated-agreement capstone in the native §5 affine-line
language, with Claim-5.11 counting supplied in the complement-threshold
arithmetic shape.  This is the same canonical-coefficient front door as
`correlatedAgreement_affine_lines_of_strict_exists_natCeil_counting_canonical_coeff`,
but the strict branch uses the natural slack `#S - threshold` directly. -/
theorem correlatedAgreement_affine_lines_of_strict_exists_natCeil_complement_counting_canonical_coeff
    {m k : ℕ} (hk : 0 < k) {ωs : Fin n ↪ F}
    [DecidableEq (RatFunc F)]
    (δ : ℚ≥0)
    (hδ : (δ : ℝ≥0) ≤ 1 - ReedSolomon.sqrtRate (k + 1) ωs)
    (hDx : ((gsDpg n m k : ℕ) : ℝ) < D_X ((k + 1) / (n : ℚ)) n m)
    (hYZ : ((gsDpg n m k + gsZCap n m k : ℕ) : ℝ) ≤
      n * (m + 1 / (2 : ℚ)) ^ 3 / (6 * Real.sqrt ((k + 1) / n)))
    (hcounting : ∀ (u₀ u₁ : Fin n → F) {Q : F[Z][X][Y]}
      (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁),
      ∃ (x₀ : F) (D : ℕ),
        (coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) u₀ u₁).card - 1 ≤
          (2 * k + 1)
            * (Polynomial.Bivariate.natDegreeY <| H k (δ : ℚ) x₀ h_gs)
            * (Polynomial.Bivariate.natDegreeY <| R k (δ : ℚ) x₀ h_gs)
            * D ∧
        (2 * k + 1)
          * (Polynomial.Bivariate.natDegreeY <| H k (δ : ℚ) x₀ h_gs)
          * (Polynomial.Bivariate.natDegreeY <| R k (δ : ℚ) x₀ h_gs)
          * D ≤ #(coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) u₀ u₁) ∧
        ⌈(δ : ℚ) * (n : ℚ)⌉₊ *
            #(coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) u₀ u₁) <
          (n - k) *
            (#(coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) u₀ u₁) -
              (2 * k + 1)
                * (Polynomial.Bivariate.natDegreeY <| H k (δ : ℚ) x₀ h_gs)
                * (Polynomial.Bivariate.natDegreeY <| R k (δ : ℚ) x₀ h_gs)
                * D))
    (hunique : ∀ (u₀ u₁ : Fin n → F) {Q : F[Z][X][Y]}
      (_h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁) (P : F → Polynomial F),
      (∀ z ∈ coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) u₀ u₁,
        (P z).natDegree < k + 1 ∧ δᵣ(u₀ + z • u₁, (P z).eval ∘ ωs) ≤ (δ : ℚ)) →
      ∀ z ∈ coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) u₀ u₁,
        P z = PzFamily (F := F) (n := n) (δ : ℚ) u₀ u₁ ωs k z)
    (hBoundaryCard : ∀ u₀ u₁ : Fin n → F,
      (δ : ℝ≥0) = 1 - ReedSolomon.sqrtRate (k + 1) ωs →
      0 < (coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) u₀ u₁).card →
      jointAgreement (C := ReedSolomon.code ωs (k + 1)) (δ := (δ : ℝ≥0))
        (W := Code.finMapTwoWords u₀ u₁)) :
    δ_ε_correlatedAgreementCurves (k := 1) (A := F) (F := F) (ι := Fin n)
      (C := ReedSolomon.code ωs (k + 1)) (δ := (δ : ℝ≥0))
      (ε := errorBound (δ : ℝ≥0) (k + 1) ωs) := by
  classical
  refine correlatedAgreement_affine_curves_of_uniform_strict_canonical_coeff_polys_and_boundary_card
    (k := 1) (deg := k + 1) (domain := ωs) (δ := (δ : ℝ≥0)) hδ ?_ ?_
  · intro u
    have h_u_eq := wordStack_fin_two_eq_finMapTwoWords (F := F) (n := n) u
    rw [h_u_eq]
    obtain ⟨Q, h_gs⟩ :=
      modified_guruswami_has_a_solution (F := F) (m := m) (n := n) (k := k)
        (Nat.pos_of_neZero n) hk (ωs := ωs) (u₀ := u 0) (u₁ := u 1) hDx hYZ
    obtain ⟨x₀, D, hcover, hthreshold, hsmall⟩ := hcounting (u 0) (u 1) h_gs
    obtain ⟨Dtop, hDtop_card, hsubset⟩ :=
      exists_points_with_close_subset_matching_set_claim511_complement
        (F := F) (m := m) (n := n) (k := k) (Q := Q) (δ := (δ : ℚ)) (x₀ := x₀)
        h_gs (D := D) hcover hthreshold hsmall
    exact PzFamily_exists_canonical_coeff_polys_goodCoeffsCurve_finMapTwoWords_of_selected_domain
      (F := F) (n := n) (m := m) (k := k) (ωs := ωs) (Q := Q)
      δ (u 0) (u 1) h_gs Dtop hDtop_card hsubset
      (hunique (u 0) (u 1) h_gs)
  · intro _hk u hδeq hcard
    have h_u_eq := wordStack_fin_two_eq_finMapTwoWords (F := F) (n := n) u
    have hcard_close :
        0 < (coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) (u 0) (u 1)).card := by
      rw [coeffs_of_close_proximity_card_eq_goodCoeffsCurve_finMapTwoWords
        (F := F) (n := n) (k := k) (ωs := ωs) δ (u 0) (u 1)]
      rw [h_u_eq] at hcard
      exact hcard
    rw [h_u_eq]
    exact hBoundaryCard (u 0) (u 1) hδeq hcard_close

/-- Strict Johnson canonical-evaluation supplier for the §6 curve front doors,
specialized to §5 affine lines represented as `Code.finMapTwoWords`.

This factors the exact hypothesis shape consumed by
`correlatedAgreement_affine_curves_of_strict_canonical_eval_polys` out of the
capstone theorem below. The remaining assumptions are the §5 Guruswami-Sudan
existence side conditions plus matching-set coverage and uniqueness for each
affine line. -/
theorem section5_strict_canonical_eval_polys_for_RS_goodCoeffsCurve_finMapTwoWords
    {m k : ℕ} (hk : 0 < k) {ωs : Fin n ↪ F}
    (δ : ℚ≥0)
    (hDx : ((gsDpg n m k : ℕ) : ℝ) < D_X ((k + 1) / (n : ℚ)) n m)
    (hYZ : ((gsDpg n m k + gsZCap n m k : ℕ) : ℝ) ≤
      n * (m + 1 / (2 : ℚ)) ^ 3 / (6 * Real.sqrt ((k + 1) / n)))
    (hsubset : ∀ (u₀ u₁ : Fin n → F) {Q : F[Z][X][Y]}
      (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁) (x : Fin n),
        coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) u₀ u₁ ⊆
          matching_set_at_x k (δ : ℚ) h_gs x)
    (hunique : ∀ (u₀ u₁ : Fin n → F) (P : F → Polynomial F),
        (∀ z ∈ coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) u₀ u₁,
          (P z).natDegree < k + 1 ∧ δᵣ(u₀ + z • u₁, (P z).eval ∘ ωs) ≤ (δ : ℚ)) →
        ∀ z ∈ coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) u₀ u₁,
          P z = PzFamily (F := F) (n := n) (δ : ℚ) u₀ u₁ ωs k z) :
    ∀ (_hk : 0 < (1 : ℕ)) (u : WordStack F (Fin (1 + 1)) (Fin n)),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin (1 + 1), (z ^ (t : ℕ)) • u t,
          ReedSolomon.code ωs (k + 1)) ≤ (δ : ℝ≥0)] >
          (((1 : ℕ) : ENNReal) * (errorBound (δ : ℝ≥0) (k + 1) ωs : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code ωs (k + 1)) : ℝ≥0)) / 2 <
        (δ : ℝ≥0) →
      ∃ P₀ : F → Polynomial F,
        (∃ E : Fin n → Polynomial F,
          (∀ x, (E x).natDegree < 1 + 1) ∧
            ∀ z ∈ RS_goodCoeffsCurve (k := 1) (deg := k + 1) (domain := ωs)
                u (δ : ℝ≥0),
              ∀ x : Fin n, (P₀ z).eval (ωs x) = (E x).eval z) ∧
        ∀ P : F → Polynomial F,
          (∀ z ∈ RS_goodCoeffsCurve (k := 1) (deg := k + 1) (domain := ωs)
              u (δ : ℝ≥0),
            (P z).natDegree < k + 1 ∧
              δᵣ(∑ t : Fin (1 + 1), (z ^ (t : ℕ)) • u t,
                (P z).eval ∘ ωs) ≤ (δ : ℝ≥0)) →
          ∀ z ∈ RS_goodCoeffsCurve (k := 1) (deg := k + 1) (domain := ωs)
              u (δ : ℝ≥0),
            P z = P₀ z := by
  classical
  intro _hk u _hprob _hJ
  have h_u_eq := wordStack_fin_two_eq_finMapTwoWords (F := F) (n := n) u
  obtain ⟨Q, h_gs⟩ :=
    modified_guruswami_has_a_solution (F := F) (m := m) (n := n) (k := k)
      (Nat.pos_of_neZero n) hk (ωs := ωs) (u₀ := u 0) (u₁ := u 1) hDx hYZ
  obtain ⟨P₀, _hDecoded, hEval, huniq⟩ :=
    PzFamily_exists_canonical_eval_polys_goodCoeffsCurve_finMapTwoWords
      (F := F) (n := n) (m := m) (k := k) (ωs := ωs) (Q := Q)
      δ (u 0) (u 1) h_gs
      (fun x => hsubset (u 0) (u 1) h_gs x)
      (hunique (u 0) (u 1))
  rw [h_u_eq]
  exact ⟨P₀, hEval, huniq⟩

/-- Strict Johnson evaluation-polynomial supplier for the §6 curve front doors,
derived from the canonical `PzFamily` supplier above. -/
theorem section5_strict_eval_polys_for_RS_goodCoeffsCurve_finMapTwoWords
    {m k : ℕ} (hk : 0 < k) {ωs : Fin n ↪ F}
    (δ : ℚ≥0)
    (hDx : ((gsDpg n m k : ℕ) : ℝ) < D_X ((k + 1) / (n : ℚ)) n m)
    (hYZ : ((gsDpg n m k + gsZCap n m k : ℕ) : ℝ) ≤
      n * (m + 1 / (2 : ℚ)) ^ 3 / (6 * Real.sqrt ((k + 1) / n)))
    (hsubset : ∀ (u₀ u₁ : Fin n → F) {Q : F[Z][X][Y]}
      (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁) (x : Fin n),
        coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) u₀ u₁ ⊆
          matching_set_at_x k (δ : ℚ) h_gs x)
    (hunique : ∀ (u₀ u₁ : Fin n → F) (P : F → Polynomial F),
        (∀ z ∈ coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) u₀ u₁,
          (P z).natDegree < k + 1 ∧ δᵣ(u₀ + z • u₁, (P z).eval ∘ ωs) ≤ (δ : ℚ)) →
        ∀ z ∈ coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) u₀ u₁,
          P z = PzFamily (F := F) (n := n) (δ : ℚ) u₀ u₁ ωs k z) :
    ∀ (_hk : 0 < (1 : ℕ)) (u : WordStack F (Fin (1 + 1)) (Fin n)),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin (1 + 1), (z ^ (t : ℕ)) • u t,
          ReedSolomon.code ωs (k + 1)) ≤ (δ : ℝ≥0)] >
          (((1 : ℕ) : ENNReal) * (errorBound (δ : ℝ≥0) (k + 1) ωs : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code ωs (k + 1)) : ℝ≥0)) / 2 <
        (δ : ℝ≥0) →
      ∀ P : F → Polynomial F,
        (∀ z ∈ RS_goodCoeffsCurve (k := 1) (deg := k + 1) (domain := ωs)
            u (δ : ℝ≥0),
          (P z).natDegree < k + 1 ∧
            δᵣ(∑ t : Fin (1 + 1), (z ^ (t : ℕ)) • u t,
              (P z).eval ∘ ωs) ≤ (δ : ℝ≥0)) →
        ∃ E : Fin n → Polynomial F,
          (∀ x, (E x).natDegree < 1 + 1) ∧
            ∀ z ∈ RS_goodCoeffsCurve (k := 1) (deg := k + 1) (domain := ωs)
                u (δ : ℝ≥0),
              ∀ x : Fin n, (P z).eval (ωs x) = (E x).eval z := by
  classical
  intro hk1 u hprob hJ P hP
  obtain ⟨P₀, hEval₀, huniq⟩ :=
    section5_strict_canonical_eval_polys_for_RS_goodCoeffsCurve_finMapTwoWords
      (F := F) (n := n) (m := m) (k := k) hk (ωs := ωs)
      δ hDx hYZ hsubset hunique hk1 u hprob hJ
  exact eval_polys_for_all_decoded_of_canonical_agreement
    (deg := k + 1) (domain := ωs) (δ := (δ : ℝ≥0))
    (S := RS_goodCoeffsCurve (k := 1) (deg := k + 1) (domain := ωs) u (δ : ℝ≥0))
    (u := u) P₀ hEval₀ huniq P hP

/-- Degree-one correlated-agreement capstone in the native §5 affine-line
language, using the raw strict evaluation-polynomial front door. This is the
same mathematical content as
`correlatedAgreement_affine_lines_of_strict_exists_PzFamily_and_boundary_card`,
but exposes the §5 extraction in the non-canonical hypothesis shape consumed by
`correlatedAgreement_affine_curves_of_strict_eval_polys_and_boundary_card`. -/
theorem correlatedAgreement_affine_lines_of_strict_eval_polys_and_boundary_card
    {m k : ℕ} (hk : 0 < k) {ωs : Fin n ↪ F}
    (δ : ℚ≥0)
    (hδ : (δ : ℝ≥0) ≤ 1 - ReedSolomon.sqrtRate (k + 1) ωs)
    (hDx : ((gsDpg n m k : ℕ) : ℝ) < D_X ((k + 1) / (n : ℚ)) n m)
    (hYZ : ((gsDpg n m k + gsZCap n m k : ℕ) : ℝ) ≤
      n * (m + 1 / (2 : ℚ)) ^ 3 / (6 * Real.sqrt ((k + 1) / n)))
    (hsubset : ∀ (u₀ u₁ : Fin n → F) {Q : F[Z][X][Y]}
      (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁) (x : Fin n),
        coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) u₀ u₁ ⊆
          matching_set_at_x k (δ : ℚ) h_gs x)
    (hunique : ∀ (u₀ u₁ : Fin n → F) (P : F → Polynomial F),
        (∀ z ∈ coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) u₀ u₁,
          (P z).natDegree < k + 1 ∧ δᵣ(u₀ + z • u₁, (P z).eval ∘ ωs) ≤ (δ : ℚ)) →
        ∀ z ∈ coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) u₀ u₁,
          P z = PzFamily (F := F) (n := n) (δ : ℚ) u₀ u₁ ωs k z)
    (hBoundaryCard : ∀ u₀ u₁ : Fin n → F,
      (δ : ℝ≥0) = 1 - ReedSolomon.sqrtRate (k + 1) ωs →
      0 < (coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) u₀ u₁).card →
      jointAgreement (C := ReedSolomon.code ωs (k + 1)) (δ := (δ : ℝ≥0))
        (W := Code.finMapTwoWords u₀ u₁)) :
    δ_ε_correlatedAgreementCurves (k := 1) (A := F) (F := F) (ι := Fin n)
      (C := ReedSolomon.code ωs (k + 1)) (δ := (δ : ℝ≥0))
      (ε := errorBound (δ : ℝ≥0) (k + 1) ωs) := by
  classical
  refine correlatedAgreement_affine_curves_of_strict_eval_polys_and_boundary_card
    (k := 1) (deg := k + 1) (domain := ωs) (δ := (δ : ℝ≥0)) hδ ?_ ?_
  · intro hk1 u hprob hJ _hsqrt
    exact section5_strict_eval_polys_for_RS_goodCoeffsCurve_finMapTwoWords
      (F := F) (n := n) (m := m) (k := k) hk (ωs := ωs) δ hDx hYZ hsubset hunique
      hk1 u hprob hJ
  · intro _hk u hδeq hcard
    have h_u_eq := wordStack_fin_two_eq_finMapTwoWords (F := F) (n := n) u
    have hcard_close :
        0 < (coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) (u 0) (u 1)).card := by
      rw [coeffs_of_close_proximity_card_eq_goodCoeffsCurve_finMapTwoWords
        (F := F) (n := n) (k := k) (ωs := ωs) δ (u 0) (u 1)]
      rw [h_u_eq] at hcard
      exact hcard
    rw [h_u_eq]
    exact hBoundaryCard (u 0) (u 1) hδeq hcard_close

/-- Strict square-root-radius degree-one correlated-agreement capstone in the
native §5 affine-line language, using the raw strict evaluation-polynomial
front door. -/
theorem correlatedAgreement_affine_lines_of_strict_eval_polys
    {m k : ℕ} (hk : 0 < k) {ωs : Fin n ↪ F}
    (δ : ℚ≥0)
    (hδ : (δ : ℝ≥0) < 1 - ReedSolomon.sqrtRate (k + 1) ωs)
    (hDx : ((gsDpg n m k : ℕ) : ℝ) < D_X ((k + 1) / (n : ℚ)) n m)
    (hYZ : ((gsDpg n m k + gsZCap n m k : ℕ) : ℝ) ≤
      n * (m + 1 / (2 : ℚ)) ^ 3 / (6 * Real.sqrt ((k + 1) / n)))
    (hsubset : ∀ (u₀ u₁ : Fin n → F) {Q : F[Z][X][Y]}
      (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁) (x : Fin n),
        coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) u₀ u₁ ⊆
          matching_set_at_x k (δ : ℚ) h_gs x)
    (hunique : ∀ (u₀ u₁ : Fin n → F) (P : F → Polynomial F),
        (∀ z ∈ coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) u₀ u₁,
          (P z).natDegree < k + 1 ∧ δᵣ(u₀ + z • u₁, (P z).eval ∘ ωs) ≤ (δ : ℚ)) →
        ∀ z ∈ coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) u₀ u₁,
          P z = PzFamily (F := F) (n := n) (δ : ℚ) u₀ u₁ ωs k z) :
    δ_ε_correlatedAgreementCurves (k := 1) (A := F) (F := F) (ι := Fin n)
      (C := ReedSolomon.code ωs (k + 1)) (δ := (δ : ℝ≥0))
      (ε := errorBound (δ : ℝ≥0) (k + 1) ωs) := by
  classical
  refine correlatedAgreement_affine_curves_of_strict_eval_polys
    (k := 1) (deg := k + 1) (domain := ωs) (δ := (δ : ℝ≥0)) hδ ?_
  intro hk1 u hprob hJ P hP
  exact section5_strict_eval_polys_for_RS_goodCoeffsCurve_finMapTwoWords
    (F := F) (n := n) (m := m) (k := k) hk (ωs := ωs) δ hDx hYZ hsubset hunique
    hk1 u hprob hJ P hP

/-- Degree-one correlated-agreement capstone in the native §5 affine-line
language. The generic §6 theorem quantifies over arbitrary
`WordStack F (Fin 2) (Fin n)`; this wrapper identifies every such stack with
`Code.finMapTwoWords (u 0) (u 1)` and transports both the strict
`PzFamily` package and the closed-boundary cardinality obligation through the
§5/§6 close-set equality. -/
theorem correlatedAgreement_affine_lines_of_strict_exists_PzFamily_and_boundary_card
    {m k : ℕ} (hk : 0 < k) {ωs : Fin n ↪ F}
    (δ : ℚ≥0)
    (hδ : (δ : ℝ≥0) ≤ 1 - ReedSolomon.sqrtRate (k + 1) ωs)
    (hDx : ((gsDpg n m k : ℕ) : ℝ) < D_X ((k + 1) / (n : ℚ)) n m)
    (hYZ : ((gsDpg n m k + gsZCap n m k : ℕ) : ℝ) ≤
      n * (m + 1 / (2 : ℚ)) ^ 3 / (6 * Real.sqrt ((k + 1) / n)))
    (hsubset : ∀ (u₀ u₁ : Fin n → F) {Q : F[Z][X][Y]}
      (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁) (x : Fin n),
        coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) u₀ u₁ ⊆
          matching_set_at_x k (δ : ℚ) h_gs x)
    (hunique : ∀ (u₀ u₁ : Fin n → F) (P : F → Polynomial F),
        (∀ z ∈ coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) u₀ u₁,
          (P z).natDegree < k + 1 ∧ δᵣ(u₀ + z • u₁, (P z).eval ∘ ωs) ≤ (δ : ℚ)) →
        ∀ z ∈ coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) u₀ u₁,
          P z = PzFamily (F := F) (n := n) (δ : ℚ) u₀ u₁ ωs k z)
    (hBoundaryCard : ∀ u₀ u₁ : Fin n → F,
      (δ : ℝ≥0) = 1 - ReedSolomon.sqrtRate (k + 1) ωs →
      0 < (coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) u₀ u₁).card →
      jointAgreement (C := ReedSolomon.code ωs (k + 1)) (δ := (δ : ℝ≥0))
        (W := Code.finMapTwoWords u₀ u₁)) :
    δ_ε_correlatedAgreementCurves (k := 1) (A := F) (F := F) (ι := Fin n)
      (C := ReedSolomon.code ωs (k + 1)) (δ := (δ : ℝ≥0))
      (ε := errorBound (δ : ℝ≥0) (k + 1) ωs) := by
  classical
  refine correlatedAgreement_affine_curves_of_strict_canonical_eval_polys_and_boundary_card
    (k := 1) (deg := k + 1) (domain := ωs) (δ := (δ : ℝ≥0)) hδ ?_ ?_
  · exact fun _hk u hprob hJ _hsqrt =>
      section5_strict_canonical_eval_polys_for_RS_goodCoeffsCurve_finMapTwoWords
        (F := F) (n := n) (m := m) (k := k) hk (ωs := ωs) δ hDx hYZ hsubset hunique
        _hk u hprob hJ
  · intro _hk u hδeq hcard
    have h_u_eq := wordStack_fin_two_eq_finMapTwoWords (F := F) (n := n) u
    have hcard_close :
        0 < (coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) (u 0) (u 1)).card := by
      rw [coeffs_of_close_proximity_card_eq_goodCoeffsCurve_finMapTwoWords
        (F := F) (n := n) (k := k) (ωs := ωs) δ (u 0) (u 1)]
      rw [h_u_eq] at hcard
      exact hcard
    rw [h_u_eq]
    exact hBoundaryCard (u 0) (u 1) hδeq hcard_close

/-- Strict square-root-radius degree-one correlated-agreement capstone in the
native §5 affine-line language. Unlike
`correlatedAgreement_affine_lines_of_strict_exists_PzFamily_and_boundary_card`,
this version needs no closed-boundary obligation because the global hypothesis
is already `δ < 1 - sqrtRate`. -/
theorem correlatedAgreement_affine_lines_of_strict_exists_PzFamily
    {m k : ℕ} (hk : 0 < k) {ωs : Fin n ↪ F}
    (δ : ℚ≥0)
    (hδ : (δ : ℝ≥0) < 1 - ReedSolomon.sqrtRate (k + 1) ωs)
    (hDx : ((gsDpg n m k : ℕ) : ℝ) < D_X ((k + 1) / (n : ℚ)) n m)
    (hYZ : ((gsDpg n m k + gsZCap n m k : ℕ) : ℝ) ≤
      n * (m + 1 / (2 : ℚ)) ^ 3 / (6 * Real.sqrt ((k + 1) / n)))
    (hsubset : ∀ (u₀ u₁ : Fin n → F) {Q : F[Z][X][Y]}
      (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁) (x : Fin n),
        coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) u₀ u₁ ⊆
          matching_set_at_x k (δ : ℚ) h_gs x)
    (hunique : ∀ (u₀ u₁ : Fin n → F) (P : F → Polynomial F),
        (∀ z ∈ coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) u₀ u₁,
          (P z).natDegree < k + 1 ∧ δᵣ(u₀ + z • u₁, (P z).eval ∘ ωs) ≤ (δ : ℚ)) →
        ∀ z ∈ coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) u₀ u₁,
          P z = PzFamily (F := F) (n := n) (δ : ℚ) u₀ u₁ ωs k z) :
    δ_ε_correlatedAgreementCurves (k := 1) (A := F) (F := F) (ι := Fin n)
      (C := ReedSolomon.code ωs (k + 1)) (δ := (δ : ℝ≥0))
      (ε := errorBound (δ : ℝ≥0) (k + 1) ωs) := by
  classical
  refine correlatedAgreement_affine_curves_of_strict_canonical_eval_polys
    (k := 1) (deg := k + 1) (domain := ωs) (δ := (δ : ℝ≥0)) hδ ?_
  exact section5_strict_canonical_eval_polys_for_RS_goodCoeffsCurve_finMapTwoWords
    (F := F) (n := n) (m := m) (k := k) hk (ωs := ωs) δ hDx hYZ hsubset hunique

end BCIKS20ProximityGapSection5To6Bridge

end ProximityGap
