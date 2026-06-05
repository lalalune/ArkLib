/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Katerina Hristova, Frantisek Silvasi, Julian Sutherland,
         Ilia Vlasov, Chung Thai Nguyen
-/

import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.Curves
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.ListDecoding.Agreement
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.ListDecoding.Guruswami

namespace ProximityGap

open NNReal Finset Function ProbabilityTheory
open scoped BigOperators LinearCode ProbabilityTheory ENNReal
open Code

section BCIKS20ProximityGapSection5To6Bridge

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

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

end BCIKS20ProximityGapSection5To6Bridge

end ProximityGap
