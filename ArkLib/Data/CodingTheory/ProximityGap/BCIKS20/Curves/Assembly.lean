/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.Curves

namespace ProximityGap

open Polynomial
open scoped BigOperators LinearCode
open Code
open NNReal

section CoreResults

variable {F : Type} [Field F]

private lemma coeff_zero_of_natDegree_lt {p : Polynomial F} {d j : ℕ}
    (hp : p.natDegree < d) (hj : d ≤ j) :
    p.coeff j = 0 := by
  by_cases hp0 : p = 0
  · simp [hp0]
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le hp hj)

/-- Coefficientwise low-degree dependence on `z` assembles a decoded family as
`P z = ∑ i, z^i A_i`. -/
theorem decoded_family_coefficients_of_coeff_polys {l deg : ℕ} [NeZero deg]
    {S' : Finset F} {P : F → Polynomial F}
    (B : ℕ → Polynomial F)
    (hBdeg : ∀ j < deg, (B j).natDegree < l + 2)
    (hPdeg : ∀ z ∈ S', (P z).natDegree < deg)
    (hcoeff : ∀ z ∈ S', ∀ j < deg, (P z).coeff j = (B j).eval z) :
    ∃ A : Fin (l + 2) → Polynomial F,
      (∀ i, (A i).natDegree < deg) ∧
        ∀ z ∈ S',
          P z = ∑ i : Fin (l + 2), Polynomial.C (z ^ (i : ℕ)) * A i := by
  classical
  let A : Fin (l + 2) → Polynomial F := fun i =>
    ∑ j ∈ Finset.range deg, Polynomial.C ((B j).coeff (i : ℕ)) * Polynomial.X ^ j
  have hAdeg : ∀ i, (A i).natDegree < deg := by
    intro i
    have hdegpos : 0 < deg := Nat.pos_of_neZero deg
    refine lt_of_le_of_lt ?_ (Nat.pred_lt (Nat.ne_of_gt hdegpos))
    refine Polynomial.natDegree_sum_le_of_forall_le
      (s := Finset.range deg)
      (f := fun j => Polynomial.C ((B j).coeff (i : ℕ)) * Polynomial.X ^ j)
      (n := deg - 1) ?_
    intro j hj
    exact (Polynomial.natDegree_C_mul_X_pow_le ((B j).coeff (i : ℕ)) j).trans
      (Nat.le_pred_of_lt (Finset.mem_range.mp hj))
  refine ⟨A, hAdeg, ?_⟩
  intro z hz
  ext j
  by_cases hj : j < deg
  · rw [hcoeff z hz j hj]
    have hBsum : (B j).eval z =
        ∑ i : Fin (l + 2), (B j).coeff (i : ℕ) * z ^ (i : ℕ) := by
      have hnat := hBdeg j hj
      rw [Polynomial.eval_eq_sum_range' hnat]
      rw [← Fin.sum_univ_eq_sum_range (fun i => (B j).coeff i * z ^ i)]
    rw [hBsum, Polynomial.finset_sum_coeff]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [Polynomial.coeff_C_mul]
    have hcoeffX : (A i).coeff j = (B j).coeff (i : ℕ) := by
      change (∑ x ∈ Finset.range deg,
        Polynomial.C ((B x).coeff (i : ℕ)) * Polynomial.X ^ x).coeff j =
          (B j).coeff (i : ℕ)
      rw [Polynomial.finset_sum_coeff]
      calc
        (∑ x ∈ Finset.range deg,
            (Polynomial.C ((B x).coeff (i : ℕ)) * Polynomial.X ^ x).coeff j)
            = (Polynomial.C ((B j).coeff (i : ℕ)) * Polynomial.X ^ j).coeff j := by
                exact Finset.sum_eq_single_of_mem
                  (s := Finset.range deg)
                  (f := fun x =>
                    (Polynomial.C ((B x).coeff (i : ℕ)) * Polynomial.X ^ x).coeff j)
                  j (Finset.mem_range.mpr hj)
                  (by
                    intro b hb hbj
                    have hjb : j ≠ b := fun h => hbj h.symm
                    change (Polynomial.C ((B b).coeff (i : ℕ)) * Polynomial.X ^ b).coeff j = 0
                    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
                    simp [hjb])
        _ = (B j).coeff (i : ℕ) := by
          simp [Polynomial.coeff_C_mul]
    simp [hcoeffX, mul_comm]
  · have hjge : deg ≤ j := Nat.le_of_not_gt hj
    have hPj : (P z).coeff j = 0 := coeff_zero_of_natDegree_lt (hPdeg z hz) hjge
    rw [hPj, Polynomial.finset_sum_coeff]
    symm
    refine Finset.sum_eq_zero ?_
    intro i _
    have hAj : (A i).coeff j = 0 := coeff_zero_of_natDegree_lt (hAdeg i) hjge
    rw [Polynomial.coeff_C_mul, hAj, mul_zero]

end CoreResults

section CurveAssemblyBridge

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

omit [Nonempty ι] [DecidableEq ι] [Field F] [Fintype F] in
/-- `jointAgreement` is invariant under reindexing the coefficient words by an
equivalence. This packages the casts needed when a curve helper is stated with
an index type definitionally different from the caller's `Fin (k + 1)`. -/
theorem jointAgreement_reindex_equiv {κ κ' : Type}
    {C : Set (ι → F)} {δ : ℝ≥0}
    {W : κ → ι → F} {W' : κ' → ι → F}
    (e : κ ≃ κ')
    (hW : ∀ i x, W' (e i) x = W i x)
    (h : jointAgreement (C := C) (δ := δ) (W := W')) :
    jointAgreement (C := C) (δ := δ) (W := W) := by
  classical
  obtain ⟨S, hS_card, v', hv'⟩ := h
  refine ⟨S, hS_card, fun i => v' (e i), ?_⟩
  intro i
  constructor
  · exact (hv' (e i)).1
  · intro x hx
    have hx' := (hv' (e i)).2 hx
    rw [Finset.mem_filter] at hx' ⊢
    exact ⟨hx'.1, by simpa [hW i x] using hx'.2⟩

omit [DecidableEq ι] in
/-- GoodCoeffs-to-joint-agreement bridge where the remaining list-decoding
output is coefficientwise low-degree dependence on the curve parameter.

For every decoded selector `P`, if each coefficient `(P z).coeff j` agrees on
`S'` with a polynomial in `z` of degree `< l + 2`, then the decoded selector
assembles into a Reed-Solomon codeword curve and the original coefficient words
have joint agreement. This is the curve-facing consumer for the §5 extraction
output. -/
theorem subset_goodCoeffsCurve_coeff_polys_implies_jointAgreement {l deg : ℕ}
    {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    {u : Fin (l + 2) → ι → F}
    {S' : Finset F}
    (hS'_card : S'.card > l + 1)
    (hS'_card₁ : S'.card ≥ (Fintype.card ι + 1) * (l + 1))
    (hS' : ∀ z ∈ S',
      z ∈ RS_goodCoeffsCurve (k := l + 1) (deg := deg) (domain := domain) u δ)
    (hcoeffPoly : ∀ P : F → Polynomial F,
      (∀ z ∈ S',
        (P z).natDegree < deg ∧
          δᵣ(∑ t : Fin (l + 2), (z ^ (t : ℕ)) • u t,
            (P z).eval ∘ domain) ≤ δ) →
        ∃ B : ℕ → Polynomial F,
          (∀ j < deg, (B j).natDegree < l + 2) ∧
            ∀ z ∈ S', ∀ j < deg, (P z).coeff j = (B j).eval z) :
    Code.jointAgreement (F := F) (κ := Fin (l + 2)) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (W := u) := by
  classical
  refine subset_goodCoeffsCurve_assembled_implies_jointAgreement
    (deg := deg) (domain := domain) (δ := δ) (u := u)
    hS'_card hS'_card₁ hS' ?_
  intro P hdecoded
  obtain ⟨B, hBdeg, hcoeff⟩ := hcoeffPoly P hdecoded
  obtain ⟨A, hAdeg, hPcoeff⟩ :=
    decoded_family_coefficients_of_coeff_polys
      (l := l) (deg := deg) (S' := S') (P := P) B
      hBdeg (fun z hz => (hdecoded z hz).1) hcoeff
  exact decoded_family_coefficients_assemble_codeword_curve
    (deg := deg) (domain := domain) P A hAdeg hPcoeff

end CurveAssemblyBridge

end ProximityGap
