/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Katerina Hristova, František Silváši, Julian Sutherland,
         Ilia Vlasov, Chung Thai Nguyen
-/

import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.ErrorBound
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.Curves.UniqueDecoding
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.WeightedAgreement
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.ToMathlib.Polynomial.EvalExt

namespace ProximityGap

open NNReal Finset Function ProbabilityTheory
open scoped BigOperators LinearCode ProbabilityTheory ENNReal
open Code

section CoreResults

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

omit [Nonempty ι] [DecidableEq ι] in
lemma prob_close_curve_eq_card_goodCoeffsCurve_div_card {k deg : ℕ}
    {domain : ι ↪ F} {δ : ℝ≥0} (u : WordStack F (Fin (k + 1)) ι) :
    Pr_{let z ← $ᵖ F}[
        δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] =
      ((RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card : ℝ≥0) /
        (Fintype.card F : ℝ≥0) := by
  classical
  simpa [RS_goodCoeffsCurve] using
    (prob_uniform_eq_card_filter_div_card (F := F)
      (P := fun z : F =>
        δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ))

omit [Nonempty ι] [DecidableEq ι] in
lemma goodCoeffsCurve_threshold_mul_card_lt_card_of_prob_gt {k deg : ℕ}
    {domain : ι ↪ F} {δ η : ℝ≥0} (u : WordStack F (Fin (k + 1)) ι)
    (hprob :
      Pr_{let z ← $ᵖ F}[
          δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
            ReedSolomon.code domain deg) ≤ δ] > (η : ENNReal)) :
    (η : ENNReal) * (Fintype.card F : ENNReal) <
      ((RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card :
        ENNReal) := by
  classical
  have hPr := prob_close_curve_eq_card_goodCoeffsCurve_div_card
    (k := k) (deg := deg) (domain := domain) (δ := δ) u
  have hlt :
      (η : ENNReal) <
        (((RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card :
          ℝ≥0) / (Fintype.card F : ℝ≥0) : ENNReal) := by
    rw [← hPr]
    exact hprob
  have hq0 : (Fintype.card F : ℝ≥0) ≠ 0 := by
    simp [Fintype.card_ne_zero]
  have hlt' :
      (η : ENNReal) <
        ((RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card :
          ENNReal) / (Fintype.card F : ENNReal) := by
    simpa [ENNReal.coe_div hq0, ENNReal.coe_natCast] using hlt
  exact ENNReal.mul_lt_of_lt_div hlt'

omit [DecidableEq ι] in
/-- Theorem 1.5 (Correlated agreement for low-degree parameterised curves) in [BCIKS20].

Take a Reed-Solomon code of length `ι` and degree `deg`, a proximity-error parameter
pair `(δ, ε)` and a curve passing through words `u₀, ..., uκ`, such that
the probability that a random point on the curve is `δ`-close to the Reed-Solomon code
is at most `ε`. Then, the words `u₀, ..., uκ` have correlated agreement. -/
theorem correlatedAgreement_affine_curves {k : ℕ}
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    -- `deg = 0` makes the statement false: `errorBound`'s Johnson
    -- branch vacates the threshold at deg = 0; counterexample in upstream-issues.md).
    [NeZero deg]
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) := by
  classical
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0
    exact RS_correlatedAgreement_curves_k_zero (deg := deg) (domain := domain) (δ := δ)
  · by_cases hUDR : δ ≤ Code.relativeUniqueDecodingRadius (ι := ι) (F := F)
        (C := ReedSolomon.code domain deg)
    · -- Unique-decoding regime: PROVEN ([BCIKS20] Theorem 6.1, all curve degrees).
      exact RS_correlatedAgreement_curves_uniqueDecodingRegime hkpos hUDR
    · -- List-decoding regime: Theorem 6.2 ([BCIKS20] §6.2 / §5 chain).
      unfold δ_ε_correlatedAgreementCurves
      intro u hprob
      have hS_card :
          ((k : ℝ≥0∞) * (errorBound δ deg domain : ℝ≥0∞)) *
              (Fintype.card F : ℝ≥0∞) <
            ((RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card :
              ℝ≥0∞) := by
        simpa [ENNReal.coe_mul, ENNReal.coe_natCast] using
          goodCoeffsCurve_threshold_mul_card_lt_card_of_prob_gt
            (u := u) (η := (k : ℝ≥0) * errorBound δ deg domain) hprob
      sorry

omit [DecidableEq ι] [Fintype F] in
/-- Integral-weight list agreement on a sufficiently large set of curve parameters
gives correlated coordinate agreement for the input coefficient lists. This is
the curve-facing form of [BCIKS20] Lemma 7.6. -/
theorem weighted_list_agreement_on_curves_implies_correlated_agreement {l : ℕ}
    {u : Fin (l + 2) → ι → F}
    {μ : ι → Set.Icc (0 : ℚ) 1}
    {α : ℝ≥0}
    {M : ℕ}
    (hμ : ∀ i, ∃ n : ℤ, (μ i).1 = (n : ℚ) / (M : ℚ))
    {v : Fin (l + 2) → ι → F}
    {S' : Finset F}
    (hS'_card : S'.card > l + 1)
    (hS'_card₁ : S'.card ≥ (M * Fintype.card ι + 1) * (l + 1))
    (hS'_agree : ∀ z ∈ S',
      WeightedAgreement.agree μ
        (fun x => Curve.polynomialCurveEval (F := F) (A := F) u z x)
        (fun x => Curve.polynomialCurveEval (F := F) (A := F) v z x) ≥ α) :
    WeightedAgreement.mu_set μ { x : ι | ∀ i, u i x = v i x } ≥ α := by
  exact WeightedAgreement.sufficiently_large_list_agreement_on_curve_implies_correlated_agreement
    (u := u) (μ := μ) (α := α) (v := v)
    hμ hS'_card hS'_card₁ hS'_agree

omit [DecidableEq ι] [Fintype F] in
/-- The unit weight function used to view ordinary coordinate density as a
weighted agreement measure. -/
def uniformWeight : ι → Set.Icc (0 : ℚ) 1 := fun _ => ⟨1, by simp⟩

omit [Nonempty ι] [DecidableEq ι] [Fintype F] in
lemma mu_set_uniformWeight_eq_card_div (S : Finset ι) :
    WeightedAgreement.mu_set (uniformWeight (ι := ι)) S =
      (S.card : ℝ) / (Fintype.card ι : ℝ) := by
  unfold WeightedAgreement.mu_set uniformWeight
  rw [Finset.sum_const]
  simp [nsmul_eq_mul, div_eq_inv_mul]

omit [Nonempty ι] [DecidableEq ι] [Field F] [Fintype F] in
lemma agree_uniformWeight_eq_card_div (a b : ι → F) :
    WeightedAgreement.agree (uniformWeight (ι := ι)) a b =
      ((Finset.univ.filter (fun i => a i = b i)).card : ℝ) /
        (Fintype.card ι : ℝ) := by
  rw [WeightedAgreement.agree_eq_mu_set_filter]
  exact mu_set_uniformWeight_eq_card_div _

omit [DecidableEq ι] [Fintype F] in
lemma card_ge_of_uniform_mu_set_ge {S : Finset ι} {δ : ℝ≥0}
    (hS :
      WeightedAgreement.mu_set (uniformWeight (ι := ι)) S
        ≥ ((1 - δ : ℝ≥0) : ℝ)) :
    (S.card : ℝ≥0) ≥ (1 - δ) * (Fintype.card ι : ℝ≥0) := by
  have hn_pos_nat : 0 < Fintype.card ι := Fintype.card_pos
  have hn_pos : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast hn_pos_nat
  rw [mu_set_uniformWeight_eq_card_div] at hS
  have hS' : ((1 - δ : ℝ≥0) : ℝ) ≤
      (S.card : ℝ) / (Fintype.card ι : ℝ) := hS
  have hreal : ((1 - δ : ℝ≥0) : ℝ) * (Fintype.card ι : ℝ) ≤
      (S.card : ℝ) := by
    rw [le_div_iff₀ hn_pos] at hS'
    simpa [mul_comm] using hS'
  rw [ge_iff_le, ← NNReal.coe_le_coe]
  rw [NNReal.coe_mul]
  exact hreal

omit [DecidableEq ι] [Field F] [Fintype F] in
lemma agree_uniformWeight_ge_one_sub_of_relDist_le {a b : ι → F} {δ : ℝ≥0}
    (hδ : δᵣ(a, b) ≤ δ) :
    WeightedAgreement.agree (uniformWeight (ι := ι)) a b ≥ ((1 - δ : ℝ≥0) : ℝ) := by
  classical
  obtain ⟨S, hS_card, hS_agree⟩ :=
    (Code.relCloseToWord_iff_exists_agreementCols a b δ).1 hδ
  let A : Finset ι := Finset.univ.filter (fun i => a i = b i)
  have hS_subset : S ⊆ A := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, (hS_agree i).1 hi⟩
  have hA_card : (1 - δ) * (Fintype.card ι : ℝ≥0) ≤ (A.card : ℝ≥0) := by
    exact le_trans
      ((Code.relDist_floor_bound_iff_complement_bound (Fintype.card ι) S.card δ).mp hS_card)
      (by exact_mod_cast Finset.card_le_card hS_subset)
  rw [agree_uniformWeight_eq_card_div]
  have hn_pos_nat : 0 < Fintype.card ι := Fintype.card_pos
  have hn_pos : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast hn_pos_nat
  rw [ge_iff_le, le_div_iff₀ hn_pos]
  rw [← NNReal.coe_le_coe] at hA_card
  rwa [NNReal.coe_mul] at hA_card

omit [DecidableEq ι] [Fintype F] in
/-- Unweighted corollary of Lemma 7.6: if a sufficiently large set of curve
parameters has ordinary coordinate agreement at least `1 - δ` with codeword
curves, then the coefficient words have `jointAgreement`. This packages the
weighted list-agreement theorem into the consequent shape used by correlated
agreement for curves. -/
theorem uniform_list_agreement_on_curves_implies_jointAgreement {l : ℕ}
    {u : Fin (l + 2) → ι → F}
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {v : Fin (l + 2) → ι → F}
    (hv : ∀ i, v i ∈ ReedSolomon.code domain deg)
    {S' : Finset F}
    (hS'_card : S'.card > l + 1)
    (hS'_card₁ : S'.card ≥ (Fintype.card ι + 1) * (l + 1))
    (hS'_agree : ∀ z ∈ S',
      WeightedAgreement.agree (uniformWeight (ι := ι))
        (fun x => Curve.polynomialCurveEval (F := F) (A := F) u z x)
        (fun x => Curve.polynomialCurveEval (F := F) (A := F) v z x)
          ≥ (1 - δ : ℝ≥0)) :
    jointAgreement (C := ReedSolomon.code domain deg) (δ := δ) (W := u) := by
  classical
  let μ : ι → Set.Icc (0 : ℚ) 1 := uniformWeight (ι := ι)
  let S : Finset ι := { x : ι | ∀ i, u i x = v i x }
  have hμ : ∀ i, ∃ n : ℤ, (μ i).1 = (n : ℚ) / (1 : ℚ) := by
    intro i
    exact ⟨1, by simp [μ, uniformWeight]⟩
  have hweighted :
      WeightedAgreement.mu_set μ S ≥ ((1 - δ : ℝ≥0) : ℝ) := by
    simpa [μ, S] using
      weighted_list_agreement_on_curves_implies_correlated_agreement
        (u := u) (μ := μ) (α := 1 - δ) (M := 1)
        hμ hS'_card (by simpa using hS'_card₁) hS'_agree
  refine ⟨S, ?_, v, ?_⟩
  · exact card_ge_of_uniform_mu_set_ge hweighted
  · intro i
    refine ⟨hv i, ?_⟩
    intro x hx
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ x, (Finset.mem_filter.mp hx).2 i |>.symm⟩

omit [DecidableEq ι] [Fintype F] in
/-- If a sufficiently large set of curve parameters is pointwise close to a
codeword curve, then the coefficient words have `jointAgreement`. This is the
unweighted, curve-close form needed after the list-decoding step produces
nearby codewords for many curve parameters. -/
theorem close_codeword_curves_on_large_parameter_set_implies_jointAgreement {l : ℕ}
    {u : Fin (l + 2) → ι → F}
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {v : Fin (l + 2) → ι → F}
    (hv : ∀ i, v i ∈ ReedSolomon.code domain deg)
    {S' : Finset F}
    (hS'_card : S'.card > l + 1)
    (hS'_card₁ : S'.card ≥ (Fintype.card ι + 1) * (l + 1))
    (hclose : ∀ z ∈ S',
      δᵣ((fun x => Curve.polynomialCurveEval (F := F) (A := F) u z x),
        (fun x => Curve.polynomialCurveEval (F := F) (A := F) v z x)) ≤ δ) :
    jointAgreement (C := ReedSolomon.code domain deg) (δ := δ) (W := u) := by
  exact uniform_list_agreement_on_curves_implies_jointAgreement
    (u := u) (deg := deg) (domain := domain) (δ := δ) (v := v)
    hv hS'_card hS'_card₁
    (fun z hz => agree_uniformWeight_ge_one_sub_of_relDist_le (hclose z hz))

omit [DecidableEq ι] [Fintype F] in
/-- If the close codewords found at many curve parameters are evaluations of
one codeword curve, then the coefficient words have `jointAgreement`. This
isolates the exact remaining output needed from the list-decoding extraction:
the per-parameter decoded words must be assembled into a single polynomial
curve through Reed-Solomon codewords. -/
theorem decoded_polynomials_on_codeword_curve_implies_jointAgreement {l : ℕ}
    {u : Fin (l + 2) → ι → F}
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {v : Fin (l + 2) → ι → F}
    (hv : ∀ i, v i ∈ ReedSolomon.code domain deg)
    {S' : Finset F}
    (hS'_card : S'.card > l + 1)
    (hS'_card₁ : S'.card ≥ (Fintype.card ι + 1) * (l + 1))
    (P : F → Polynomial F)
    (hPcurve : ∀ z ∈ S',
      (fun x : ι => (P z).eval (domain x)) =
        (fun x => Curve.polynomialCurveEval (F := F) (A := F) v z x))
    (hclose : ∀ z ∈ S',
      δᵣ((fun x => Curve.polynomialCurveEval (F := F) (A := F) u z x),
        (fun x : ι => (P z).eval (domain x))) ≤ δ) :
    jointAgreement (C := ReedSolomon.code domain deg) (δ := δ) (W := u) := by
  exact close_codeword_curves_on_large_parameter_set_implies_jointAgreement
    (u := u) (deg := deg) (domain := domain) (δ := δ) (v := v)
    hv hS'_card hS'_card₁
    (fun z hz => by
      simpa [hPcurve z hz] using hclose z hz)

omit [DecidableEq ι] [Fintype F] in
/-- Same bridge as `decoded_polynomials_on_codeword_curve_implies_jointAgreement`,
with the decoded-polynomial hypotheses bundled in the natural selector form:
degree bounds plus relative closeness at each selected parameter. -/
theorem decoded_polynomial_family_on_codeword_curve_implies_jointAgreement {l : ℕ}
    {u : Fin (l + 2) → ι → F}
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {v : Fin (l + 2) → ι → F}
    (hv : ∀ i, v i ∈ ReedSolomon.code domain deg)
    {S' : Finset F}
    (hS'_card : S'.card > l + 1)
    (hS'_card₁ : S'.card ≥ (Fintype.card ι + 1) * (l + 1))
    (P : F → Polynomial F)
    (hdecoded : ∀ z ∈ S',
      (P z).natDegree < deg ∧
        δᵣ((fun x => Curve.polynomialCurveEval (F := F) (A := F) u z x),
          (fun x : ι => (P z).eval (domain x))) ≤ δ)
    (hPcurve : ∀ z ∈ S',
      (fun x : ι => (P z).eval (domain x)) =
        (fun x => Curve.polynomialCurveEval (F := F) (A := F) v z x)) :
    jointAgreement (C := ReedSolomon.code domain deg) (δ := δ) (W := u) := by
  exact decoded_polynomials_on_codeword_curve_implies_jointAgreement
    (u := u) (deg := deg) (domain := domain) (δ := δ) (v := v)
    hv hS'_card hS'_card₁ P hPcurve (fun z hz => (hdecoded z hz).2)

omit [Nonempty ι] [DecidableEq ι] [Fintype F] [DecidableEq F] in
/-- The two curve notations used in the Curves files agree pointwise. -/
lemma polynomialCurveEval_eq_sum_smul {k : ℕ} (u : Fin (k + 1) → ι → F) (z : F) :
    (fun x => Curve.polynomialCurveEval (F := F) (A := F) u z x) =
      ∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t := by
  funext x
  simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

omit [DecidableEq ι] [Fintype F] in
/-- GoodCoeffs-facing form of the decoded-family bridge: if decoded
per-parameter polynomials are close to the syntactic parameterized curve
`∑ t, z^t • u t` and assemble into one codeword curve, then the coefficient
words have `jointAgreement`. -/
theorem decoded_sum_polynomial_family_on_codeword_curve_implies_jointAgreement {l : ℕ}
    {u : Fin (l + 2) → ι → F}
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {v : Fin (l + 2) → ι → F}
    (hv : ∀ i, v i ∈ ReedSolomon.code domain deg)
    {S' : Finset F}
    (hS'_card : S'.card > l + 1)
    (hS'_card₁ : S'.card ≥ (Fintype.card ι + 1) * (l + 1))
    (P : F → Polynomial F)
    (hdecoded : ∀ z ∈ S',
      (P z).natDegree < deg ∧
        δᵣ(∑ t : Fin (l + 2), (z ^ (t : ℕ)) • u t,
          (P z).eval ∘ domain) ≤ δ)
    (hPcurve : ∀ z ∈ S',
      (fun x : ι => (P z).eval (domain x)) =
        (fun x => Curve.polynomialCurveEval (F := F) (A := F) v z x)) :
    jointAgreement (C := ReedSolomon.code domain deg) (δ := δ) (W := u) := by
  exact decoded_polynomial_family_on_codeword_curve_implies_jointAgreement
    (u := u) (deg := deg) (domain := domain) (δ := δ) (v := v)
    hv hS'_card hS'_card₁ P
    (fun z hz => by
      refine ⟨(hdecoded z hz).1, ?_⟩
      have hcurve :
          (fun x => Curve.polynomialCurveEval (F := F) (A := F) u z x) =
            ∑ t : Fin (l + 2), (z ^ (t : ℕ)) • u t :=
        polynomialCurveEval_eq_sum_smul (u := u) z
      have hP :
          (fun x : ι => (P z).eval (domain x)) = (P z).eval ∘ domain := rfl
      rw [hcurve, hP]
      exact (hdecoded z hz).2)
    hPcurve

omit [DecidableEq ι] in
/-- Relative-distance form of the per-parameter decoding witness for
`RS_goodCoeffsCurve`. The GoodCoeffs file constructs a polynomial within
`floor(δ * n)` Hamming distance; this packages the same witness as
`δᵣ ≤ δ`, which is the form consumed by the list-decoding curve bridges. -/
theorem exists_rel_close_polynomial_of_mem_goodCoeffsCurve {k deg : ℕ}
    {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (u : WordStack F (Fin (k + 1)) ι) {z : F}
    (hz : z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ) :
    ∃ Pz : Polynomial F, Pz.natDegree < deg ∧
      δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
        Pz.eval ∘ domain) ≤ δ := by
  obtain ⟨Pz, hdeg, hdist⟩ :=
    RS_exists_Pz_of_mem_goodCoeffsCurve (k := k) (deg := deg)
      (domain := domain) (δ := δ) u hz
  exact ⟨Pz, hdeg, (Code.pairRelDist_le_iff_pairDist_le
    (u := ∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t)
    (v := Pz.eval ∘ domain) (δ := δ)).2 hdist⟩

omit [DecidableEq ι] in
/-- Choose decoded polynomials uniformly over a finite set of good curve
parameters. The resulting selector is unconstrained away from `S'`; on `S'`
it has degree `< deg` and is relatively `δ`-close to the input curve point. -/
theorem exists_decoded_polynomial_family_of_subset_goodCoeffsCurve {k deg : ℕ}
    {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (u : WordStack F (Fin (k + 1)) ι) {S' : Finset F}
    (hS' : ∀ z ∈ S', z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ) :
    ∃ P : F → Polynomial F, ∀ z ∈ S',
      (P z).natDegree < deg ∧
        δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
          (P z).eval ∘ domain) ≤ δ := by
  classical
  let P : F → Polynomial F := fun z =>
    if hz : z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ then
      Classical.choose
        (exists_rel_close_polynomial_of_mem_goodCoeffsCurve
          (k := k) (deg := deg) (domain := domain) (δ := δ) u hz)
    else 0
  refine ⟨P, ?_⟩
  intro z hzS'
  have hzgood := hS' z hzS'
  have hspec :=
    Classical.choose_spec
      (exists_rel_close_polynomial_of_mem_goodCoeffsCurve
        (k := k) (deg := deg) (domain := domain) (δ := δ) u hzgood)
  simpa [P, hzgood] using hspec

omit [Fintype ι] [Nonempty ι] [DecidableEq ι] [Fintype F] [DecidableEq F] in
/-- Assemble a decoded polynomial family into a Reed-Solomon codeword curve once the
decoded family is known to be polynomial in the curve parameter with coefficient
polynomials of degree `< deg`.

This is the algebraic assembly step consumed by the list-decoding branch: from
`P z = ∑ i, z^i A_i` it constructs the codeword stack
`v i x = A_i(domain x)`. -/
theorem decoded_family_coefficients_assemble_codeword_curve {l deg : ℕ}
    {domain : ι ↪ F}
    [NeZero deg]
    (P : F → Polynomial F)
    (A : Fin (l + 2) → Polynomial F)
    (hAdeg : ∀ i, (A i).natDegree < deg)
    {S' : Finset F}
    (hPcoeff : ∀ z ∈ S',
      P z = ∑ i : Fin (l + 2), Polynomial.C (z ^ (i : ℕ)) * A i) :
    ∃ v : Fin (l + 2) → ι → F,
      (∀ i, v i ∈ ReedSolomon.code domain deg) ∧
      ∀ z ∈ S',
        (fun x : ι => (P z).eval (domain x)) =
          (fun x => Curve.polynomialCurveEval (F := F) (A := F) v z x) := by
  classical
  let v : Fin (l + 2) → ι → F := fun i x => (A i).eval (domain x)
  refine ⟨v, ?_, ?_⟩
  · intro i
    rw [ReedSolomon.mem_code_iff_exists_polynomial_of_ne_zero]
    refine ⟨A i, hAdeg i, ?_⟩
    rfl
  · intro z hz
    funext x
    rw [hPcoeff z hz]
    simp [v, Curve.polynomialCurveEval, Polynomial.eval_finset_sum,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

omit [Nonempty ι] [DecidableEq ι] [Fintype F] in
/-- Named form of the list-decoding assembly output expected by
`subset_goodCoeffsCurve_assembled_implies_jointAgreement`.

If §5 supplies coefficient polynomials `A_i` with
`P z = ∑ i, z^i A_i` on the selected set, this theorem produces the exact
`hassemble` hypothesis consumed by the curve GoodCoeffs bridge. -/
theorem decoded_family_coefficients_has_assembly {l deg : ℕ}
    {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    {u : Fin (l + 2) → ι → F}
    {S' : Finset F}
    (A : Fin (l + 2) → Polynomial F)
    (hAdeg : ∀ i, (A i).natDegree < deg)
    (hcoeff : ∀ P : F → Polynomial F,
      (∀ z ∈ S',
        (P z).natDegree < deg ∧
          δᵣ(∑ t : Fin (l + 2), (z ^ (t : ℕ)) • u t,
            (P z).eval ∘ domain) ≤ δ) →
        ∀ z ∈ S',
          P z = ∑ i : Fin (l + 2), Polynomial.C (z ^ (i : ℕ)) * A i) :
    ∀ P : F → Polynomial F,
      (∀ z ∈ S',
        (P z).natDegree < deg ∧
          δᵣ(∑ t : Fin (l + 2), (z ^ (t : ℕ)) • u t,
            (P z).eval ∘ domain) ≤ δ) →
        ∃ v : Fin (l + 2) → ι → F,
          (∀ i, v i ∈ ReedSolomon.code domain deg) ∧
          ∀ z ∈ S',
            (fun x : ι => (P z).eval (domain x)) =
              (fun x => Curve.polynomialCurveEval (F := F) (A := F) v z x) := by
  intro P hdecoded
  exact decoded_family_coefficients_assemble_codeword_curve
    (deg := deg) (domain := domain) P A hAdeg (hcoeff P hdecoded)

omit [DecidableEq ι] in
/-- GoodCoeffs-to-joint-agreement bridge with the remaining list-decoding output
as one explicit assembly hypothesis. If a large selected set of good curve
parameters admits decoded polynomials that assemble into one curve through
Reed-Solomon codewords, then the coefficient words have `jointAgreement`. -/
theorem subset_goodCoeffsCurve_assembled_implies_jointAgreement {l deg : ℕ}
    {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    {u : Fin (l + 2) → ι → F}
    {S' : Finset F}
    (hS'_card : S'.card > l + 1)
    (hS'_card₁ : S'.card ≥ (Fintype.card ι + 1) * (l + 1))
    (hS' : ∀ z ∈ S',
      z ∈ RS_goodCoeffsCurve (k := l + 1) (deg := deg) (domain := domain) u δ)
    (hassemble : ∀ P : F → Polynomial F,
      (∀ z ∈ S',
        (P z).natDegree < deg ∧
          δᵣ(∑ t : Fin (l + 2), (z ^ (t : ℕ)) • u t,
            (P z).eval ∘ domain) ≤ δ) →
        ∃ v : Fin (l + 2) → ι → F,
          (∀ i, v i ∈ ReedSolomon.code domain deg) ∧
          ∀ z ∈ S',
            (fun x : ι => (P z).eval (domain x)) =
              (fun x => Curve.polynomialCurveEval (F := F) (A := F) v z x)) :
    jointAgreement (C := ReedSolomon.code domain deg) (δ := δ) (W := u) := by
  classical
  obtain ⟨P, hdecoded⟩ :=
    exists_decoded_polynomial_family_of_subset_goodCoeffsCurve
      (k := l + 1) (deg := deg) (domain := domain) (δ := δ) u hS'
  obtain ⟨v, hv, hPcurve⟩ := hassemble P hdecoded
  exact decoded_sum_polynomial_family_on_codeword_curve_implies_jointAgreement
    (u := u) (deg := deg) (domain := domain) (δ := δ) (v := v)
    hv hS'_card hS'_card₁ P hdecoded hPcurve

omit [DecidableEq ι] in
/-- GoodCoeffs-to-joint-agreement bridge where the list-decoding output is
provided as coefficient polynomials. This removes the existential assembly
hypothesis from `subset_goodCoeffsCurve_assembled_implies_jointAgreement` in the
standard case where §5 produces `P(z, X) = ∑ z^i A_i(X)`. -/
theorem subset_goodCoeffsCurve_coefficient_assembly_implies_jointAgreement {l deg : ℕ}
    {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    {u : Fin (l + 2) → ι → F}
    {S' : Finset F}
    (hS'_card : S'.card > l + 1)
    (hS'_card₁ : S'.card ≥ (Fintype.card ι + 1) * (l + 1))
    (hS' : ∀ z ∈ S',
      z ∈ RS_goodCoeffsCurve (k := l + 1) (deg := deg) (domain := domain) u δ)
    (A : Fin (l + 2) → Polynomial F)
    (hAdeg : ∀ i, (A i).natDegree < deg)
    (hcoeff : ∀ P : F → Polynomial F,
      (∀ z ∈ S',
        (P z).natDegree < deg ∧
          δᵣ(∑ t : Fin (l + 2), (z ^ (t : ℕ)) • u t,
            (P z).eval ∘ domain) ≤ δ) →
        ∀ z ∈ S',
          P z = ∑ i : Fin (l + 2), Polynomial.C (z ^ (i : ℕ)) * A i) :
    jointAgreement (C := ReedSolomon.code domain deg) (δ := δ) (W := u) := by
  classical
  exact subset_goodCoeffsCurve_assembled_implies_jointAgreement
    (deg := deg) (domain := domain) (δ := δ) (u := u)
    hS'_card hS'_card₁ hS'
    (decoded_family_coefficients_has_assembly
      (deg := deg) (domain := domain) (δ := δ) (u := u) A hAdeg hcoeff)

end CoreResults

section BCIKS20ProximityGapSection6

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- The parameters for which the curve points are `δ`-close to a set `V`
(typically, a linear code). This is the set `S` from the proximity gap paper. -/
noncomputable def coeffs_of_close_proximity_curve {l : ℕ}
    (δ : ℚ≥0) (u : Fin l → Fin n → F) (V : Finset (Fin n → F)) : Finset F :=
  have : Fintype { z | δᵣ(Curve.polynomialCurveEval (F := F) (A := F) u z, V) ≤ δ } := by
    infer_instance
  @Set.toFinset _ { z | δᵣ(Curve.polynomialCurveEval (F := F) (A := F) u z, V) ≤ δ } this

omit [DecidableEq F] in
/-- Propagation brick for the §6.1 argument: two polynomial curves of degree `< l`
that agree in coordinate `x` on at least `l` parameter values agree in that
coordinate everywhere. -/
private lemma polynomialCurveEval_coord_eq_of_agree {n l : ℕ} {F : Type} [Field F]
    {u v : Fin l → Fin n → F} {x : Fin n}
    {Zs : Finset F} (hZ : l ≤ Zs.card)
    (h : ∀ z ∈ Zs, Curve.polynomialCurveEval (F := F) (A := F) u z x
      = Curve.polynomialCurveEval (F := F) (A := F) v z x) :
    ∀ z : F, Curve.polynomialCurveEval (F := F) (A := F) u z x
      = Curve.polynomialCurveEval (F := F) (A := F) v z x := by
  -- coordinate-wise polynomial packaging
  have hEval : ∀ (a : Fin l → Fin n → F) (w : F),
      (∑ i : Fin l, Polynomial.C (a i x) * Polynomial.X ^ (i : ℕ)).eval w
        = Curve.polynomialCurveEval (F := F) (A := F) a w x := by
    intro a w
    rw [Polynomial.eval_finset_sum]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
      Curve.polynomialCurveEval, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hdeg : ∀ (a : Fin l → Fin n → F),
      (∑ i : Fin l, Polynomial.C (a i x) * Polynomial.X ^ (i : ℕ)).degree
        < ((l : ℕ) : WithBot ℕ) := by
    intro a
    apply lt_of_le_of_lt (Polynomial.degree_sum_le _ _)
    rw [Finset.sup_lt_iff (by exact_mod_cast WithBot.bot_lt_coe l)]
    intro i _
    exact lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le _ _) (by exact_mod_cast i.isLt)
  have hPQ := Polynomial.eq_of_eval_eq_degree (n := l) (hdeg u) (hdeg v) Zs hZ
    (fun w hw => by rw [hEval u, hEval v]; exact h w hw)
  intro z
  calc Curve.polynomialCurveEval (F := F) (A := F) u z x
      = (∑ i : Fin l, Polynomial.C (u i x) * Polynomial.X ^ (i : ℕ)).eval z := (hEval u z).symm
    _ = (∑ i : Fin l, Polynomial.C (v i x) * Polynomial.X ^ (i : ℕ)).eval z := by rw [hPQ]
    _ = Curve.polynomialCurveEval (F := F) (A := F) v z x := hEval v z

/-- Counting brick for the §6.1 argument (generic double counting): if every
`z ∈ S` has a bad-set of size at most `m`, then the number of coordinates that
are bad for at least `t` elements of `S` is bounded: `t · #poor ≤ m · #S`. -/
private lemma card_heavyCoords_mul_le {α β : Type} [Fintype α] [DecidableEq α]
    {S : Finset β} {B : β → Finset α} {m : ℕ}
    (hB : ∀ z ∈ S, (B z).card ≤ m) (t : ℕ) :
    ((Finset.univ : Finset α).filter
      (fun x => t ≤ (S.filter (fun z => x ∈ B z)).card)).card * t
      ≤ m * S.card := by
  classical
  -- double counting: Σ_x #{z ∈ S : x ∈ B z} = Σ_{z ∈ S} #(B z)
  have hswap : ∑ x : α, (S.filter (fun z => x ∈ B z)).card
      = ∑ z ∈ S, (B z).card := by
    have h1 : ∀ x : α, (S.filter (fun z => x ∈ B z)).card
        = ∑ z ∈ S, if x ∈ B z then 1 else 0 := fun x => Finset.card_filter _ _
    have h2 : ∀ z : β, (B z).card = ∑ x : α, if x ∈ B z then 1 else 0 := by
      intro z
      rw [← Finset.card_filter, Finset.filter_univ_mem]
    simp only [h1, h2]
    exact Finset.sum_comm
  have hbound : ∑ z ∈ S, (B z).card ≤ m * S.card := by
    calc ∑ z ∈ S, (B z).card ≤ ∑ _z ∈ S, m := Finset.sum_le_sum hB
      _ = m * S.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have hfilter : ((Finset.univ : Finset α).filter
      (fun x => t ≤ (S.filter (fun z => x ∈ B z)).card)).card * t
      ≤ ∑ x : α, (S.filter (fun z => x ∈ B z)).card := by
    calc ((Finset.univ : Finset α).filter
        (fun x => t ≤ (S.filter (fun z => x ∈ B z)).card)).card * t
        = ∑ _x ∈ (Finset.univ : Finset α).filter
            (fun x => t ≤ (S.filter (fun z => x ∈ B z)).card), t := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ x ∈ (Finset.univ : Finset α).filter
            (fun x => t ≤ (S.filter (fun z => x ∈ B z)).card),
            (S.filter (fun z => x ∈ B z)).card :=
          Finset.sum_le_sum fun x hx => (Finset.mem_filter.mp hx).2
      _ ≤ ∑ x : α, (S.filter (fun z => x ∈ B z)).card :=
          Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  exact le_trans hfilter (hswap ▸ hbound)

omit [DecidableEq F] in
/-- Interpolation brick for the §6.1 argument: through any `l` distinct parameter
values and arbitrary target vectors there is a polynomial curve of degree `< l`. -/
private lemma exists_polynomialCurve_through {n l : ℕ} {F : Type} [Field F]
    (zs : Fin l → F) (hinj : Function.Injective zs)
    (w : Fin l → Fin n → F) :
    ∃ v : Fin l → Fin n → F,
      ∀ j, Curve.polynomialCurveEval (F := F) (A := F) v (zs j) = w j := by
  -- per-coordinate Lagrange interpolant
  classical
  set P : Fin n → Polynomial F :=
    fun x => Lagrange.interpolate Finset.univ zs (fun j => w j x) with hP
  have hdeg : ∀ x, (P x).degree < (l : WithBot ℕ) := by
    intro x
    simpa using Lagrange.degree_interpolate_lt (s := (Finset.univ : Finset (Fin l)))
      (v := zs) (r := fun j => w j x) (fun a _ b _ hab => hinj hab)
  refine ⟨fun i x => (P x).coeff i, ?_⟩
  intro j
  funext x
  have hnat : (P x).natDegree < l := by
    rcases eq_or_ne (P x) 0 with h0 | h0
    · simpa [h0] using j.pos
    · exact (Polynomial.natDegree_lt_iff_degree_lt h0).mpr (by exact_mod_cast hdeg x)
  have heval : (P x).eval (zs j) = w j x :=
    Lagrange.eval_interpolate_at_node (s := (Finset.univ : Finset (Fin l)))
      (v := zs) (r := fun j => w j x) (fun a _ b _ hab => hinj hab) (Finset.mem_univ j)
  calc Curve.polynomialCurveEval (F := F) (A := F) (fun i x => (P x).coeff i) (zs j) x
      = ∑ i : Fin l, (zs j) ^ (i : ℕ) * (P x).coeff i := by
        simp [Curve.polynomialCurveEval, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    _ = ∑ i ∈ Finset.range l, (P x).coeff i * (zs j) ^ i := by
        rw [← Fin.sum_univ_eq_sum_range (fun i => (P x).coeff i * (zs j) ^ i)]
        exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    _ = (P x).eval (zs j) := (Polynomial.eval_eq_sum_range' hnat _).symm
    _ = w j x := heval

/-- Unique decoding brick for the §6.1 argument: two codewords of a code with
minimum distance `d` that are both within distance summing below `d` of a common
word are equal (triangle inequality). -/
private lemma eq_of_both_close_lt_minDist {n : ℕ} {F : Type} [DecidableEq F]
    {V : Finset (Fin n → F)} {d : ℕ}
    (hV : ∀ w ∈ V, ∀ w' ∈ V, w ≠ w' → d ≤ Δ₀(w, w'))
    {w₁ w₂ f : Fin n → F} (h₁ : w₁ ∈ V) (h₂ : w₂ ∈ V)
    (hsum : Δ₀(w₁, f) + Δ₀(f, w₂) < d) :
    w₁ = w₂ := by
  by_contra hne
  have htri : Δ₀(w₁, w₂) ≤ Δ₀(w₁, f) + Δ₀(f, w₂) := hammingDist_triangle w₁ f w₂
  exact absurd (le_trans (hV w₁ h₁ w₂ h₂ hne) htri) (not_le.mpr hsum)

end BCIKS20ProximityGapSection6

end ProximityGap
