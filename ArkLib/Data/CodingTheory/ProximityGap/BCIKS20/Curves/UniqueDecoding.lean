/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.Curves.JointAgreement
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.ErrorBound

/-!
# Correlated agreement for parameterized curves — unique-decoding regime

[BCIKS20] Theorem 6.1 (the unique-decoding case of Theorem 1.5): if a random
point on the degree-`k` parameterized curve through `u 0, …, u k` is `δ`-close
to the Reed–Solomon code with probability exceeding `k · (n/q)`, then the
words have correlated (joint) agreement. Curves analogue of
`AffineLines/UniqueDecoding.lean`; consumes the Curves GoodCoeffs +
JointAgreement chain. The list-decoding regime (Theorem 6.2) remains open
(§5 chain).
-/

namespace ProximityGap

open NNReal Finset Function ProbabilityTheory Code
open scoped BigOperators LinearCode

section CoreResults
variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
         {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **Correlated agreement for low-degree parameterized curves, unique-decoding
regime** ([BCIKS20] Theorem 6.1 / the UDR case of Theorem 1.5): curves analogue
of `RS_correlatedAgreement_affineLines_uniqueDecodingRegime`. -/
theorem RS_correlatedAgreement_curves_uniqueDecodingRegime {k deg : ℕ}
    {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg] (hk : 0 < k)
    (hδ : δ ≤ relativeUniqueDecodingRadius (ι := ι) (F := F)
      (C := ReedSolomon.code domain deg)) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) := by
  classical
  unfold δ_ε_correlatedAgreementCurves
  intro u hprob
  have hkε : (k : ℝ≥0) * errorBound δ deg domain
      = ((k * Fintype.card ι : ℕ) : ℝ≥0) / (Fintype.card F : ℝ≥0) := by
    rw [errorBound_eq_n_div_q_of_le_relUDR (deg := deg) (domain := domain) (δ := δ) hδ]
    push_cast
    ring
  have hprob' :
      Pr_{let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ]
        > ((k * Fintype.card ι : ℕ) : ℝ≥0) / (Fintype.card F : ℝ≥0) := by
    have hqne : ((Fintype.card F : ℝ≥0)) ≠ 0 := by
      simp [Fintype.card_ne_zero]
    calc ((((k * Fintype.card ι : ℕ) : ℝ≥0) : ENNReal) / (((Fintype.card F : ℝ≥0)) : ENNReal))
        = ((((k * Fintype.card ι : ℕ) : ℝ≥0) / (Fintype.card F : ℝ≥0) : ℝ≥0) : ENNReal) :=
          (ENNReal.coe_div hqne).symm
      _ = (((k : ℝ≥0) * errorBound δ deg domain : ℝ≥0) : ENNReal) := by rw [hkε]
      _ = (k : ENNReal) * (errorBound δ deg domain : ENNReal) := by
          rw [ENNReal.coe_mul, ENNReal.coe_natCast]
      _ < _ := by simpa using hprob
  have hS := card_RS_goodCoeffsCurve_gt_of_prob_gt_kn_div_q (k := k) (deg := deg)
    (domain := domain) (δ := δ) u (by exact_mod_cast hprob')
  exact RS_jointAgreement_of_goodCoeffsCurve_card_gt (k := k) (deg := deg)
    (domain := domain) (δ := δ) hk hδ u hS

/-- The `k = 0` corner of curves correlated agreement: a degree-0 "curve" is the
constant word `u 0`, so any positive probability of closeness gives the plain
closeness fact, and joint agreement follows from unique decoding. -/
theorem RS_correlatedAgreement_curves_k_zero {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    [NeZero deg]
    (hδ : δ ≤ relativeUniqueDecodingRadius (ι := ι) (F := F)
      (C := ReedSolomon.code domain deg)) :
    δ_ε_correlatedAgreementCurves (k := 0) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) := by
  classical
  unfold δ_ε_correlatedAgreementCurves
  intro u hprob
  -- the curve is constant: ∑ t : Fin 1, r^t • u t = u 0
  have hconst : ∀ r : F, (∑ t : Fin (0 + 1), (r ^ (t : ℕ)) • u t) = u 0 := by
    intro r
    simp
  -- positive probability ⇒ nonempty good set (bridge at k = 0) ⇒ the constant fact
  have hS := card_RS_goodCoeffsCurve_gt_of_prob_gt_kn_div_q (k := 0) (deg := deg)
    (domain := domain) (δ := δ) u (by simpa using hprob)
  have hclose : δᵣ(u 0, (ReedSolomon.code domain deg : Set (ι → F))) ≤ δ := by
    have hne : (RS_goodCoeffsCurve (k := 0) (deg := deg) (domain := domain) u δ).Nonempty := by
      rw [← Finset.card_pos]
      omega
    obtain ⟨z, hz⟩ := hne
    have hz' := hz
    simp only [RS_goodCoeffsCurve, hconst z, Finset.filter_const] at hz'
    by_contra hp
    simp [hp] at hz' 
  -- unique-decode and collect the agreement set
  set e : ℕ := Nat.floor (δ * Fintype.card ι) with he
  have hdist : Δ₀(u 0, (ReedSolomon.code domain deg : Set (ι → F))) ≤ (e : ℕ∞) := by
    have h := (Code.relDistFromCode_le_iff_distFromCode_le
        (u := u 0) (C := (ReedSolomon.code domain deg : Set (ι → F))) (δ := δ)).1 hclose
    simpa [e] using h
  rcases (Code.closeToCode_iff_closeToCodeword_of_minDist
        (u := u 0) (C := (ReedSolomon.code domain deg : Set (ι → F))) (e := e)).1 hdist with
    ⟨w, hwC, hwdist⟩
  obtain ⟨T, hT_card, hT_agree⟩ :=
    (Code.closeToWord_iff_exists_agreementCols (u := u 0) (v := w) (e := e)).1 hwdist
  refine ⟨T, ?_, fun _ => w, ?_⟩
  · have hnat : Fintype.card ι - e ≤ T.card := hT_card
    simpa [e] using
      (Code.relDist_floor_bound_iff_complement_bound (Fintype.card ι) T.card δ).mp
        (by simpa [e] using hnat)
  · intro t
    refine ⟨hwC, ?_⟩
    intro j hj
    have := (hT_agree j).1 hj
    have ht0 : t = 0 := Fin.fin_one_eq_zero t
    simp [ht0, Finset.mem_filter]
    exact this.symm


-- Placed here to avoid invalidating the ReedSolomon.lean olean cascade;
-- natural upstream home: ReedSolomon.lean next to relativeUniqueDecodingRadius_RS_eq'.
/-- The relative unique decoding radius of a Reed–Solomon code is strictly below
the Johnson-type bound `1 − √ρ` whenever it is positive: `(1−ρ)/2 < 1−√ρ` for
`ρ < 1`, by AM–GM (`2√ρ < 1 + ρ` strictly since `√ρ < 1`). Merges the
unique-decoding hypothesis into the [BCIKS20] full-range hypothesis. -/
lemma relativeUniqueDecodingRadius_lt_one_sub_sqrtRate
    {ι : Type*} [Fintype ι] {F : Type*} [Field F] [DecidableEq F]
    {deg : ℕ} {domain : ι ↪ F} [NeZero deg] (h : deg ≤ Fintype.card ι)
    (hpos : 0 < Code.relativeUniqueDecodingRadius (ι := ι) (F := F)
      (C := ReedSolomon.code domain deg)) :
    Code.relativeUniqueDecodingRadius (ι := ι) (F := F)
        (C := ReedSolomon.code domain deg)
      < 1 - ReedSolomon.sqrtRate deg domain := by
  classical
  have hn_pos : 0 < Fintype.card ι :=
    lt_of_lt_of_le (Nat.pos_of_neZero deg) h
  -- the rate is deg/n
  have hrate : (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)
      = (deg : ℝ≥0) / (Fintype.card ι : ℝ≥0) := by
    rw [ReedSolomon.rateOfLinearCode_eq_min_div, min_eq_left (by exact_mod_cast h)]
    push_cast
    ring
  set ρ : ℝ≥0 := (deg : ℝ≥0) / (Fintype.card ι : ℝ≥0) with hρ
  -- relUDR = (1 − ρ)/2
  have hudr : Code.relativeUniqueDecodingRadius (ι := ι) (F := F)
      (C := ReedSolomon.code domain deg) = (1 - ρ) / 2 := by
    rw [ReedSolomon.relativeUniqueDecodingRadius_RS_eq' (α := domain) (n := deg) h]
  -- positivity forces ρ < 1
  have hρ_lt_one : ρ < 1 := by
    by_contra hge
    push_neg at hge
    have : (1 : ℝ≥0) - ρ = 0 := tsub_eq_zero_of_le hge
    rw [hudr, this] at hpos
    simp at hpos
  -- pass to ℝ
  rw [hudr]
  rw [show ReedSolomon.sqrtRate deg domain = NNReal.sqrt ρ by
    simp only [ReedSolomon.sqrtRate, hrate]]
  rw [← NNReal.coe_lt_coe]
  have hsqrt_le_one : NNReal.sqrt ρ ≤ 1 := by
    rw [show (1 : ℝ≥0) = NNReal.sqrt 1 by simp]
    exact NNReal.sqrt_le_sqrt.mpr (le_of_lt hρ_lt_one)
  rw [NNReal.coe_sub hsqrt_le_one]
  rw [NNReal.coe_div, NNReal.coe_sub (le_of_lt hρ_lt_one)]
  have hρ_real : ((NNReal.sqrt ρ : ℝ≥0) : ℝ) = Real.sqrt (ρ : ℝ) := by
    rw [Real.coe_sqrt]
  rw [hρ_real]
  have hρ0 : (0 : ℝ) ≤ (ρ : ℝ) := (ρ : ℝ≥0).coe_nonneg
  have hρ1 : (ρ : ℝ) < 1 := by exact_mod_cast hρ_lt_one
  have hsq : Real.sqrt (ρ : ℝ) ^ 2 = (ρ : ℝ) := Real.sq_sqrt hρ0
  have hsqrt_lt_one : Real.sqrt (ρ : ℝ) < 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt hρ0 hρ1
  have hsub_pos : 0 < 1 - Real.sqrt (ρ : ℝ) := sub_pos.mpr hsqrt_lt_one
  push_cast
  nlinarith [pow_pos hsub_pos 2, hsq]

end CoreResults

end ProximityGap
