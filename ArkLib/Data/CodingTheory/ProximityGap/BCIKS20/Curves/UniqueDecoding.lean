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
JointAgreement chain. The list-decoding regime (Theorem 6.2) is handled by
the separate §5 chain.
-/

namespace ProximityGap

-- Decidability/Fintype instances are threaded through the section; the
-- statement-level theorem does not mention them directly.
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false

open NNReal Finset Function ProbabilityTheory Code
open scoped BigOperators LinearCode

section CoreResults
variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
         {F : Type} [Field F] [Fintype F] [DecidableEq F]

omit [DecidableEq ι] in
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

omit [DecidableEq ι] in
/-- The `k = 0` corner of curves correlated agreement, **unconditional in the regime**:
a degree-0 "curve" is the uniform word `u 0`, so any positive probability of closeness
gives the plain closeness fact, and a *closest* codeword (not necessarily unique) furnishes
the agreement set. Note this argument never uses the unique-decoding radius bound — it goes
through `closeToCode_iff_closeToCodeword_of_minDist`, which holds for any code — so the
statement is valid for every `δ`, including the list-decoding regime `δ > relUDR`. The
list-decoding regime is reachable at `k = 0` from `correlatedAgreement_affine_curves`
(`Curves.lean`), where no UDR hypothesis is in scope. -/
theorem RS_correlatedAgreement_curves_k_zero_unconditional
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg] :
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
    simp only [RS_goodCoeffsCurve] at hz'
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
    subst ht0; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact this.symm

omit [DecidableEq ι] in
/-- The `k = 0` corner of curves correlated agreement: a degree-0 "curve" is the
uniform word `u 0`, so any positive probability of closeness gives the plain
closeness fact, and joint agreement follows from unique decoding. The
unique-decoding-radius hypothesis `_hδ` is retained in the signature to match the
keystone call shape used by `Stir/Combine.lean` and `proximity_gap_uniqueDecodingRegime`
(repair #17-class), but the proof delegates to the regime-unconditional version since the
`k = 0` argument never consumes it. -/
theorem RS_correlatedAgreement_curves_k_zero {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    [NeZero deg]
    (_hδ : δ ≤ relativeUniqueDecodingRadius (ι := ι) (F := F)
      (C := ReedSolomon.code domain deg)) :
    δ_ε_correlatedAgreementCurves (k := 0) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) :=
  RS_correlatedAgreement_curves_k_zero_unconditional

/-- **Formal BCIKS20 Theorem 1.2, unique-decoding regime, witness-extraction form**
— the machine-verified UDR rung of the proximity-prize ladder (cf. research dossier).

This is the witness-extraction specialization of the proximity gap, pinned to the
monomial / power generator `r ↦ (i ↦ rⁱ)` (curve `∑ᵢ rⁱ • fᵢ`), in the unique-decoding
regime `δ ≤ relativeUniqueDecodingRadius`. If a random point on the degree-`k` curve
through `f₀, …, f_k` is `δ`-close to the Reed–Solomon code with probability exceeding
`k · errorBound`, then there is a large coordinate set `S` (`|S| ≥ (1−δ)·n`) on which
every `fᵢ` is explained by a codeword of `code domain deg`.

The error is stated against the **native** in-tree bound `errorBound δ deg domain`
(which in this regime equals `n/q`, by `errorBound_eq_n_div_q_of_le_relUDR`), the exact
quantity the keystone `RS_correlatedAgreement_curves_uniqueDecodingRegime` consumes; no
cross-paper bridge is invented. The STIR-side `proximityError`-form of this statement
(`STIR.proximity_gap`) additionally requires the `proximityError ↔ (m−1)·errorBound`
bridge and the √ρ-radius (list-decoding) regime, both of which remain residual.

Proof: instantiate the curves keystone (`RS_correlatedAgreement_curves_*`, which is the
proven UDR branch of `correlatedAgreement_affine_curves`) with the supplied word stack;
this is exactly the call shape `Stir/Combine.lean:589+` uses to consume the keystone. The
resulting `jointAgreement` is then destructured into the witness-extraction form, with the
agreement-column subset relation `S ⊆ filter (v i · = f i ·)` read off pointwise. -/
theorem proximity_gap_uniqueDecodingRegime {k deg : ℕ}
    {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hδ : δ ≤ relativeUniqueDecodingRadius (ι := ι) (F := F)
      (C := ReedSolomon.code domain deg))
    (f : Fin (k + 1) → ι → F)
    (hProb :
      Pr_{
        let r ← $ᵖ F}[δᵣ(∑ i : Fin (k + 1), (r ^ (i : ℕ)) • f i,
          (ReedSolomon.code domain deg : Set (ι → F))) ≤ δ]
        > (k : ℝ≥0) * errorBound δ deg domain) :
    ∃ S : Finset ι,
      S.card ≥ (1 - δ) * (Fintype.card ι) ∧
      ∀ i : Fin (k + 1), ∃ u : ι → F,
        u ∈ (ReedSolomon.code domain deg : Set (ι → F)) ∧ ∀ x ∈ S, f i x = u x := by
  classical
  -- Instantiate the curves keystone (proven UDR branch of `correlatedAgreement_affine_curves`):
  -- the `k = 0` corner and the `k > 0` case both land in the unique-decoding regime here.
  have keystone : δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) := by
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0; exact RS_correlatedAgreement_curves_k_zero hδ
    · exact RS_correlatedAgreement_curves_uniqueDecodingRegime hkpos hδ
  -- Feed the probability hypothesis through the keystone (same shape as Combine.lean:599+).
  simp only [δ_ε_correlatedAgreementCurves] at keystone
  have hja := keystone f (by exact_mod_cast hProb)
  -- Destructure `jointAgreement` into the witness-extraction form.
  simp only [jointAgreement, ge_iff_le, SetLike.mem_coe] at hja
  obtain ⟨S, hS_card, v, hv⟩ := hja
  refine ⟨S, hS_card, fun i => ?_⟩
  refine ⟨v i, (hv i).1, fun x hx => ?_⟩
  -- The agreement column subset gives `v i x = f i x`; the witness form wants the symmetric eq.
  have hmem : x ∈ Finset.filter (fun j => v i j = f i j) Finset.univ :=
    (hv i).2 hx
  simpa using ((Finset.mem_filter.mp hmem).2).symm


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
    push Not at hge
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
