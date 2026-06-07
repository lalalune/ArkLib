import ArkLib.ToMathlib.UniformTranslationAverage
import ArkLib.ToMathlib.DG25CoveringRadiusProof
import ArkLib.Data.CodingTheory.InterleavedRowDistance
import ArkLib.Data.Probability.Notation

open scoped NNReal ENNReal BigOperators ProbabilityTheory
open Code

namespace ArkLib

variable {F : Type} [Field F] [Fintype F] [Nonempty F]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem sum_uniform_line_probability_eq (P : (ι → F) → Prop) [DecidablePred P] (w : ι → F) :
    (∑ u₀ : ι → F, (Fintype.card (ι → F) : ℝ≥0∞)⁻¹ *
        Pr_{let γ ← $ᵖ F}[P (u₀ + γ • w)])
      = Pr_{let u ← $ᵖ (ι → F)}[P u] := by
  classical
  rw [ProbabilityTheory.Pr_eq_tsum_indicator]
  simp_rw [ProbabilityTheory.Pr_eq_tsum_indicator]
  simp only [PMF.uniformOfFintype_apply]
  simp_rw [tsum_fintype]
  exact sum_uniform_line_indicator_eq P w

theorem dg25_sampling_mass_le_epsCA_of_coveringRadius
    (C : Set (ι → F)) (δ δ' : ℝ≥0)
    (hδ' : (δ' : ENNReal) = ⨆ u : ι → F, δᵣ(u, C))
    (hδ_lt : δ < δ') :
    (((Fintype.card F - 1 : ℝ≥0) / Fintype.card F : ℝ≥0∞) *
        Pr_{let u ← $ᵖ (ι → F)}[δᵣ(u, C) ≤ δ])
      ≤ ProximityGap.epsCA (F := F) (A := F) C δ δ := by
  classical
  have hδlt_iSup : (δ : ENNReal) < ⨆ u : ι → F, δᵣ(u, C) := by
    rw [← hδ']
    exact ENNReal.coe_lt_coe.mpr hδ_lt
  obtain ⟨w, hw⟩ := exists_lt_of_lt_iSup hδlt_iSup
  let lineProb : (ι → F) → ENNReal :=
    fun u₀ => Pr_{let γ ← $ᵖ F}[δᵣ(u₀ + γ • w, C) ≤ δ]
  have hline_le : ∀ u₀ : ι → F,
      lineProb u₀ ≤ ProximityGap.epsCA (F := F) (A := F) C δ δ := by
    intro u₀
    have hnot : ¬ jointProximity (C := C) (u := finMapTwoWords u₀ w) δ := by
      intro hjp
      have hwle := relDistFromCode_snd_le_of_jointProximity (C := C) (u₀ := u₀)
        (w := w) (δ := δ) hjp
      exact (not_lt_of_ge hwle) hw
    simpa [lineProb, finMapTwoWords] using
      ProximityGap.epsCA_ge_line_prob_of_not_jointProximity
        (F := F) (C := C) δ δ (finMapTwoWords u₀ w) hnot
  have havg_le :
      (∑ u₀ : ι → F, (Fintype.card (ι → F) : ℝ≥0∞)⁻¹ * lineProb u₀)
        ≤ ProximityGap.epsCA (F := F) (A := F) C δ δ := by
    refine le_trans (sum_uniform_mul_le_iSup lineProb) ?_
    exact iSup_le hline_le
  have hbridge := sum_uniform_line_probability_eq
    (P := fun u : ι → F => δᵣ(u, C) ≤ δ) w
  have hpr_le : Pr_{let u ← $ᵖ (ι → F)}[δᵣ(u, C) ≤ δ]
      ≤ ProximityGap.epsCA (F := F) (A := F) C δ δ := by
    rw [← hbridge]
    exact havg_le
  have hden_pos : 0 < (Fintype.card F : ℝ≥0) := by
    exact_mod_cast Fintype.card_pos
  have hcoef_nn :
      ((Fintype.card F - 1 : ℝ≥0) / (Fintype.card F : ℝ≥0)) ≤ 1 := by
    rw [div_le_iff₀ hden_pos]
    norm_num
  have hcoef_le_one :
      (((Fintype.card F - 1 : ℝ≥0) / Fintype.card F : ℝ≥0∞) ≤ 1) :=
    ENNReal.coe_le_coe.mpr hcoef_nn
  exact le_trans (mul_le_mul_right' hcoef_le_one _) (by simpa using hpr_le)

end ArkLib
