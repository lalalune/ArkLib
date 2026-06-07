import ArkLib.Data.CodingTheory.Connections.GKL24FirstMoment

namespace ProximityGap

open NNReal Code Finset
open scoped ProbabilityTheory BigOperators

section
variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

def GKL24MaxCorrWitnessCoverResidual_scratch
    (MC : Submodule F (ι → F)) (δ p : ℝ≥0) (B_T : ℝ) : Prop :=
  ∀ u : WordStack F (Fin 2) ι,
    ∃ T : Finset (ι → F),
      (∀ w ∈ T, w ∈ (MC : Set (ι → F))) ∧
        mcaBad (F := F) (MC : Set (ι → F)) δ (u 0) (u 1) ⊆
          T.biUnion (fun w =>
            mcaBadWitness (F := F) (MC : Set (ι → F)) δ (u 0) (u 1) w) ∧
        (T.card : ℝ) ≤ B_T ∧
          ∀ w ∈ T,
            ∃ D : Finset ι,
              maxCorrAgreeDomain MC p (u 0) (u 1) D ∧
                (∀ γ ∈ mcaBadWitness (F := F) (MC : Set (ι → F)) δ (u 0) (u 1) w,
                  D ⊂ lineAgreeSet (u 0) (u 1) w γ) ∧
                  (∀ γ ∈ mcaBadWitness (F := F) (MC : Set (ι → F)) δ (u 0) (u 1) w,
                    ∀ γ' ∈ mcaBadWitness (F := F) (MC : Set (ι → F)) δ (u 0) (u 1) w,
                      γ ≠ γ' →
                        ((1 - p) * Fintype.card ι : ℝ≥0) ≤
                          (((lineAgreeSet (u 0) (u 1) w γ ∩
                              lineAgreeSet (u 0) (u 1) w γ').card : ℕ) : ℝ≥0))

theorem GKL24FirstMomentWitnessCoverResidual_of_maxCorr_cover_scratch
    (MC : Submodule F (ι → F)) (δ p : ℝ≥0) {B_T : ℝ}
    (hmax : GKL24MaxCorrWitnessCoverResidual_scratch MC δ p B_T) :
    GKL24FirstMomentWitnessCoverResidual MC δ B_T ((p : ℝ) * (Fintype.card ι : ℝ)) := by
  intro u
  obtain ⟨T, hTsub, hcover, hcard, hmaxT⟩ := hmax u
  refine ⟨T, hTsub, hcover, hcard, ?_⟩
  intro w hw
  obtain ⟨D, hD, hstrict, hIlarge⟩ := hmaxT w hw
  exact mcaBadWitness_card_le_radius_mul_card_of_maxCorrAgreeDomain
    MC δ p (u 0) (u 1) w D (hTsub w hw) hD hstrict hIlarge

theorem mcaBad_card_le_of_gkl24_maxCorr_witnessCover_residual_scratch
    (MC : Submodule F (ι → F)) (δ p : ℝ≥0) {B_T : ℝ}
    (hres : GKL24MaxCorrWitnessCoverResidual_scratch MC δ p B_T)
    (u : WordStack F (Fin 2) ι) :
    ((mcaBad (F := F) (MC : Set (ι → F)) δ (u 0) (u 1)).card : ℝ) ≤
      B_T * ((p : ℝ) * (Fintype.card ι : ℝ)) :=
  mcaBad_card_le_of_gkl24_witnessCover_residual MC δ
    (mul_nonneg (by positivity) (by positivity))
    (GKL24FirstMomentWitnessCoverResidual_of_maxCorr_cover_scratch MC δ p hres) u

theorem epsMCA_le_ofReal_of_gkl24_maxCorr_witnessCover_residual_scratch
    (MC : Submodule F (ι → F)) (δ p : ℝ≥0) {B_T : ℝ}
    (hres : GKL24MaxCorrWitnessCoverResidual_scratch MC δ p B_T) :
    epsMCA (F := F) (A := F) (MC : Set (ι → F)) δ ≤
      ENNReal.ofReal ((B_T * ((p : ℝ) * (Fintype.card ι : ℝ))) / Fintype.card F) :=
  epsMCA_le_ofReal_of_gkl24_witnessCover_residual MC δ
    (mul_nonneg (by positivity) (by positivity))
    (GKL24FirstMomentWitnessCoverResidual_of_maxCorr_cover_scratch MC δ p hres)

end

end ProximityGap
