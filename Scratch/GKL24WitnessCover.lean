import ArkLib.Data.CodingTheory.Connections.GKL24FirstMoment

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace ProximityGap

open NNReal Code Finset
open scoped ProbabilityTheory BigOperators

section

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

open CodingTheory.Bridge

theorem mcaBad_card_le_listFactor_mul_perCodeword_of_cover
    (MC : Submodule F (ι → F)) (δ : ℝ≥0) (u₀ u₁ : ι → F)
    (T : Finset (ι → F))
    (hcover :
      mcaBad (F := F) (MC : Set (ι → F)) δ u₀ u₁ ⊆
        T.biUnion (fun w => mcaBadWitness (F := F) (MC : Set (ι → F)) δ u₀ u₁ w))
    {b B_T : ℝ} (hb0 : 0 ≤ b) (hb_card : (T.card : ℝ) ≤ B_T)
    (hper : ∀ w ∈ T,
      ((mcaBadWitness (F := F) (MC : Set (ι → F)) δ u₀ u₁ w).card : ℝ) ≤ b) :
    ((mcaBad (F := F) (MC : Set (ι → F)) δ u₀ u₁).card : ℝ) ≤ B_T * b := by
  classical
  have hsum : ((mcaBad (F := F) (MC : Set (ι → F)) δ u₀ u₁).card : ℝ) ≤
      ∑ w ∈ T, ((mcaBadWitness (F := F) (MC : Set (ι → F)) δ u₀ u₁ w).card : ℝ) := by
    calc ((mcaBad (F := F) (MC : Set (ι → F)) δ u₀ u₁).card : ℝ)
        ≤ ((T.biUnion
            (fun w => mcaBadWitness (F := F) (MC : Set (ι → F)) δ u₀ u₁ w)).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hcover
      _ ≤ ((∑ w ∈ T,
            (mcaBadWitness (F := F) (MC : Set (ι → F)) δ u₀ u₁ w).card : ℕ) : ℝ) := by
          exact_mod_cast (Finset.card_biUnion_le
            (s := T)
            (t := fun w => mcaBadWitness (F := F) (MC : Set (ι → F)) δ u₀ u₁ w))
      _ = ∑ w ∈ T,
            ((mcaBadWitness (F := F) (MC : Set (ι → F)) δ u₀ u₁ w).card : ℝ) := by
          push_cast
          ring
  calc ((mcaBad (F := F) (MC : Set (ι → F)) δ u₀ u₁).card : ℝ)
      ≤ ∑ w ∈ T,
          ((mcaBadWitness (F := F) (MC : Set (ι → F)) δ u₀ u₁ w).card : ℝ) := hsum
    _ ≤ ∑ _w ∈ T, b := Finset.sum_le_sum (fun w hw => hper w hw)
    _ = (T.card : ℝ) * b := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ B_T * b := by exact mul_le_mul_of_nonneg_right hb_card hb0

def GKL24FirstMomentWitnessCoverResidual
    (MC : Submodule F (ι → F)) (δ : ℝ≥0) (B_T b : ℝ) : Prop :=
  ∀ u : WordStack F (Fin 2) ι,
    ∃ T : Finset (ι → F),
      mcaBad (F := F) (MC : Set (ι → F)) δ (u 0) (u 1) ⊆
        T.biUnion (fun w =>
          mcaBadWitness (F := F) (MC : Set (ι → F)) δ (u 0) (u 1) w) ∧
      (T.card : ℝ) ≤ B_T ∧
      ∀ w ∈ T,
        ((mcaBadWitness (F := F) (MC : Set (ι → F)) δ (u 0) (u 1) w).card : ℝ) ≤ b

theorem GKL24FirstMomentWitnessCoverResidual.ofFullCarrier
    (MC : Submodule F (ι → F)) (δ : ℝ≥0) {B_T b : ℝ}
    (hres : GKL24FirstMomentResidual MC δ B_T b) :
    GKL24FirstMomentWitnessCoverResidual MC δ B_T b := by
  classical
  intro u
  obtain ⟨T, hT, hcard, hper⟩ := hres u
  exact ⟨T,
    mcaBad_subset_biUnion_mcaBadWitness (F := F) (A := F)
      (MC : Set (ι → F)) δ (u 0) (u 1) T hT,
    hcard, hper⟩

theorem mcaBad_card_le_of_gkl24_witnessCover_residual
    (MC : Submodule F (ι → F)) (δ : ℝ≥0) {B_T b : ℝ} (hb0 : 0 ≤ b)
    (hres : GKL24FirstMomentWitnessCoverResidual MC δ B_T b) (u : WordStack F (Fin 2) ι) :
    ((mcaBad (F := F) (MC : Set (ι → F)) δ (u 0) (u 1)).card : ℝ) ≤ B_T * b := by
  obtain ⟨T, hcover, hcard, hper⟩ := hres u
  exact mcaBad_card_le_listFactor_mul_perCodeword_of_cover MC δ (u 0) (u 1) T hcover
    hb0 hcard hper

end

end ProximityGap
