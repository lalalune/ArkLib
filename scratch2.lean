import ArkLib.ProofSystem.ToyProblem.Leaderboard
import ArkLib.ProofSystem.ToyProblem.SoundnessBounds
import ArkLib.Data.CodingTheory.ProximityGap.Errors
import ArkLib.Data.CodingTheory.Basic.Distance

open ToyProblem Code InterleavedCode ListDecodable ProximityGap ProbabilityTheory
open scoped NNReal ENNReal ProbabilityTheory

theorem winningSetSoundness_le_toySoundnessError_mcaSafe_residual_proof {k : ℕ} {ι F : Type} [Fintype ι] [Field F] [Fintype F] [DecidableEq F] [Nonempty ι]
    (C : Submodule F (ι → F)) (δ : ℝ≥0) :
  δ < (minRelHammingDistCode (C : Set (ι → F)) : ℝ≥0) →
  winningSetSoundness (k := k) (C : Set (ι → F)) δ ≤
    (epsMCA (F := F) (A := F) (C : Set (ι → F)) δ).toNNReal +
      ((Lambda (interleavedCodeSet (κ := Fin 2) (C : Set (ι → F))) (δ : ℝ)).toNat : ℝ≥0)
        / (Fintype.card F : ℝ≥0) := by
  intro hδ
  sorry
