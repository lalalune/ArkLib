import ArkLib.ProofSystem.ToyProblem.SoundnessBounds
import Mathlib.Data.Fintype.Card

open scoped NNReal

variable {ι F : Type} [Fintype ι] [Field F] [Fintype F] [DecidableEq F]

theorem my_trivial_proof {k : ℕ} [Nonempty ι]
    (C : Set (ι → F)) (δ : ℝ≥0)
    (hδle : δ ≤ 1)
    (hEnc : ∃ encode : (Fin k → F) →ₗ[F] (ι → F),
      (∀ m, encode m ∈ C) ∧ ∀ c ∈ C, ∃ m, encode m = c)
    (hF : (Fintype.card F : ℝ) >
      ((Lambda (interleavedCodeSet (κ := Fin 2) C) (δ : ℝ)).toNat).choose 2) :
    ∃ (f₁ f₂ : ι → F)
      (chal : Fin (Lambda (interleavedCodeSet (κ := Fin 2) C) (δ : ℝ)).toNat → F),
      Function.Injective chal ∧
      ∃ c : Fin (Lambda (interleavedCodeSet (κ := Fin 2) C) (δ : ℝ)).toNat → (ι → F),
        (∀ j, c j ∈ C) ∧
          ∀ j, minRelHammingDistCode C ≤ δ := by
  sorry
