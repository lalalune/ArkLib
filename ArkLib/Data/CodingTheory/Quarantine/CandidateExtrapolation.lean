import ArkLib.Data.CodingTheory.ProximityGap.GrandChallenge141PrizeMath

open scoped BigOperators NNReal

namespace ArkLib.CodingTheory.Research

/-! # Candidate: interpolating between Johnson and capacity bounds -/

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- Proposed explicit interpolation bound in the Johnson-to-capacity gap. -/
def HasExtrapolativeBound (domain : ι ↪ F) : Prop :=
  ∃ profile : (Fin 4 → Fin (Fintype.card ι + 1)) → ℝ≥0, ∀ τ,
    ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved domain τ →
      profile τ ≤ ((2 : ℝ≥0) ^ 128)⁻¹

/-- Open bridge from the extrapolative profile to MCA control. -/
def mca_bound_of_extrapolation
    (domain : ι ↪ F) (C : Set (ι → F)) (δ : ℝ≥0) : Prop :=
  HasExtrapolativeBound domain →
    ProximityGap.epsMCA (F := F) (A := F) C δ ≤ ((2 : ℝ≥0) ^ 128)⁻¹

/-- Candidate endpoint for the extrapolation route. -/
def candidate_extrapolation_mca_bound (domain : ι ↪ F) : Prop :=
  ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
    ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved domain τ

end ArkLib.CodingTheory.Research
