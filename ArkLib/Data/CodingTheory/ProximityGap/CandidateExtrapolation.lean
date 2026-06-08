import ArkLib.Data.CodingTheory.ProximityGap.GrandChallenge141PrizeMath

open Classical
open scoped BigOperators

namespace ArkLib.CodingTheory.Research

/-! # Candidate: interpolating between Johnson and capacity bounds -/

/-- Proposed explicit interpolation bound in the Johnson-to-capacity gap. -/
def HasExtrapolativeBound {F : Type} [Field F] [Fintype F] (L : Finset F) : Prop :=
  ∃ profile : ℝ≥0 → ℝ≥0, ∀ δ, ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved L δ → profile δ ≤ 2⁻¹²⁸

/-- Open bridge from the extrapolative profile to MCA control. -/
def mca_bound_of_extrapolation {F : Type} [Field F] [Fintype F]
    (L : Finset F) (C : Set (F → F)) (δ : ℝ≥0) : Prop :=
  HasExtrapolativeBound L → ProximityGap.epsMCA C δ ≤ 2⁻¹²⁸

/-- Candidate endpoint for the extrapolation route. -/
def candidate_extrapolation_mca_bound (F : Type) [Field F] [Fintype F]
    (L : Finset F) : Prop :=
  ∃ τ, ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved L τ

end ArkLib.CodingTheory.Research
