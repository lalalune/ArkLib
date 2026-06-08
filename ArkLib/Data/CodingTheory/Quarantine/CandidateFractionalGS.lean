import ArkLib.Data.CodingTheory.ProximityGap.GrandChallenge141PrizeMath

open Classical
open scoped BigOperators

namespace ArkLib.CodingTheory.Research

/-! # Candidate: fractional Guruswami-Sudan relaxation -/

/-- Proposed fractional interpolation invariant. -/
def HasFractionalOverRelaxation {F : Type} [Field F] [Fintype F] (L : Finset F) : Prop :=
  ∃ slack : ℝ≥0, 0 < slack ∧ slack < 1 ∧ L.Nonempty

/-- Open bridge from fractional relaxation to MCA control. -/
def mca_bound_of_fractional_relaxation {F : Type} [Field F] [Fintype F]
    (L : Finset F) (C : Set (F → F)) (δ : ℝ≥0) : Prop :=
  HasFractionalOverRelaxation L → ProximityGap.epsMCA C δ ≤ 2⁻¹²⁸

/-- Candidate endpoint for the fractional-GS route. -/
def candidate_fractional_gs_mca_bound (F : Type) [Field F] [Fintype F]
    (L : Finset F) : Prop :=
  ∃ τ, ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved L τ

end ArkLib.CodingTheory.Research
