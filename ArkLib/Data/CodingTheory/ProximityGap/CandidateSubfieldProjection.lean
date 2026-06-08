import ArkLib.Data.CodingTheory.ProximityGap.GrandChallenge141PrizeMath

open Classical
open scoped BigOperators

namespace ArkLib.CodingTheory.Research

/-! # Candidate: prime-subfield projection -/

/-- Proposed projection invariant. -/
def HasPrimeSubfieldProjection {F : Type} [Field F] [Fintype F] (L : Finset F) : Prop :=
  ∃ projectionSize : ℕ, 0 < projectionSize ∧ projectionSize ≤ L.card

/-- Open bridge from projection structure to MCA control. -/
def mca_bound_of_subfield_projection {F : Type} [Field F] [Fintype F]
    (L : Finset F) (C : Set (F → F)) (δ : ℝ≥0) : Prop :=
  HasPrimeSubfieldProjection L → ProximityGap.epsMCA C δ ≤ 2⁻¹²⁸

/-- Candidate endpoint for the subfield-projection route. -/
def candidate_subfield_projection_mca_bound (F : Type) [Field F] [Fintype F]
    (L : Finset F) : Prop :=
  ∃ τ, ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved L τ

end ArkLib.CodingTheory.Research
