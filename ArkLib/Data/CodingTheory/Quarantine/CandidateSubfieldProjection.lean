import ArkLib.Data.CodingTheory.ProximityGap.GrandChallenge141PrizeMath

open scoped BigOperators NNReal

namespace ArkLib.CodingTheory.Research

/-! # Candidate: prime-subfield projection -/

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- Proposed projection invariant. -/
def HasPrimeSubfieldProjection (L : Finset F) : Prop :=
  ∃ projectionSize : ℕ, 0 < projectionSize ∧ projectionSize ≤ L.card

/-- Open bridge from projection structure to MCA control. -/
def mca_bound_of_subfield_projection
    (L : Finset F) (C : Set (F → F)) (δ : ℝ≥0) : Prop :=
  HasPrimeSubfieldProjection L →
    ProximityGap.epsMCA (F := F) (A := F) C δ ≤ ((2 : ℝ≥0) ^ 128)⁻¹

/-- Candidate endpoint for the subfield-projection route. -/
def candidate_subfield_projection_mca_bound (domain : ι ↪ F) : Prop :=
  ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
    ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved domain τ

end ArkLib.CodingTheory.Research
