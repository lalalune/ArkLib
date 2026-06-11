import ArkLib.Data.CodingTheory.ProximityGap.141Math

open scoped BigOperators NNReal

namespace ArkLib.CodingTheory.Research

/-! # Candidate: bivariate-resultant collapse -/

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- Proposed resultant-cancellation invariant. -/
def HasDestructiveResultant (L : Finset F) : Prop :=
  ∃ budget : ℕ, L.card ≤ budget

/-- Open bridge from resultant structure to MCA control. -/
def mca_bound_of_resultant
    (L : Finset F) (C : Set (F → F)) (δ : ℝ≥0) : Prop :=
  HasDestructiveResultant L →
    ProximityGap.epsMCA (F := F) (A := F) C δ ≤ ((2 : ℝ≥0) ^ 128)⁻¹

/-- Candidate endpoint for the resultant route. -/
def candidate_resultant_mca_bound (domain : ι ↪ F) : Prop :=
  ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
    ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved domain τ

end ArkLib.CodingTheory.Research
