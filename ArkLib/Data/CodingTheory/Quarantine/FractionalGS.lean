import ArkLib.Data.CodingTheory.ProximityGap.141Math

open scoped BigOperators NNReal

namespace ArkLib.CodingTheory.Research

/-! # Candidate: fractional Guruswami-Sudan relaxation -/

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- Proposed fractional interpolation invariant. -/
def HasFractionalOverRelaxation (L : Finset F) : Prop :=
  ∃ slack : ℝ≥0, 0 < slack ∧ slack < 1 ∧ L.Nonempty

/-- Open bridge from fractional relaxation to MCA control. -/
def mca_bound_of_fractional_relaxation
    (L : Finset F) (C : Set (F → F)) (δ : ℝ≥0) : Prop :=
  HasFractionalOverRelaxation L →
    ProximityGap.epsMCA (F := F) (A := F) C δ ≤ ((2 : ℝ≥0) ^ 128)⁻¹

/-- Candidate endpoint for the fractional-GS route. -/
def candidate_fractional_gs_mca_bound (domain : ι ↪ F) : Prop :=
  ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
    ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved domain τ

end ArkLib.CodingTheory.Research
