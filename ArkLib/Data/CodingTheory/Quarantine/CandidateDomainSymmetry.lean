import ArkLib.Data.CodingTheory.ProximityGap.GrandChallenge141PrizeMath

open scoped BigOperators NNReal

namespace ArkLib.CodingTheory.Research

/-! # Candidate: evaluation-domain symmetry -/

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- Proposed symmetry invariant needed by the candidate route. -/
def HasTranslationalSymmetry (L : Finset F) : Prop :=
  ∀ x ∈ L, ∀ y ∈ L, x + y ∈ L

/-- Open bridge from the symmetry invariant to MCA control. -/
def mca_bound_of_symmetry
    (L : Finset F) (C : Set (F → F)) (δ : ℝ≥0) : Prop :=
  HasTranslationalSymmetry L →
    ProximityGap.epsMCA (F := F) (A := F) C δ ≤ ((2 : ℝ≥0) ^ 128)⁻¹

/-- Candidate endpoint for the symmetry route. -/
def candidate_symmetry_mca_bound (domain : ι ↪ F) : Prop :=
  ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
    ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved domain τ

end ArkLib.CodingTheory.Research
