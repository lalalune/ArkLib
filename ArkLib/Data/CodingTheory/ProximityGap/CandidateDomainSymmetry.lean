import ArkLib.Data.CodingTheory.ProximityGap.GrandChallenge141PrizeMath

open Classical
open scoped BigOperators

namespace ArkLib.CodingTheory.Research

/-! # Candidate: evaluation-domain symmetry -/

/-- Proposed symmetry invariant needed by the candidate route. -/
def HasTranslationalSymmetry {F : Type} [Field F] [Fintype F] (L : Finset F) : Prop :=
  ∀ x ∈ L, ∀ y ∈ L, x + y ∈ L

/-- Open bridge from the symmetry invariant to MCA control. -/
def mca_bound_of_symmetry {F : Type} [Field F] [Fintype F]
    (L : Finset F) (C : Set (F → F)) (δ : ℝ≥0) : Prop :=
  HasTranslationalSymmetry L → ProximityGap.epsMCA C δ ≤ 2⁻¹²⁸

/-- Candidate endpoint for the symmetry route. -/
def candidate_symmetry_mca_bound (F : Type) [Field F] [Fintype F]
    (L : Finset F) : Prop :=
  ∃ τ, ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved L τ

end ArkLib.CodingTheory.Research
