import ArkLib.Data.CodingTheory.ProximityGap.GrandChallenge141PrizeMath

open Classical
open scoped BigOperators

namespace ArkLib.CodingTheory.Research

/-- Candidate 7: Random Sub-field Projection Constraint
    Projecting the evaluation space down to a prime sub-field restricts the algebraic degree. -/

def HasPrimeSubfieldProjection {F : Type} [Field F] [Fintype F] (L : Finset F) : Prop :=
  sorry

/-- The sub-field projection bridge lemma. -/
lemma mca_bound_of_subfield_projection {F : Type} [Field F] [Fintype F]
    (L : Finset F) (hL_smooth : L.card.IsPowerOfTwo)
    (h_proj : HasPrimeSubfieldProjection L)
    (C : Set (F → F)) (δ : ℝ≥0) :
    ProximityGap.epsMCA C δ ≤ 2⁻¹²⁸ := by
  sorry

theorem candidate_subfield_projection_mca_bound (F : Type) [Field F] [Fintype F]
    (L : Finset F) (hL_smooth : L.card.IsPowerOfTwo) :
    ∃ τ, ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved L τ := by
  sorry

end ArkLib.CodingTheory.Research
