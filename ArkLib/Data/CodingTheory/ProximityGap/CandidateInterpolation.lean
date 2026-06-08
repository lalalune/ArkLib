import ArkLib.Data.CodingTheory.ProximityGap.MCASecondMoment
import ArkLib.Data.CodingTheory.ProximityGap.GrandChallenge141PrizeMath

open Classical
open scoped BigOperators

namespace ArkLib.CodingTheory.Research

/-! # Candidate: locating the threshold by bound interpolation -/

/-- Candidate endpoint for an interpolation-of-bounds route. -/
def candidate_interpolation_mca_bound (F : Type) [Field F] [Fintype F]
    (L : Finset F) : Prop :=
  ∃ τ, GrandChallengesLattice.mcaPrizeLatticeResolved L τ

end ArkLib.CodingTheory.Research
