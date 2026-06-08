import ArkLib.Data.CodingTheory.ProximityGap.MCASecondMoment
import ArkLib.Data.CodingTheory.ProximityGap.GrandChallenge141PrizeMath

open Classical
open scoped BigOperators

namespace ArkLib.CodingTheory.Research

/-! # Candidate: syndrome-space lens -/

/-- Candidate endpoint for a syndrome-space phase-transition route. -/
def candidate_syndrome_mca_bound (F : Type) [Field F] [Fintype F]
    (L : Finset F) : Prop :=
  ∃ τ, GrandChallengesLattice.mcaPrizeLatticeResolved L τ

end ArkLib.CodingTheory.Research
