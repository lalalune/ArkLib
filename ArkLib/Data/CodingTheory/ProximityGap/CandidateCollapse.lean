import ArkLib.Data.CodingTheory.ProximityGap.MCASecondMoment
import ArkLib.Data.CodingTheory.ProximityGap.GrandChallenge141PrizeMath

open Classical
open scoped BigOperators

namespace ArkLib.CodingTheory.Research

/-!
# Candidate: list-decoding collapse

This file records the proposed route "interleaved list-size control implies MCA control" as
named `Prop` surfaces. Earlier revisions stated these bridges as theorems with `sorry`; that
misrepresented an open ABF26 prize route as proved content.
-/

/-- Interleaved list decoding has the requested epsilon-scale bound.  The exact list-decoding
object is intentionally left as future work rather than replaced by a fake witness. -/
def HasBoundedListSize (F : Type) [Field F] [Fintype F]
    (C : Set (F → F)) (m : ℕ) (δ : ℝ≥0) (ε : ℝ≥0) : Prop :=
  ∃ listBound : ℕ, (listBound : ℝ≥0) ≤ ε * Fintype.card F

/-- The open bridge from list-size control to MCA control. -/
def mca_of_bounded_list_size {F : Type} [Field F] [Fintype F]
    (C : Set (F → F)) (m : ℕ) (δ : ℝ≥0) (ε : ℝ≥0) : Prop :=
  HasBoundedListSize F C m δ ε → ProximityGap.epsMCA C δ ≤ ε

/-- Candidate endpoint for resolving the lattice prize through the list-decoding-collapse route. -/
def candidate_collapse_mca_bound (F : Type) [Field F] [Fintype F]
    (L : Finset F) : Prop :=
  ∃ τ, ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved L τ

end ArkLib.CodingTheory.Research
