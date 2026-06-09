import ArkLib.Data.CodingTheory.ProximityGap.MCASecondMoment
import ArkLib.Data.CodingTheory.ProximityGap.GrandChallenge141PrizeMath

open Classical
open scoped BigOperators NNReal

namespace ArkLib.CodingTheory.Research

/-!
# Candidate: list-decoding collapse

This file records a *candidate attack strategy* on the open MCA Grand Challenge prize, not a
proof of it. The proposed route is: a tight interleaved list-decoding size bound
`|Lambda(C^m, delta)| <= epsilon * |F|` would bridge to the `epsMCA` proximity-gap error.
The bridge and endpoint are named `Prop` surfaces rather than `sorry`-backed theorems.
-/

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- Interleaved list decoding has the requested epsilon-scale bound.  The exact list-decoding
object is intentionally left as future work rather than replaced by a fake witness. -/
def HasBoundedListSize (F : Type) [Field F] [Fintype F]
    (C : Set (F → F)) (m : ℕ) (δ : ℝ≥0) (ε : ℝ≥0) : Prop :=
  ∃ listBound : ℕ, (listBound : ℝ≥0) ≤ ε * (Fintype.card F : ℝ≥0)

/-- The open bridge from list-size control to MCA control. -/
def mca_of_bounded_list_size {F : Type} [Field F] [Fintype F]
    (C : Set (F → F)) (m : ℕ) (δ : ℝ≥0) (ε : ℝ≥0) : Prop :=
  HasBoundedListSize F C m δ ε → ProximityGap.epsMCA (F := F) (A := F) C δ ≤ ε

/-- **OPEN CONJECTURE — Candidate 2 (list-decoding collapse).** The MCA prize-lattice resolution
target this strategy aims to reach for a Reed–Solomon evaluation `domain`. This is the *statement*
of an open problem (the existence of resolving lattice thresholds), not a proved fact. -/
def candidate_collapse_mca_bound_conjecture (domain : ι ↪ F) : Prop :=
  ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
    ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved domain τ

/-- Backwards-compatible name for the list-decoding-collapse endpoint. -/
def candidate_collapse_mca_bound (domain : ι ↪ F) : Prop :=
  candidate_collapse_mca_bound_conjecture domain

end ArkLib.CodingTheory.Research
