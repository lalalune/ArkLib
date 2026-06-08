import ArkLib.Data.CodingTheory.ProximityGap.MCASecondMoment
import ArkLib.Data.CodingTheory.ProximityGap.GrandChallenge141PrizeMath

open Classical
open scoped BigOperators

namespace ArkLib.CodingTheory.Research

/-- Candidate 2: List-Decoding Collapse
    Prove that a tight list-decoding bound implies the MCA bound directly.
    We seek to bridge the definition of list-size bounds to the `epsMCA`
    proximity gap error definition. -/
/-- Definition of the interleaved list decoding set size bound. -/
def HasBoundedListSize (F : Type) [Field F] [Fintype F] (C : Set (F → F)) (m : ℕ) (δ : ℝ≥0) (ε : ℝ≥0) : Prop :=
  -- Represents `|Λ(C^{≡m},δ)| ≤ ε * |F|`
  sorry

/-- The collapse bridge: if the list size is bounded by ε, then the
    Mutual Correlated Agreement error is also bounded by a function of ε. -/
lemma mca_of_bounded_list_size {F : Type} [Field F] [Fintype F]
    (C : Set (F → F)) (m : ℕ) (δ : ℝ≥0) (ε : ℝ≥0)
    (h_list : HasBoundedListSize F C m δ ε) :
    ProximityGap.epsMCA C δ ≤ ε := by
  -- We assume that every 'bad' point in the MCA sense must correspond
  -- to a spurious polynomial in the interleaved list decoding set.
  sorry

/-- The main threshold bound mapping the list-decoding size into the MCA. -/
theorem candidate_collapse_mca_bound (F : Type) [Field F] [Fintype F]
    (L : Finset F) (hL_smooth : L.card.IsPowerOfTwo) :
    ∃ τ, ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved L τ := by
  -- We assume `|Λ(C^{≡m},δ)| ≤ ε*·|F|` for an interleaved Reed-Solomon code,
  -- and use this to bound the mutual correlated agreement error (mcaBad count)
  -- via `mca_of_bounded_list_size`.
  sorry

end ArkLib.CodingTheory.Research
