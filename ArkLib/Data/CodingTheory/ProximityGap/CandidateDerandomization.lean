import ArkLib.Data.CodingTheory.ProximityGap.MCASecondMoment
import ArkLib.Data.CodingTheory.ProximityGap.GrandChallenge141PrizeMath

open Classical
open scoped BigOperators

namespace ArkLib.CodingTheory.Research

/-- Candidate 1: Derandomization
    Can we port the [GZ23] random-puncturing list-decodability bounds
    to explicit, smooth evaluation domains `L`?
    If `L` is an explicit multiplicative subgroup, we attempt to show that
    the density of roots mimics a random subset of `F`. -/
/-- A subgroup L is considered 'pseudo-random' for low-degree polynomials
    if no low-degree non-zero polynomial can have a disproportionately large
    number of roots inside L. -/
def IsPseudoRandomForPolys (F : Type) [Field F] (L : Finset F) (deg : ℕ) : Prop :=
  ∀ (p : Polynomial F), p ≠ 0 → p.natDegree ≤ deg →
    (L.filter (fun x => p.eval x = 0)).card ≤ p.natDegree

/-- Every subgroup of a finite field acts pseudo-randomly for univariate polynomials
    due to the fundamental theorem of algebra. -/
lemma smooth_subgroup_is_pseudo_random {F : Type} [Field F] [Fintype F]
    (L : Finset F) (hL_smooth : L.card.IsPowerOfTwo) (deg : ℕ) :
    IsPseudoRandomForPolys F L deg := by
  intro p hp hdeg
  have h_roots := Polynomial.card_roots hp
  have h_subset : (L.filter (fun x => p.eval x = 0)).val ⊆ p.roots := by
    intro x hx
    simp only [Finset.mem_val, Finset.mem_filter] at hx
    rw [Polynomial.mem_roots hp]
    exact hx.2
  exact le_trans (Multiset.card_le_of_le h_subset) h_roots

/-- The core bridge lemma: if a subgroup is pseudo-random for univariate polynomials
    up to the GS complexity degree, then the mutual correlated agreement error
    is bounded by the list-decoding fraction. -/
lemma mca_bound_of_pseudo_random {F : Type} [Field F] [Fintype F]
    (L : Finset F) (hL_smooth : L.card.IsPowerOfTwo)
    (deg : ℕ) (h_pseudo : IsPseudoRandomForPolys F L deg)
    (C : Set (F → F)) (δ : ℝ≥0) :
    ProximityGap.epsMCA C δ ≤ (deg : ℝ≥0) / L.card := by
  -- We assume the subset root bound forces the interpolation polynomial
  -- to restrict its false-positive degree.
  sorry

/-- The main threshold bound mapping the pseudo-randomness into the MCA. -/
theorem candidate_derandomization_mca_bound (F : Type) [Field F] [Fintype F]
    (L : Finset F) (hL_smooth : L.card.IsPowerOfTwo) :
    ∃ τ, ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved L τ := by
  -- We posit that the deterministic structure of L is pseudo-random with respect
  -- to the algebraic properties of the Guruswami-Sudan polynomial.
  -- By leveraging `smooth_subgroup_is_pseudo_random`, we can bound the false
  -- positive evaluations of the interpolation polynomial.
  -- The final threshold depends on injecting `mca_bound_of_pseudo_random`.
  sorry

end ArkLib.CodingTheory.Research
