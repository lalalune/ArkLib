import ArkLib.Data.CodingTheory.ProximityGap.MCASecondMoment
import ArkLib.Data.CodingTheory.ProximityGap.GrandChallenge141PrizeMath

open Classical
open scoped BigOperators

namespace ArkLib.CodingTheory.Research

/-!
# Candidate: derandomizing random-puncturing bounds

The univariate root-counting fact below is proved. The leap from that fact to a beyond-Johnson
MCA threshold is deliberately recorded as a `Prop`, not as a theorem with `sorry`.
-/

/-- A set acts pseudorandomly for low-degree univariate root counting. -/
def IsPseudoRandomForPolys (F : Type) [Field F] (L : Finset F) (deg : ℕ) : Prop :=
  ∀ p : Polynomial F, p ≠ 0 → p.natDegree ≤ deg →
    (L.filter fun x => p.eval x = 0).card ≤ p.natDegree

/-- Any finite subset satisfies the basic univariate root-counting bound. -/
lemma smooth_subgroup_is_pseudo_random {F : Type} [Field F] [Fintype F]
    (L : Finset F) (_hL_smooth : L.card.IsPowerOfTwo) (deg : ℕ) :
    IsPseudoRandomForPolys F L deg := by
  intro p hp _hdeg
  have h_roots := Polynomial.card_roots hp
  have h_subset : (L.filter fun x => p.eval x = 0).val ≤ p.roots := by
    intro x hx
    simp only [Finset.mem_val, Finset.mem_filter] at hx
    rw [Polynomial.mem_roots hp]
    exact hx.2
  exact le_trans (Multiset.card_le_of_le h_subset) h_roots

/-- Open bridge from deterministic pseudorandom root counting to the MCA bound. -/
def mca_bound_of_pseudo_random {F : Type} [Field F] [Fintype F]
    (L : Finset F) (deg : ℕ) (C : Set (F → F)) (δ : ℝ≥0) : Prop :=
  IsPseudoRandomForPolys F L deg → ProximityGap.epsMCA C δ ≤ (deg : ℝ≥0) / L.card

/-- Candidate endpoint for resolving the lattice prize through derandomization. -/
def candidate_derandomization_mca_bound (F : Type) [Field F] [Fintype F]
    (L : Finset F) : Prop :=
  ∃ τ, ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved L τ

end ArkLib.CodingTheory.Research
