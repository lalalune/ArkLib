import ArkLib.Data.CodingTheory.ProximityGap.MCASecondMoment
import ArkLib.Data.CodingTheory.ProximityGap.GrandChallenge141PrizeMath

open Classical
open scoped BigOperators

namespace ArkLib.CodingTheory.Research

/-!
# Candidate: derandomizing random-puncturing bounds

Candidate attack strategy on the open MCA Grand Challenge prize: port random-puncturing
list-decodability bounds to explicit, smooth evaluation domains. The univariate root-counting
fact below is proved. The leap from that fact to a beyond-Johnson MCA threshold is deliberately
recorded as a `Prop`, not as a theorem with `sorry`.
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

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- Candidate endpoint for resolving the lattice prize through derandomization.

Stated against a Reed–Solomon evaluation `domain : ι ↪ F` — the type
`ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved` actually requires — so the
statement type-checks. (An earlier revision passed a bare `Finset F` here, which does not unify
with the required `ι ↪ F` and silently failed to elaborate.) This is an open conjecture recorded
as a `Prop`, not a theorem. -/
def candidate_derandomization_mca_bound_conjecture (domain : ι ↪ F) : Prop :=
  ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
    ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved domain τ

/-- Backwards-compatible name for the derandomization endpoint. -/
def candidate_derandomization_mca_bound (domain : ι ↪ F) : Prop :=
  candidate_derandomization_mca_bound_conjecture domain

end ArkLib.CodingTheory.Research
