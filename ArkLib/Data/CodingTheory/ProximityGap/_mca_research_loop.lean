import ArkLib.Data.CodingTheory.ProximityGap.MCASecondMoment
import ArkLib.Data.CodingTheory.BinomialEntropyBound

open Classical
open scoped BigOperators

namespace ArkLib.CodingTheory.Research

/-- Open beyond-UDR Guruswami-Sudan mass-bound route for the prize. -/
def mcaPrize_beyond_udr_bound (domain : Type) [Fintype domain] : Prop :=
  ∃ τ, GrandChallengesLattice.mcaPrizeLatticeResolved domain τ

/-- Lemma bounding the density of false-positive roots for univariate polynomials. -/
lemma root_density_bound_univ {F : Type} [Field F] [Fintype F] (p : Polynomial F) (hp : p ≠ 0) :
    (Finset.univ.filter fun x => p.eval x = 0).card ≤ p.natDegree := by
  have h_roots := Polynomial.card_roots hp
  have h_subset : (Finset.univ.filter fun x => p.eval x = 0).val ≤ p.roots := by
    intro x hx
    simp only [Finset.mem_val, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    rw [Polynomial.mem_roots hp]
    exact hx
  exact le_trans (Multiset.card_le_of_le h_subset) h_roots

end ArkLib.CodingTheory.Research
