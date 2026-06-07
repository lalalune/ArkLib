import Mathlib
import ArkLib.Data.CodingTheory.ProximityGap.BivariateVanishing

/-! **GS interpolation soundness** (BCIKS20 §5 Claim 5.7 / `hcount` core, GS99 Lemma 4):
a bivariate `Q` vanishing to order `m` at the `|A|` distinct agreement points
`(ω i, P (ω i))`, whose curve restriction `Q.eval P` has degree `< m·|A|`, must restrict to
zero on the curve `Y = P(X)`. This is the multiplicity Schwartz–Zippel forcing the GS factor. -/

open Polynomial Finset

namespace ArkLib.GS

variable {F : Type*} [CommRing F] [IsDomain F]

/-- **The soundness theorem.** If `Q` vanishes to order `m` at each `(ω i, P (ω i))` for `i` in a
finite index set `A` on which `ω` is injective, and the curve restriction `Q.eval P` has
`natDegree < m * |A|`, then `Q.eval P = 0`. The distinct roots `ω i` each contribute
multiplicity `≥ m`, summing to `≥ m·|A|`, exceeding the degree budget unless the restriction
vanishes. -/
theorem eval_eq_zero_of_vanishesToOrder_card {m : ℕ} {Q : Polynomial (Polynomial F)}
    {P : Polynomial F} {ι : Type*} (A : Finset ι) (ω : ι → F) (hω : Set.InjOn ω A)
    (hvan : ∀ i ∈ A, vanishesToOrder m Q (ω i) (P.eval (ω i)))
    (hdeg : (Q.eval P).natDegree < m * A.card) :
    Q.eval P = 0 := by
  classical
  by_contra hne
  -- Each ω i is a root of the restriction of multiplicity ≥ m.
  have hmult : ∀ i ∈ A, m ≤ rootMultiplicity (ω i) (Q.eval P) :=
    fun i hi => (hvan i hi).le_rootMultiplicity_eval P rfl hne
  -- Lower bound: m·|A| ≤ ∑ multiplicities.
  have hsum_ge : m * A.card ≤ ∑ i ∈ A, rootMultiplicity (ω i) (Q.eval P) := by
    calc m * A.card = ∑ _i ∈ A, m := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ i ∈ A, rootMultiplicity (ω i) (Q.eval P) := Finset.sum_le_sum hmult
  -- Upper bound: ∑ multiplicities ≤ card roots ≤ natDegree.
  have hsum_le : ∑ i ∈ A, rootMultiplicity (ω i) (Q.eval P) ≤ (Q.eval P).natDegree := by
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · subst hm0; simp only [Nat.zero_mul, Nat.not_lt_zero] at hdeg
    have hcount : ∑ i ∈ A, rootMultiplicity (ω i) (Q.eval P)
        = ∑ x ∈ A.image ω, (Q.eval P).roots.count x := by
      rw [Finset.sum_image (fun i hi j hj h => hω hi hj h)]
      exact Finset.sum_congr rfl (fun i _ => (Polynomial.count_roots (Q.eval P)).symm)
    rw [hcount]
    have hsub : A.image ω ⊆ (Q.eval P).roots.toFinset := by
      intro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      rw [Multiset.mem_toFinset, ← Multiset.count_pos, Polynomial.count_roots]
      exact lt_of_lt_of_le hmpos (hmult i hi)
    calc ∑ x ∈ A.image ω, (Q.eval P).roots.count x
        ≤ ∑ x ∈ (Q.eval P).roots.toFinset, (Q.eval P).roots.count x :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)
      _ = Multiset.card (Q.eval P).roots := Multiset.toFinset_sum_count_eq _
      _ ≤ (Q.eval P).natDegree := (Q.eval P).card_roots'
  omega

#print axioms ArkLib.GS.eval_eq_zero_of_vanishesToOrder_card

end ArkLib.GS
