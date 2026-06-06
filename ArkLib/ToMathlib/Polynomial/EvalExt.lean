/-!
# Uniqueness of Polynomial Interpolation

This module establishes the uniqueness of polynomial interpolation over a field. Specifically, it
formalizes the classical result that if two polynomials $p, q \in \mathbb{F}[X]$ of degree strictly less than $n$
agree on at least $n$ distinct points (i.e., a subset $S \subseteq \mathbb{F}$ with $|S| \ge n$), then $p = q$.

In the context of algebraic complexity theory, PCPs, and interactive proofs (e.g., Reed–Solomon proximity
testing or KZG polynomial commitments), this property is central to establishing the soundness of
evaluation-based query protocols, where polynomials of bounded degree are uniquely determined by their
evaluations on a sufficiently large set of challenges.
-/

import Mathlib.LinearAlgebra.Lagrange

namespace Polynomial

variable {𝔽 : Type*} [Field 𝔽]

/--
Let $p, q \in \mathbb{F}[X]$ be polynomials whose degrees are strictly bounded by $n$.
If $p$ and $q$ agree on a subset $S \subseteq \mathbb{F}$ with cardinality at least $n$,
then they are identical.

**Proof intuition**: The difference polynomial $r = p - q$ has degree less than $n$. If $r \neq 0$, it can have at
most $\deg(r) < n$ roots. However, $r$ vanishes on all elements of $S$, which has size at least $n$,
contradicting the degree bound. Thus, $r = 0$, implying $p = q$.
-/
lemma eq_of_eval_eq_degree {p q : 𝔽[X]} {n : ℕ}
      (hp : p.degree < .some n) (hq : q.degree < .some n) (s : Finset 𝔽) :
    s.card ≥ n → (∀ x ∈ s, p.eval x = q.eval x) → p = q := by
  intros h h'
  by_cases h'' : p = 0 ∧ q = 0
  · rw [h''.1, h''.2]
  · have h'' : p ≠ 0 ∨ q ≠ 0 := by tauto
    have : p - q = 0 → p = q := by rw [sub_eq_zero]; exact id
    apply this
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ s
    · intros x h''
      specialize h' x h''
      simp only [eval_sub]
      rw [h']
      simp
    · have {x} : @Nat.cast (WithBot ℕ) WithBot.addMonoidWithOne.toNatCast x = .some x := by rfl
      refine lt_of_lt_of_le ?_ h
      rcases h'' with h'' | h''
      · rw [Polynomial.degree_eq_natDegree h'', this, WithBot.coe_lt_coe] at hp
        apply lt_of_le_of_lt
        · exact Polynomial.natDegree_sub_le _ _
        · by_cases q_eq : q = 0
          · rw [q_eq]
            simp [hp]
          · rw [Polynomial.degree_eq_natDegree q_eq, this, WithBot.coe_lt_coe] at hq
            simp [hp, hq]
      · rw [Polynomial.degree_eq_natDegree h'', this, WithBot.coe_lt_coe] at hq
        apply lt_of_le_of_lt
        · exact Polynomial.natDegree_sub_le _ _
        · by_cases p_eq : p = 0
          · rw [p_eq]
            simp [hq]
          · rw [Polynomial.degree_eq_natDegree p_eq, this, WithBot.coe_lt_coe] at hp
            simp [hp, hq]

/--
A variant of `eq_of_eval_eq_degree` using the natural degree `natDegree` instead of `degree`.
If two polynomials $p, q \in \mathbb{F}[X]$ have natural degree strictly less than $n$,
and they agree on a subset $S \subseteq \mathbb{F}$ of size at least $n$, then $p = q$.
-/
lemma eq_of_eval_eq_natDegree {p q : 𝔽[X]} {n : ℕ}
      (hp : p.natDegree < n) (hq : q.natDegree < n) (s : Finset 𝔽) :
    s.card ≥ n → (∀ x ∈ s, p.eval x = q.eval x) → p = q := by
    intros hs h_eval; use eq_of_eval_eq_degree (by
    exact lt_of_le_of_lt (Polynomial.degree_le_natDegree) (WithBot.coe_lt_coe.mpr hp)) (by
    exact lt_of_le_of_lt (Polynomial.degree_le_natDegree) (WithBot.coe_lt_coe.mpr hq)) s hs h_eval

end Polynomial
