/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib.Combinatorics.Nullstellensatz
import Mathlib.Algebra.MvPolynomial.Coeff
import Mathlib.Data.Nat.Choose.Dvd

/-!
# The Erdős–Heilbronn restricted-sumset bound (`h = 2` case)

This file proves the **Erdős–Heilbronn theorem** in the `h = 2` case via Alon's Combinatorial
Nullstellensatz (`MvPolynomial.combinatorial_nullstellensatz_exists_eval_nonzero`).

For a field `F` of prime characteristic `p`, a finite set `A ⊆ F` with `n := |A| ≥ 2`, and
`2(n - 2) < p`, the set of distinct-pair sums

  `Σ₂(A) := { ∑_{a ∈ S} a : S ⊆ A, |S| = 2 } = { a + b : a, b ∈ A, a ≠ b }`

has cardinality at least `2n - 3`:

  `|Σ₂(A)| ≥ 2(n - 2) + 1`   (`erdos_heilbronn_two`).

## Proof (Alon–Nathanson–Ruzsa, `h = 2`)

Suppose `|Σ₂(A)| ≤ 2(n - 2)`. Pad `Σ₂(A)` to a set `C'` of size exactly `m := 2(n - 2)`
(possible because `|F| ≥ p > m`). Consider the two-variable polynomial

  `Q := (X₁ - X₀) · ∏_{c ∈ C'} (X₀ + X₁ - C c) ∈ F[X₀, X₁]`.

`Q` vanishes on all of `A × A`: tuples with `X₀ = X₁` are killed by the first factor; tuples with
`X₀ ≠ X₁` have `X₀ + X₁ ∈ Σ₂(A) ⊆ C'`, killing one factor of the product.

`Q` has total degree `1 + m = 2n - 3`, equal to the degree of the monomial
`t := X₀^{n-1} X₁^{n-2}`. The coefficient of `t` in `Q` equals its coefficient in the leading
part `(X₁ - X₀)(X₀ + X₁)^m`, namely

  `C(m, n-1) - C(m, n-2)`,

which is nonzero mod `p` because `(n-1)·(C(m,n-2) - C(m,n-1)) = C(m,n-2)` and `p` is coprime to
`C(m, n-2)` (as `m < p`). Since `t i < n = |A|` for both variables, the Combinatorial
Nullstellensatz produces a point of `A × A` where `Q ≠ 0`, contradicting the vanishing.

## References

- [Alon, *Combinatorial Nullstellensatz*][Alon_1999]
- Dias da Silva, Hamidoune; Erdős, Heilbronn.
-/

namespace MvPolynomial

open scoped BigOperators

section ErdosHeilbronn

variable {F : Type*} [Field F]

/-- The target monomial `X₀^{a} X₁^{b}` as an element of `Fin 2 →₀ ℕ`. -/
private noncomputable def ehMon (a b : ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 a + Finsupp.single 1 b

private lemma ehMon_apply_zero (a b : ℕ) : ehMon a b 0 = a := by
  simp [ehMon]

private lemma ehMon_apply_one (a b : ℕ) : ehMon a b 1 = b := by
  simp [ehMon]

/-- The coefficient of `X₀^{a} X₁^{b}` in `(X 0 + X 1)^N` (over a field). -/
private lemma coeff_ehMon_add_pow (a b N : ℕ) (hab : a + b = N) :
    coeff (ehMon a b) ((X 0 + X 1 : MvPolynomial (Fin 2) F) ^ N) = (N.choose a : F) := by
  rw [coeff_add_pow]
  rw [ehMon_apply_zero, ehMon_apply_one]
  rw [if_pos]
  · rw [Finset.mem_antidiagonal]; exact hab

/-- **Leading coefficient computation.** The coefficient of `X₀^{n-1} X₁^{n-2}` in
`(X 1 - X 0)(X 0 + X 1)^m` with `m = 2(n-2)` is `C(m, n-1) - C(m, n-2)` (as an element of `F`).
We prove it for `m = a' + b'` with the relevant exponent bookkeeping. -/
private lemma coeff_leading
    {n : ℕ} (hn : 3 ≤ n) :
    coeff (ehMon (n - 1) (n - 2))
        ((X 1 - X 0 : MvPolynomial (Fin 2) F) * (X 0 + X 1) ^ (2 * (n - 2)))
      = ((2 * (n - 2)).choose (n - 1) : F) - ((2 * (n - 2)).choose (n - 2) : F) := by
  classical
  set m := 2 * (n - 2) with hm
  rw [sub_mul, coeff_sub]
  -- `X 1 * (X0+X1)^m` term
  have hX1 : coeff (ehMon (n - 1) (n - 2)) (X 1 * (X 0 + X 1 : MvPolynomial (Fin 2) F) ^ m)
      = (m.choose (n - 1) : F) := by
    have hsplit : ehMon (n - 1) (n - 2) = Finsupp.single 1 1 + ehMon (n - 1) (n - 3) := by
      rw [ehMon, ehMon]
      have : (n - 2) = 1 + (n - 3) := by omega
      rw [this]
      rw [show Finsupp.single (1 : Fin 2) (1 + (n - 3))
          = Finsupp.single 1 1 + Finsupp.single 1 (n - 3) from (Finsupp.single_add _ _ _)]
      abel
    rw [hsplit, coeff_X_mul]
    rw [coeff_ehMon_add_pow (n - 1) (n - 3) m (by omega)]
  -- `X 0 * (X0+X1)^m` term
  have hX0 : coeff (ehMon (n - 1) (n - 2)) (X 0 * (X 0 + X 1 : MvPolynomial (Fin 2) F) ^ m)
      = (m.choose (n - 2) : F) := by
    have hsplit : ehMon (n - 1) (n - 2) = Finsupp.single 0 1 + ehMon (n - 2) (n - 2) := by
      rw [ehMon, ehMon]
      have : (n - 1) = 1 + (n - 2) := by omega
      rw [this]
      rw [show Finsupp.single (0 : Fin 2) (1 + (n - 2))
          = Finsupp.single 0 1 + Finsupp.single 0 (n - 2) from (Finsupp.single_add _ _ _)]
      abel
    rw [hsplit, coeff_X_mul]
    rw [coeff_ehMon_add_pow (n - 2) (n - 2) m (by omega)]
  rw [hX1, hX0]

/-- **Nonvanishing of the leading coefficient mod `p`.** With `m := 2(n-2)`, the integer
`C(m, n-2) - C(m, n-1)` (a Catalan number) is nonzero in `F` provided `m < ringChar F` and
`ringChar F` is prime. Equivalently the leading coefficient `C(m,n-1) - C(m,n-2)` is nonzero. -/
private lemma leading_coeff_ne_zero {p : ℕ} (hp : p.Prime) (hchar : ringChar F = p)
    {n : ℕ} (hn : 3 ≤ n) (hmp : 2 * (n - 2) < p) :
    (((2 * (n - 2)).choose (n - 1) : F) - ((2 * (n - 2)).choose (n - 2) : F)) ≠ 0 := by
  set m := 2 * (n - 2) with hm
  set A : ℕ := m.choose (n - 2) with hA
  set B : ℕ := m.choose (n - 1) with hB
  -- Recurrence: `B * (n-1) = A * (n-2)`  (since `m - (n-2) = n-2`).
  have hrec : B * (n - 1) = A * (n - 2) := by
    have h := Nat.choose_succ_right_eq m (n - 2)
    -- `m.choose ((n-2)+1) * ((n-2)+1) = m.choose (n-2) * (m - (n-2))`
    rw [show (n - 2) + 1 = n - 1 from by omega] at h
    rw [show m - (n - 2) = n - 2 from by omega] at h
    rw [hA, hB]; exact h
  -- `0 < A` since `n - 2 ≤ m`.
  have hApos : 0 < A := Nat.choose_pos (by omega)
  -- Hence `B ≤ A`: from `B*(n-1) = A*(n-2)` and `n-2 < n-1`, `B ≤ A`.
  have hle : B ≤ A := by
    by_contra hgt
    push_neg at hgt
    have h1 : A * (n - 2) < B * (n - 1) := by
      calc A * (n - 2) < A * (n - 1) := by
            have : n - 2 < n - 1 := by omega
            exact (Nat.mul_lt_mul_left hApos).mpr this
        _ ≤ B * (n - 1) := Nat.mul_le_mul_right _ (le_of_lt hgt)
    omega
  set D : ℕ := A - B with hD
  -- `(n-1) * D = A`.
  have hDmul : (n - 1) * D = A := by
    have hstep : (n - 1) * D = (n - 1) * A - (n - 1) * B := by rw [hD, Nat.mul_sub]
    have hnb : (n - 1) * B = (n - 2) * A := by rw [mul_comm, hrec, mul_comm]
    rw [hstep, hnb]
    have : (n - 1) * A - (n - 2) * A = ((n - 1) - (n - 2)) * A := (Nat.sub_mul _ _ _).symm
    rw [this, show (n - 1) - (n - 2) = 1 from by omega, one_mul]
  -- `p` is coprime to `A = C(m, n-2)` (since `m < p`), so `p ∤ (n-1)*D`, so `p ∤ D`.
  have hcop : p.Coprime A := hp.coprime_choose_of_lt hmp (by omega)
  have hpD : ¬ (p ∣ D) := by
    intro hpd
    have hpA : p ∣ A := hDmul ▸ hpd.mul_left _
    exact (hp.dvd_iff_not_coprime.mp hpA) hcop
  -- Translate to `F`: `(D : F) ≠ 0`.
  haveI : CharP F p := hchar ▸ ringChar.charP F
  have hDF : (D : F) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff F p D]; exact hpD
  -- the leading coefficient `B - A = -(A - B) = -(D : F)`.
  have hval : ((B : F) - (A : F)) = -(D : F) := by
    have : ((D : ℕ) : F) = (A : F) - (B : F) := by
      rw [hD]; push_cast [hle]; ring
    rw [this]; ring
  rw [hval]
  simpa using hDF

/-- Abbreviation for the "diagonal" variable `y = X₀ + X₁`. -/
private noncomputable def ehY : MvPolynomial (Fin 2) F := X 0 + X 1

private lemma totalDegree_ehY_pow_le (j : ℕ) :
    (ehY (F := F) ^ j).totalDegree ≤ j := by
  calc (ehY (F := F) ^ j).totalDegree ≤ j * (ehY (F := F)).totalDegree := totalDegree_pow _ _
    _ ≤ j * 1 := by
        gcongr
        calc (ehY (F := F)).totalDegree ≤ max (X 0 : MvPolynomial (Fin 2) F).totalDegree
              (X 1 : MvPolynomial (Fin 2) F).totalDegree := totalDegree_add _ _
          _ ≤ 1 := by simp [totalDegree_X]
    _ = j := by ring

/-- **Leading-part difference bound.** The product `∏_{c ∈ s} (y - C c)` differs from `y^{|s|}`
by a polynomial of total degree at most `|s| - 1`. -/
private lemma totalDegree_prod_sub_pow_le (s : Finset F) :
    ((∏ c ∈ s, (ehY (F := F) - C c)) - ehY ^ s.card).totalDegree ≤ s.card - 1 := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s has hind =>
    rw [Finset.prod_cons, Finset.card_cons]
    -- diff(insert) = (y - C a)*(∏_s - y^{|s|}) - C a · y^{|s|}
    have hdecomp :
        (ehY (F := F) - C a) * (∏ c ∈ s, (ehY - C c)) - ehY ^ (s.card + 1)
          = (ehY - C a) * ((∏ c ∈ s, (ehY - C c)) - ehY ^ s.card) - C a * ehY ^ s.card := by
      ring
    rw [hdecomp]
    refine (totalDegree_sub _ _).trans ?_
    apply max_le
    · -- (y - C a) * (∏ - y^{|s|})
      rcases s.eq_empty_or_nonempty with rfl | hne
      · simp
      · refine (totalDegree_mul _ _).trans ?_
        have h1 : (ehY (F := F) - C a).totalDegree ≤ 1 := by
          refine (totalDegree_sub _ _).trans ?_
          apply max_le
          · calc (ehY (F := F)).totalDegree
                  ≤ max (X 0 : MvPolynomial (Fin 2) F).totalDegree
                      (X 1 : MvPolynomial (Fin 2) F).totalDegree := totalDegree_add _ _
              _ ≤ 1 := by simp [totalDegree_X]
          · simp [totalDegree_C]
        have hscard : 1 ≤ s.card := hne.card_pos
        calc (ehY (F := F) - C a).totalDegree
              + ((∏ c ∈ s, (ehY - C c)) - ehY ^ s.card).totalDegree
            ≤ 1 + (s.card - 1) := by gcongr
          _ = s.card := by omega
    · -- C a · y^{|s|}
      refine (totalDegree_mul _ _).trans ?_
      rw [totalDegree_C, zero_add]
      exact totalDegree_ehY_pow_le _

/-- **The Erdős–Heilbronn polynomial** for a padded sumset `C'`. -/
private noncomputable def ehQ (Cset : Finset F) : MvPolynomial (Fin 2) F :=
  (X 1 - X 0) * ∏ c ∈ Cset, (X 0 + X 1 - C c)

/-- The coefficient of the top monomial `X₀^{n-1} X₁^{n-2}` in `ehQ C'` (with `|C'| = 2(n-2)`)
equals its coefficient in the leading part `(X₁ - X₀)(X₀ + X₁)^{2(n-2)}`. -/
private lemma coeff_ehQ_eq_leading {Cset : Finset F} {n : ℕ} (hn : 3 ≤ n)
    (hCcard : Cset.card = 2 * (n - 2)) :
    coeff (ehMon (n - 1) (n - 2)) (ehQ Cset)
      = coeff (ehMon (n - 1) (n - 2))
          ((X 1 - X 0 : MvPolynomial (Fin 2) F) * (X 0 + X 1) ^ (2 * (n - 2))) := by
  classical
  set m := 2 * (n - 2) with hm
  -- difference of the two polynomials = (X1 - X0) * (P' - y^m)
  set P' : MvPolynomial (Fin 2) F := ∏ c ∈ Cset, (X 0 + X 1 - C c) with hP'
  have hP'eq : P' = ∏ c ∈ Cset, (ehY - C c) := by rw [hP', ehY]
  -- the difference polynomial has total degree < m + 1 = degree of target monomial
  have hQdiff : ehQ Cset - (X 1 - X 0 : MvPolynomial (Fin 2) F) * (X 0 + X 1) ^ m
      = (X 1 - X 0) * (P' - ehY ^ m) := by
    rw [ehQ, ehY, ← hP']
    ring
  -- total degree of the difference < m + 1
  have htd : (ehQ Cset - (X 1 - X 0 : MvPolynomial (Fin 2) F) * (X 0 + X 1) ^ m).totalDegree
      < m + 1 := by
    rw [hQdiff]
    refine lt_of_le_of_lt (totalDegree_mul _ _) ?_
    have h1 : (X 1 - X 0 : MvPolynomial (Fin 2) F).totalDegree ≤ 1 := by
      refine (totalDegree_sub _ _).trans ?_
      apply max_le <;> simp [totalDegree_X]
    have h2 : (P' - ehY ^ m).totalDegree ≤ m - 1 := by
      rw [hP'eq, ← hCcard]
      exact totalDegree_prod_sub_pow_le Cset
    have hmpos : 1 ≤ m := by omega
    calc (X 1 - X 0 : MvPolynomial (Fin 2) F).totalDegree + (P' - ehY ^ m).totalDegree
        ≤ 1 + (m - 1) := by gcongr
      _ = m := by omega
      _ < m + 1 := by omega
  -- target monomial has degree m + 1
  have htdeg : ∑ i ∈ (ehMon (n - 1) (n - 2)).support, (ehMon (n - 1) (n - 2)) i = m + 1 := by
    have hsub : (ehMon (n - 1) (n - 2)).support ⊆ (Finset.univ : Finset (Fin 2)) :=
      Finset.subset_univ _
    rw [Finset.sum_subset hsub (fun i _ hi => Finsupp.notMem_support_iff.mp hi)]
    rw [Fin.sum_univ_two, ehMon_apply_zero, ehMon_apply_one]
    omega
  -- conclude coeff of difference is 0
  have hcoeff0 : coeff (ehMon (n - 1) (n - 2))
      (ehQ Cset - (X 1 - X 0 : MvPolynomial (Fin 2) F) * (X 0 + X 1) ^ m) = 0 := by
    apply coeff_eq_zero_of_totalDegree_lt
    rw [htdeg]; exact htd
  rw [coeff_sub, sub_eq_zero] at hcoeff0
  rw [hcoeff0]

end ErdosHeilbronn

end MvPolynomial
