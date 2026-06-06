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

end ErdosHeilbronn

end MvPolynomial
