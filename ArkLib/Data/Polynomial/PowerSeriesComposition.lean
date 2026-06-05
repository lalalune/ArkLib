/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Algebra.Polynomial.Basic

/-!
# Power-series composition coefficients (BCIKS20 App. A.4 — WAVE 3 foundation)
-/

namespace ArkLib.PowerSeriesComposition

open Finset BigOperators PowerSeries

section Combinatorics

variable {M : Type*} [CommMonoid M]

/-- The **multiset of values** of a weak composition `l` over the index set `s`. -/
def valueMultiset {ι : Type*} (s : Finset ι) (l : ι →₀ ℕ) : Multiset ℕ :=
  s.val.map (fun i => l i)

@[simp]
theorem valueMultiset_card {ι : Type*} (s : Finset ι) (l : ι →₀ ℕ) :
    (valueMultiset s l).card = s.card := by
  rw [valueMultiset, Multiset.card_map, Finset.card_def]

theorem valueMultiset_sum {ι : Type*} (s : Finset ι) (l : ι →₀ ℕ) :
    (valueMultiset s l).sum = ∑ i ∈ s, l i := by
  rw [valueMultiset, Finset.sum]

/-- **Index-set → value-multiset.**  The product `∏_{i∈s} b (l i)` of a family `b : ℕ → M`
evaluated at the *values* `l i` equals the product over the **multiset of values**
`valueMultiset s l` after applying `b`.  This is the rewriting that turns an index-keyed
product into a value-keyed one, so that two compositions sharing the same bag of values
produce the same product — the prerequisite for the multiplicity grouping below. -/
theorem prod_eq_multiset_value_prod {ι : Type*} (s : Finset ι) (l : ι →₀ ℕ) (b : ℕ → M) :
    ∏ i ∈ s, b (l i) = ((valueMultiset s l).map b).prod := by
  rw [valueMultiset, Multiset.map_map, Finset.prod]
  rfl

/-- **L4 — FOUNDATIONAL: the multiplicity-grouping identity.**

The order-`t` weak-composition sum
`∑_{l ∈ finsuppAntidiag s t} ∏_{i∈s} b (l i)` — exactly the shape produced by mathlib's
`PowerSeries.coeff_pow` / `coeff_prod` — regroups, *by the multiset of part-values*, into a
sum indexed by the distinct value-multisets `m` (each a `Multiset ℕ` of `card = #s`,
`sum = t`, realized by some composition), weighted by the number of compositions realizing
`m`:

`∑_{l} ∏_{i∈s} b (l i) = ∑_{m ∈ image valueMultiset} (#fiber of m) • ((m.map b).prod)`.

This is the multivariate-Faà-di-Bruno combinatorial core (BCIKS20 A.4): the fiber
cardinality `#{l | valueMultiset s l = m}` is the multinomial counting how many weak
compositions share the bag `m`, and `(m.map b).prod = ∏_l (b l)^{count l m}` is the
partition-product `∏ β^λ`.  The products run in the multiplicative monoid of `R` while the
outer sum / `•` run in its additive monoid (so the natural home is a `CommSemiring`, which
is also where `coeff_pow` lives).  It is pure semiring combinatorics — no dependence on
`𝕃`/`R`/`H` — so it compiles fast and (witnessed by `compositionSum_example`) cannot be
vacuous.  Everything downstream (`coeff_pow_eq_valueMultisetSum`, and the staged
`compositionSum_eq_partitionSum`) reuses it. -/
theorem compositionSum_eq_valueMultisetSum {ι : Type*} [DecidableEq ι]
    {R : Type*} [CommSemiring R] (s : Finset ι) (t : ℕ) (b : ℕ → R) :
    ∑ l ∈ finsuppAntidiag s t, ∏ i ∈ s, b (l i)
      = ∑ m ∈ (finsuppAntidiag s t).image (valueMultiset s),
          (#{l ∈ finsuppAntidiag s t | valueMultiset s l = m}) • ((m.map b).prod) := by
  classical
  -- Each summand depends on `l` only through `valueMultiset s l`, so this is exactly the
  -- fiber-cardinality grouping `Finset.sum_comp`.
  have hsummand : ∀ l : ι →₀ ℕ, (∏ i ∈ s, b (l i)) = ((valueMultiset s l).map b).prod :=
    fun l => prod_eq_multiset_value_prod s l b
  simp_rw [hsummand]
  exact Finset.sum_comp (fun m => (m.map b).prod) (valueMultiset s)

/-- The concrete family `b n := 2 ^ n : ℕ → ℕ` used to witness non-vacuity of L4. -/
private def bWitness : ℕ → ℕ := fun n => 2 ^ n

/-- **Non-vacuity witness for L4 (composition side).**  At `s = range 2`, `t = 2`, with
`b n := 2 ^ n`, the three weak compositions `(2,0),(0,2),(1,1)` each contribute
`2^{l₀}·2^{l₁} = 2^2 = 4`, so the left-hand (ungrouped) sum is `4 + 4 + 4 = 12 ≠ 0`. -/
example : (∑ l ∈ finsuppAntidiag (range 2) 2, ∏ i ∈ range 2, bWitness (l i)) = 12 := by decide

/-- **Non-vacuity witness for L4 (grouped side).**  The same data, grouped by value-multiset:
`{2,0}` has fiber size `2` and product `2^2·2^0 = 4` (contributing `2 • 4 = 8`); `{1,1}` has
fiber size `1` and product `2^1·2^1 = 4` (contributing `1 • 4 = 4`); total `12`.  So the
grouping genuinely splits into two distinct multisets with *different* multinomial weights —
neither an empty sum nor a degenerate `0 = 0`. -/
example :
    (∑ m ∈ (finsuppAntidiag (range 2) 2).image (valueMultiset (range 2)),
        (#{l ∈ finsuppAntidiag (range 2) 2 | valueMultiset (range 2) l = m})
          • ((m.map bWitness).prod)) = 12 := by decide

/-- The two sides of L4 visibly agree, and both equal the nonzero value `12`, at the concrete
instance `s = range 2`, `t = 2`, `b n = 2^n`: a self-check that
`compositionSum_eq_valueMultisetSum` is not vacuous. -/
theorem compositionSum_example :
    (∑ l ∈ finsuppAntidiag (range 2) 2, ∏ i ∈ range 2, bWitness (l i))
      = ∑ m ∈ (finsuppAntidiag (range 2) 2).image (valueMultiset (range 2)),
          (#{l ∈ finsuppAntidiag (range 2) 2 | valueMultiset (range 2) l = m})
            • ((m.map bWitness).prod) :=
  compositionSum_eq_valueMultisetSum (range 2) 2 bWitness

end Combinatorics

end ArkLib.PowerSeriesComposition
