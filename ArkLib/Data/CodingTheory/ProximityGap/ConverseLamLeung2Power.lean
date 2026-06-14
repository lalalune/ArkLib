/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Converse Lam–Leung direction for 2-power order (#407)

This strengthens `VanishingRootSumHeightGate.lean` (namespace
`ArkLib.ProximityGap.RouVanishingCount`), which proves the EASY direction
`sum_eq_zero_of_antipodal` (a finite antipodal set of `n`-th roots sums to `0` in char `≠ 2`).
Here we prove the CONVERSE for **2-power order** over a **char-0 field**:

> If `ζ` is a primitive `2^a`-th root of unity (`a ≥ 1`) and a subset `S ⊆ {0,…,2^a-1}` of
> exponents has vanishing root-sum `∑_{i∈S} ζ^i = 0`, then `S` is **antipodal**:
> `j ∈ S ↔ j + 2^{a-1} ∈ S` for every `j < 2^{a-1}`.

Together with the easy direction this characterizes vanishing sums of distinct `2^a`-th roots of
unity in char 0 as exactly the antipodal (disjoint-union-of-negation-pairs) sets — the
char-0 content of `NoSpuriousVanishing` for `n = 2^a`.

## Why 2-power order is special (the Mathlib-free mechanism)

`Φ_{2^a}(X) = X^{2^{a-1}} + 1`, so `ζ^{2^{a-1}} = -1` (`ζ^{n/2}` is a primitive 2nd root of unity).
Splitting exponents into the low half (`< 2^{a-1}`) and high half (`≥ 2^{a-1}`) and rewriting
`ζ^{j + 2^{a-1}} = -ζ^j` collapses the sum onto `{1, ζ, …, ζ^{2^{a-1}-1}}`.  Those powers are
linearly independent over `ℤ` because `(minpoly ℤ ζ).natDegree = φ(2^a) = 2^{a-1}` (char-0 field:
`cyclotomic (2^a) ℤ = minpoly ℤ ζ`), so each integer coefficient `[j∈S] - [j+2^{a-1}∈S]` vanishes
— exactly antipodality.  No Lam–Leung machinery, just minimal-polynomial degree.
-/

open Finset Polynomial

namespace ArkLib.ProximityGap.RouVanishingCount

variable {F : Type*} [Field F] [CharZero F]

/-- **Linear independence of low-half powers over `ℤ`.** For `ζ` a primitive `2^a`-th root of
unity over a char-0 field (`a ≥ 1`), any *integer* combination `∑_{j < 2^{a-1}} c j • ζ^j = 0`
forces every coefficient `c j` (`j < 2^{a-1}`) to vanish.

Proof: `P = ∑_j C (c j) X^j ∈ ℤ[X]` has `aeval ζ P = 0` and `degree P < 2^{a-1}`, while
`degree (minpoly ℤ ζ) = degree (cyclotomic (2^a) ℤ) = φ(2^a) = 2^{a-1}` (over a char-0 field).
So `minpoly.IsIntegrallyClosed.degree_le_of_ne_zero` (over the integrally-closed `ℤ`) forces
`P = 0`, hence every coefficient — which on `range (2^{a-1})` is exactly `c j` — vanishes. -/
theorem lowHalf_powers_linearIndependent {a : ℕ} (ha : 1 ≤ a) {ζ : F}
    (hζ : IsPrimitiveRoot ζ (2 ^ a)) (c : ℕ → ℤ)
    (hsum : ∑ j ∈ range (2 ^ (a - 1)), (c j : F) * ζ ^ j = 0) :
    ∀ j ∈ range (2 ^ (a - 1)), c j = 0 := by
  classical
  have hpos : 0 < 2 ^ a := pow_pos (by norm_num) a
  have hζint : IsIntegral ℤ ζ := hζ.isIntegral hpos
  have hminpoly : cyclotomic (2 ^ a) ℤ = minpoly ℤ ζ := cyclotomic_eq_minpoly hζ hpos
  have hdeg : (minpoly ℤ ζ).natDegree = 2 ^ (a - 1) := by
    rw [← hminpoly, natDegree_cyclotomic, Nat.totient_prime_pow Nat.prime_two ha]
    norm_num
  set d : ℕ := 2 ^ (a - 1) with hd
  set P : ℤ[X] := ∑ j ∈ range d, C (c j) * X ^ j with hP
  have haeval : aeval ζ P = 0 := by
    rw [hP, map_sum, ← hsum]
    apply Finset.sum_congr rfl
    intro j _
    rw [map_mul, aeval_C, aeval_X_pow, algebraMap_int_eq, eq_intCast]
  have hdpos : 0 < d := pow_pos (by norm_num) (a - 1)
  have hPdeg : P.degree < (d : ℕ) := by
    rw [hP]
    refine lt_of_le_of_lt (degree_sum_le _ _) ?_
    refine (Finset.sup_lt_iff (WithBot.bot_lt_coe d)).mpr ?_
    intro j hj
    calc (C (c j) * X ^ j).degree ≤ (C (c j)).degree + (X ^ j).degree := degree_mul_le _ _
      _ ≤ 0 + j := by
          gcongr
          · exact degree_C_le
          · rw [degree_X_pow]
      _ = (j : WithBot ℕ) := by rw [zero_add]
      _ < (d : ℕ) := by exact_mod_cast Finset.mem_range.mp hj
  have hP0 : P = 0 := by
    by_contra hPne
    have hle : (minpoly ℤ ζ).degree ≤ P.degree :=
      minpoly.IsIntegrallyClosed.degree_le_of_ne_zero hPne haeval
    rw [degree_eq_natDegree (minpoly.ne_zero hζint), hdeg] at hle
    exact absurd (lt_of_le_of_lt hle hPdeg) (lt_irrefl _)
  intro j hj
  have hcoeff : P.coeff j = c j := by
    rw [hP, finset_sum_coeff]
    simp only [coeff_C_mul, coeff_X_pow]
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hbj; rw [if_neg (by omega)]; ring
    · intro hjmem; exact absurd hj hjmem
  rw [← hcoeff, hP0, coeff_zero]

/-- A finite set `S ⊆ {0,…,2^a-1}` of exponents is **antipodal** when `j ∈ S ↔ j + 2^{a-1} ∈ S`
for every low-half exponent `j < 2^{a-1}`.  (Equivalently `S` is a disjoint union of negation
pairs `{ζ^j, ζ^{j+2^{a-1}}}`, recalling `ζ^{2^{a-1}} = -1`.)  This is the exponent-indexed form of
the `Antipodal` predicate of `VanishingRootSumHeightGate.lean`. -/
def ExponentAntipodal (a : ℕ) (S : Finset ℕ) : Prop :=
  ∀ j < 2 ^ (a - 1), (j ∈ S ↔ j + 2 ^ (a - 1) ∈ S)

/-- **Converse Lam–Leung for 2-power order.** If `ζ` is a primitive `2^a`-th root of unity over a
char-0 field (`a ≥ 1`), and a subset `S ⊆ {0,…,2^a-1}` of exponents has vanishing root-sum
`∑_{i∈S} ζ^i = 0`, then `S` is antipodal: `j ∈ S ↔ j + 2^{a-1} ∈ S` for all `j < 2^{a-1}`.

This is the converse of the easy `sum_eq_zero_of_antipodal` direction; together they characterize
vanishing sums of distinct `2^a`-th roots of unity in char 0 as exactly the antipodal sets. -/
theorem zero_sum_imp_antipodal {a : ℕ} (ha : 1 ≤ a) {ζ : F}
    (hζ : IsPrimitiveRoot ζ (2 ^ a)) {S : Finset ℕ} (hS : S ⊆ range (2 ^ a))
    (hsum : ∑ i ∈ S, ζ ^ i = 0) : ExponentAntipodal a S := by
  classical
  set d : ℕ := 2 ^ (a - 1) with hd
  -- `2^a = d + d` (i.e. `n = 2·(n/2)`).
  have hsplit : (2 : ℕ) ^ a = d + d := by
    rw [hd, ← two_mul, ← pow_succ']
    congr 1; omega
  -- `ζ^d = -1` (it is a primitive 2nd root of unity).
  have hhalf : ζ ^ d = -1 := by
    have hp2 : IsPrimitiveRoot (ζ ^ d) 2 := by
      refine hζ.pow (by positivity) ?_
      rw [hsplit, ← two_mul]; ring
    exact hp2.eq_neg_one_of_two_right
  have hSlt : ∀ i ∈ S, i < d + d := fun i hi => by
    have := hS hi; rw [hsplit] at this; exact mem_range.mp this
  -- Integer coefficient on each low index `j`: `[j∈S] - [j+d∈S]`.
  set c : ℕ → ℤ := fun j => (if j ∈ S then 1 else 0) - (if j + d ∈ S then 1 else 0) with hc
  -- The vanishing sum, re-collected on `{ζ^0,…,ζ^{d-1}}` using `ζ^{j+d} = -ζ^j`.
  have hcollect : ∑ j ∈ range d, (c j : F) * ζ ^ j = 0 := by
    have hdistrib : ∀ j ∈ range d, (c j : F) * ζ ^ j
        = (if j ∈ S then ζ ^ j else 0) - (if j + d ∈ S then ζ ^ j else 0) := by
      intro j _
      rw [hc]; push_cast
      by_cases h1 : j ∈ S <;> by_cases h2 : j + d ∈ S <;> simp [h1, h2]
    rw [Finset.sum_congr rfl hdistrib, Finset.sum_sub_distrib]
    -- low half
    have hA : ∑ j ∈ range d, (if j ∈ S then ζ ^ j else 0) = ∑ i ∈ S.filter (· < d), ζ ^ i := by
      rw [← Finset.sum_filter]
      apply Finset.sum_congr _ (fun _ _ => rfl)
      ext i; simp only [mem_filter, mem_range]; tauto
    -- high half, reindexed `j ↦ j + d` with `ζ^j = -ζ^{j+d}`
    have hB : ∑ j ∈ range d, (if j + d ∈ S then ζ ^ j else 0)
        = - ∑ i ∈ S.filter (¬ · < d), ζ ^ i := by
      have step1 : ∑ j ∈ range d, (if j + d ∈ S then ζ ^ j else 0)
          = ∑ j ∈ (range d).filter (fun j => j + d ∈ S), ζ ^ j := (Finset.sum_filter _ _).symm
      rw [step1, ← Finset.sum_neg_distrib]
      refine Finset.sum_bij'
        (i := fun j _ => j + d) (j := fun i _ => i - d) ?_ ?_ ?_ ?_ ?_
      · intro j hj; simp only [mem_filter, mem_range] at hj ⊢; exact ⟨hj.2, by omega⟩
      · intro i hi; simp only [mem_filter, mem_range] at hi ⊢
        have hib : i < d + d := hSlt i hi.1
        have h : i - d + d = i := by omega
        rw [h]; exact ⟨by omega, hi.1⟩
      · intro j _; dsimp only; omega
      · intro i hi; simp only [mem_filter] at hi
        have hib : i < d + d := hSlt i hi.1; dsimp only; omega
      · intro j hj; simp only [mem_filter, mem_range] at hj
        rw [pow_add, hhalf]; ring
    rw [hA, hB, sub_neg_eq_add, Finset.sum_filter_add_sum_filter_not, hsum]
  -- Apply the linear-independence lemma: every `c j = 0`, i.e. antipodality.
  have hvanish : ∀ j ∈ range d, c j = 0 := lowHalf_powers_linearIndependent ha hζ c hcollect
  intro j hj
  have hj0 := hvanish j (Finset.mem_range.mpr hj)
  rw [hc] at hj0; simp only at hj0
  by_cases hjS : j ∈ S <;> by_cases hjdS : j + d ∈ S <;> simp_all

end ArkLib.ProximityGap.RouVanishingCount

#print axioms ArkLib.ProximityGap.RouVanishingCount.lowHalf_powers_linearIndependent
#print axioms ArkLib.ProximityGap.RouVanishingCount.zero_sum_imp_antipodal
