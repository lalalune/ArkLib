/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.RingTheory.Norm.Basic
import Mathlib.Tactic

/-!
# The half-sum cyclotomic norm closed form (#407 — Half-Sum Lemma, GRIND T5)

The Half-Sum Lemma (issue #407, the irreducible non-BGK residual of the Proximity Prize)
asks for the structure of antipodal-free vanishing sums of `2^μ`-th roots of unity in the
split regime `p ≡ 1 mod 2^μ`. The candidate-bad-prime method reduces the per-`n` statement
to the algebraic norm `N_{ℚ(ζ_n)/ℚ}(∑_{u ∈ U} u)` of subset sums `U ⊆ μ_n`: a bad prime
must divide one of these norms.

The **base point of that ledger** — the "all-ones" half-sum
`α = 1 + ζ + ⋯ + ζ^{n/2-1}` over a primitive `n = 2^{m+1}`-th root of unity — has an exact
closed form. This file proves it,
char-`0`, axiom-clean, uniformly in `m`:

> **`norm_halfSum_eq` :  `N_{K/ℚ}(∑_{i < 2^m} ζ^i) = 2^{2^m - 1}`**

(for any cyclotomic extension `K ⊆ L` of conductor `2^{m+1}`, `m ≥ 1`). Numerically:
`n = 8 → 2³ = 8`, `n = 16 → 2⁷ = 128`, `n = 32 → 2¹⁵ = 32768`, `n = 64 → 2³¹` —
matching the probe `scripts/probes/probe_407_halfsum_*` exactly.

## Mechanism (the proof is short and structural)

Since `ζ^{2^m} = -1` (the defining negation of the prime-2 tower, `LamLeungTwoPow`), the
geometric series telescopes:
`(ζ - 1)·(∑_{i < 2^m} ζ^i) = ζ^{2^m} - 1 = -2`.
Taking the multiplicative `K`-norm and using two Mathlib facts —
`N(ζ - 1) = (2^{m+1}).minFac = 2` (`IsPrimitiveRoot.sub_one_norm_isPrimePow`) and
`N(-2) = (-2)^{φ(2^{m+1})} = (-2)^{2^m} = 2^{2^m}` (`Algebra.norm_algebraMap` +
`IsCyclotomicExtension.finrank`) — gives `2·N(α) = 2^{2^m}`, hence `N(α) = 2^{2^m - 1}`.

## Why this matters for the prize

This is the **clean, uniform-in-n sub-result** the GRIND T5 thread asks for: the all-ones
half-sum has norm a pure power of `2`, so it can **never** be divisible by an odd prime
`p ≡ 1 mod n` — the base case of "no antipodal-free subset of the full half-coset structure
contributes a bad prime". It pins the simplest member of the candidate-norm ledger
unconditionally and uniformly, removing it from the finite enumeration at every level `n`. It
does NOT resolve the full Half-Sum Lemma (general antipodal-free `U` can have norms with
genuine odd-prime factors — e.g. `N = 9` at `n = 8`, `N = 17, 97, …` at `n = 16`; those primes
`≡ 1 mod n` are the open candidates), and it does not touch the BGK character-sum wall: it is
a pure cyclotomic-arithmetic identity.

Axiom target: `[propext, Classical.choice, Quot.sound]`.
-/

open Polynomial Finset

namespace ArkLib.ProximityGap.HalfSumNorm

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- In a cyclotomic extension of conductor `2^{m+1}`, the base field has `(2 : K) ≠ 0`
(the conductor `2^{m+1}` is invertible, so `2` is). -/
theorem two_ne_zero_of_cyclotomic {m : ℕ} [NeZero ((2:ℕ) ^ (m + 1))]
    [IsCyclotomicExtension {(2:ℕ) ^ (m + 1)} K L] : (2 : K) ≠ 0 := by
  haveI hnz : NeZero (((2:ℕ) ^ (m + 1) : ℕ) : K) :=
    IsCyclotomicExtension.neZero' ((2:ℕ) ^ (m + 1)) K L
  have h0 : (((2:ℕ) ^ (m + 1) : ℕ) : K) ≠ 0 := hnz.ne
  rw [Nat.cast_pow, Nat.cast_ofNat] at h0
  exact fun h2 => h0 (by rw [h2]; ring)

/-- A primitive `2^{m+1}`-th root of unity has `ζ^{2^m} = -1` (the prime-2 negation). -/
theorem pow_half_eq_neg_one {m : ℕ} {ζ : L} (hζ : IsPrimitiveRoot ζ (2 ^ (m + 1))) :
    ζ ^ (2 ^ m) = -1 := by
  have hsq : (ζ ^ 2 ^ m) ^ 2 = 1 := by
    rw [← pow_mul, show 2 ^ m * 2 = 2 ^ (m + 1) by ring]; exact hζ.pow_eq_one
  have hne : ζ ^ 2 ^ m ≠ 1 :=
    hζ.pow_ne_one_of_pos_of_lt (Nat.two_pow_pos m).ne'
      (Nat.pow_lt_pow_right (by norm_num) (by omega))
  have hfac : (ζ ^ 2 ^ m - 1) * (ζ ^ 2 ^ m + 1) = 0 := by ring_nf; linear_combination hsq
  rcases mul_eq_zero.mp hfac with h | h
  · exact absurd (by linear_combination h) hne
  · linear_combination h

/-- **The telescoping identity.** Over a primitive `2^{m+1}`-th root, the all-ones half-sum
`∑_{i < 2^m} ζ^i` times `(ζ - 1)` collapses to `-2`. -/
theorem halfSum_mul_sub_one {m : ℕ} {ζ : L} (hζ : IsPrimitiveRoot ζ (2 ^ (m + 1))) :
    (ζ - 1) * (∑ i ∈ range (2 ^ m), ζ ^ i) = -2 := by
  rw [mul_geom_sum, pow_half_eq_neg_one hζ]; ring

/-- `N_{K/ℚ}(ζ - 1) = 2` for `ζ` a primitive `2^{m+1}`-th root (`m ≥ 1`). The `minFac` of a
2-power prime power is `2`. -/
theorem norm_sub_one {m : ℕ} (hm : 1 ≤ m) {ζ : L} [NeZero ((2:ℕ) ^ (m + 1))]
    (hζ : IsPrimitiveRoot ζ ((2:ℕ) ^ (m + 1)))
    [IsCyclotomicExtension {(2:ℕ) ^ (m + 1)} K L]
    (hirr : Irreducible (cyclotomic ((2:ℕ) ^ (m + 1)) K)) :
    Algebra.norm K (ζ - 1) = (2 : K) := by
  have hpp : IsPrimePow ((2:ℕ) ^ (m + 1)) := ⟨2, m + 1, Nat.prime_two.prime, by omega, rfl⟩
  have hne2 : (2 : ℕ) ^ (m + 1) ≠ 2 := by
    have : (2:ℕ) ^ (m + 1) ≥ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hmf : Nat.minFac ((2:ℕ) ^ (m + 1)) = 2 := by
    rw [Nat.minFac_eq, if_pos (dvd_pow_self 2 (Nat.succ_ne_zero m))]
  rw [hζ.sub_one_norm_isPrimePow hpp hirr hne2, hmf]; norm_num

/-- `N_{K/ℚ}(-2) = (-2)^{φ(2^{m+1})} = (-2)^{2^m} = 2^{2^m}` (`2^m` is even for `m ≥ 1`). -/
theorem norm_neg_two {m : ℕ} (hm : 1 ≤ m) [NeZero ((2:ℕ) ^ (m + 1))]
    [IsCyclotomicExtension {(2:ℕ) ^ (m + 1)} K L]
    (hirr : Irreducible (cyclotomic ((2:ℕ) ^ (m + 1)) K)) :
    Algebra.norm K (-2 : L) = (2 : K) ^ (2 ^ m) := by
  have h1 : (-2 : L) = algebraMap K L (-2 : K) := by rw [map_neg, map_ofNat]
  rw [h1, Algebra.norm_algebraMap, IsCyclotomicExtension.finrank L hirr,
      Nat.totient_prime_pow_succ Nat.prime_two]
  -- exponent simplifies: 2^m * (2-1) = 2^m
  have hexp : 2 ^ m * (2 - 1) = 2 ^ m := by omega
  rw [hexp]
  -- (-2)^(2^m) = 2^(2^m) since 2^m is even
  have heven : Even (2 ^ m) := (Nat.even_pow.mpr ⟨even_two, by omega⟩)
  rw [neg_pow, heven.neg_one_pow, one_mul]

/-- **The half-sum norm closed form.** For a cyclotomic extension of conductor `n = 2^{m+1}`
(`m ≥ 1`) and `ζ` a primitive `n`-th root of unity,
`N_{K/ℚ}(1 + ζ + ⋯ + ζ^{n/2 - 1}) = 2^{n/2 - 1}`.

Verified numerically: `n = 8 → 8`, `n = 16 → 128`, `n = 32 → 32768`, `n = 64 → 2^31`. -/
theorem norm_halfSum_eq {m : ℕ} (hm : 1 ≤ m) {ζ : L} [NeZero ((2:ℕ) ^ (m + 1))]
    (hζ : IsPrimitiveRoot ζ ((2:ℕ) ^ (m + 1)))
    [IsCyclotomicExtension {(2:ℕ) ^ (m + 1)} K L]
    (hirr : Irreducible (cyclotomic ((2:ℕ) ^ (m + 1)) K)) :
    Algebra.norm K (∑ i ∈ range (2 ^ m), ζ ^ i) = (2 : K) ^ (2 ^ m - 1) := by
  -- N(ζ - 1) * N(α) = N((ζ-1)*α) = N(-2) = 2^(2^m)
  have hmul : Algebra.norm K (ζ - 1) * Algebra.norm K (∑ i ∈ range (2 ^ m), ζ ^ i)
      = (2 : K) ^ (2 ^ m) := by
    rw [← map_mul, halfSum_mul_sub_one hζ, norm_neg_two hm hirr]
  rw [norm_sub_one hm hζ hirr] at hmul
  -- 2 * N(α) = 2^(2^m) = 2 * 2^(2^m - 1)
  have hpow : (2 : K) ^ (2 ^ m) = 2 * (2 : K) ^ (2 ^ m - 1) := by
    rw [← pow_succ']
    congr 1
    have : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    omega
  rw [hpow] at hmul
  exact mul_left_cancel₀ (two_ne_zero_of_cyclotomic (m := m) (L := L)) hmul

end ArkLib.ProximityGap.HalfSumNorm
#print axioms ArkLib.ProximityGap.HalfSumNorm.norm_halfSum_eq
