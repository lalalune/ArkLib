/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.PairSumRigidityModP

/-!
# The two-plus-antipodal chord law: the dominant slanted family in closed form

Campaign #357, the first closed sub-family of the slanted stratum. The corrected char-0
census (probe `probe_slanted_char0_census.py`) decomposes into the `(d, d, n/2)` family —
*two pairs of one difference class plus one antipodal pair* — and a sporadic
all-distinct-difference layer; the family accounts for **all** slanted circuits at
`n = 8` (16 of 16) and the `18×16 = 288` part at `n = 16`. This file proves the family's
law:

* `chord_det_factor` — **the determinant factorization**: for pair-points
  `{i, i+d}, {j, j+d}, {k, k+2^(m−1)}` of `Γ_n`, the collinearity determinant of the
  pencil criterion factors **exactly** as

    `det = (ζ^j − ζ^i) · (1 + ζ^d) · (ζ^(i+j+d) − ζ^(2k))`.

  Geometry: the chord of the parabola `e² = c_d·m` through the two class-`d` points
  crosses the degenerate vertical line `e = 0` at exactly `m = −ζ^(i+j+d)`; the first two
  factors are the nondegeneracy of the chord.
* `two_plus_antipodal_collinear_iff` — **the chord law**: for `d` non-antipodal and
  `ζ^i ≠ ζ^j`, the triple is collinear **iff** `2k ≡ i + j + d (mod 2^m)` — a single
  congruence, uniform in the scale, over **any** field with a primitive `2^m`-th root
  (no characteristic hypothesis, no threshold: the law is exact algebra).

The horizontal degenerations (`j ≡ i + 2^(m−1)`, where all three products coincide) are
*included* in the law on both sides; the slanted/horizontal split is downstream
classification. Probe: exhaustive at `n = 8, 16, 32` (10⁶ tuples) + the factorization
identity verified exactly mod several primes — ALL PASS.

## Honest scope

This closes the supply law of the `(d, d, n/2)` family; the family's *census count* per
scale (a counting corollary over the congruence) and the sporadic all-distinct-difference
layer (8 orbits × 32 at `n = 16`) remain the open part of the slanted classification.

All results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References

* Issue #357 (round 9/10 stratification; the census-correction comment);
  `MCAParabolaStratification.lean` (the parabola frame, the negative law),
  `MCADualPencilLaw.dependent_iff_collinear` (the consumer interface).
* Probe: `scripts/probes/probe_two_plus_antipodal_chord_law.py`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial Finset

namespace ArkLib.ProximityGap.TwoPlusAntipodalChordLaw

open ArkLib.ProximityGap.PairSumRigidityModP

variable {L : Type*} [Field L]

/-- Exponent reduction at a `2^m`-th root of unity. -/
theorem pow_reduce {m : ℕ} {ζ : L} (hζ : IsPrimitiveRoot ζ (2 ^ m)) (A : ℕ) :
    ζ ^ A = ζ ^ (A % 2 ^ m) := by
  conv_lhs => rw [← Nat.div_add_mod A (2 ^ m)]
  rw [pow_add, pow_mul, hζ.pow_eq_one, one_pow, one_mul]

/-- **The determinant factorization.** For the pair-points
`({i, i+d}, {j, j+d}, {k, k+2^(m−1)})` of `Γ_n` — coordinates
`(e, m) = (ζ^x + ζ^y, ζ^x·ζ^y)` — the collinearity determinant of the pencil criterion
factors as `(ζ^j − ζ^i)·(1 + ζ^d)·(ζ^(i+j+d) − ζ^(2k))`. -/
theorem chord_det_factor {m : ℕ} (hm : 1 ≤ m) {ζ : L}
    (hζ : IsPrimitiveRoot ζ (2 ^ m)) (i j k d : ℕ) :
    (ζ ^ j + ζ ^ (j + d) - (ζ ^ i + ζ ^ (i + d)))
        * (ζ ^ k * ζ ^ (k + 2 ^ (m - 1)) - ζ ^ i * ζ ^ (i + d))
      - (ζ ^ j * ζ ^ (j + d) - ζ ^ i * ζ ^ (i + d))
        * (ζ ^ k + ζ ^ (k + 2 ^ (m - 1)) - (ζ ^ i + ζ ^ (i + d)))
      = (ζ ^ j - ζ ^ i) * (1 + ζ ^ d) * (ζ ^ (i + j + d) - ζ ^ (2 * k)) := by
  have hkh : ζ ^ (k + 2 ^ (m - 1)) = -(ζ ^ k) := by
    rw [pow_add, pow_half_eq_neg_one_field hm hζ, mul_neg_one]
  rw [hkh]
  ring

/-- **THE TWO-PLUS-ANTIPODAL CHORD LAW.** For a non-antipodal difference class `d`
(`d % 2^m ≠ 2^(m−1)`) and distinct class-`d` pairs (`ζ^i ≠ ζ^j`): the triple
`({i, i+d}, {j, j+d}, {k, k+2^(m−1)})` satisfies the pencil collinearity equation **iff**
`2k ≡ i + j + d (mod 2^m)` — the chord of the `d`-parabola through the two points meets
the degenerate vertical line exactly at the antipodal pair-point of `m`-value
`−ζ^(i+j+d)`. -/
theorem two_plus_antipodal_collinear_iff {m : ℕ} (hm : 1 ≤ m) {ζ : L}
    (hζ : IsPrimitiveRoot ζ (2 ^ m)) {i j k d : ℕ}
    (hd : d % 2 ^ m ≠ 2 ^ (m - 1)) (hij : ζ ^ i ≠ ζ ^ j) :
    ((ζ ^ j + ζ ^ (j + d) - (ζ ^ i + ζ ^ (i + d)))
        * (ζ ^ k * ζ ^ (k + 2 ^ (m - 1)) - ζ ^ i * ζ ^ (i + d))
      = (ζ ^ j * ζ ^ (j + d) - ζ ^ i * ζ ^ (i + d))
        * (ζ ^ k + ζ ^ (k + 2 ^ (m - 1)) - (ζ ^ i + ζ ^ (i + d))))
      ↔ (2 * k) % 2 ^ m = (i + j + d) % 2 ^ m := by
  have hsplit : 2 ^ (m - 1) + 2 ^ (m - 1) = 2 ^ m := by
    have h := pow_succ 2 (m - 1)
    rw [Nat.sub_add_cancel hm] at h
    omega
  have hhalf_lt : 2 ^ (m - 1) < 2 ^ m := by
    have h1 : (1 : ℕ) ≤ 2 ^ (m - 1) := Nat.one_le_two_pow
    omega
  have hpos : 0 < 2 ^ m := by positivity
  -- the non-antipodal class has `1 + ζ^d ≠ 0`
  have h1pd : (1 : L) + ζ ^ d ≠ 0 := by
    intro h0
    have hneg : ζ ^ (d % 2 ^ m) = ζ ^ (2 ^ (m - 1)) := by
      rw [← pow_reduce hζ d, pow_half_eq_neg_one_field hm hζ]
      linear_combination h0
    exact hd (hζ.pow_inj (Nat.mod_lt _ hpos) hhalf_lt hneg)
  have hfactors : (ζ ^ j - ζ ^ i) * (1 + ζ ^ d) ≠ 0 :=
    mul_ne_zero (sub_ne_zero.mpr (Ne.symm hij)) h1pd
  -- power equality ↔ the congruence
  have hpow_iff : ζ ^ (i + j + d) = ζ ^ (2 * k)
      ↔ (2 * k) % 2 ^ m = (i + j + d) % 2 ^ m := by
    rw [pow_reduce hζ (i + j + d), pow_reduce hζ (2 * k)]
    constructor
    · intro h
      exact (hζ.pow_inj (Nat.mod_lt _ hpos) (Nat.mod_lt _ hpos) h).symm
    · intro h
      rw [h]
  constructor
  · intro hdet
    have h0 : (ζ ^ j - ζ ^ i) * (1 + ζ ^ d) * (ζ ^ (i + j + d) - ζ ^ (2 * k)) = 0 :=
      (chord_det_factor hm hζ i j k d).symm.trans (sub_eq_zero.mpr hdet)
    have h3 : ζ ^ (i + j + d) - ζ ^ (2 * k) = 0 := by
      rcases mul_eq_zero.mp h0 with h | h
      · exact absurd h hfactors
      · exact h
    exact hpow_iff.mp (sub_eq_zero.mp h3)
  · intro hcong
    have h3 : ζ ^ (i + j + d) - ζ ^ (2 * k) = 0 :=
      sub_eq_zero.mpr (hpow_iff.mpr hcong)
    have h0 : (ζ ^ j - ζ ^ i) * (1 + ζ ^ d) * (ζ ^ (i + j + d) - ζ ^ (2 * k)) = 0 := by
      rw [h3, mul_zero]
    exact sub_eq_zero.mp ((chord_det_factor hm hζ i j k d).trans h0)

/-! ## Source audit -/

#print axioms pow_reduce
#print axioms chord_det_factor
#print axioms two_plus_antipodal_collinear_iff

end ArkLib.ProximityGap.TwoPlusAntipodalChordLaw
