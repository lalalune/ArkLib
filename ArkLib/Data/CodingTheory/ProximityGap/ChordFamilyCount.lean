/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.ZMod.Basic

/-!
# The chord-family count, odd classes: `n(n−4)` parametrized solutions per class

Campaign #357, the per-class counting corollary of the two-plus-antipodal chord law. The
probe-pinned targets: each odd difference class carries exactly `n(n−4)/4` unordered
family triples, each even class `n(n−8)/4`, summing over the `n/4` odd and `n/4 − 1`
even non-antipodal classes to the family closed form `n(n−4)²/8`.

This file proves the odd-class count in its parametrized (ordered) form. The chord law
says `{i, i+d}, {j, j+d}, {k, k+2^(m−1)}` is collinear iff `2k = i + j + d`, so a family
triple is parametrized by `(i, k)` (then `j := 2k − i − d`), and:

* the disjointness of the antipodal completion from the two chord pairs is **exactly**
  `k ∉ {i, i+h, i+d, i+d+h}` (`h = 2^(m−1)`) — the `j`-side disjointness conditions
  coincide with these four (`2k ≡ 2i ⟺ j ≡ i−d`, `2k ≡ 2i+2d ⟺ j ≡ i+d`);
* the degeneracy conditions (`j = i`, the pair collision, and `j = i+h`, the horizontal
  line) are `2k = 2i + d` and `2k = 2i + d + h` — **unsolvable for odd `d`**
  (`oddCast_ne_double`: project to `ZMod 2`).

Hence the parametrized solution set is, per odd class, a per-`i` exclusion of four
distinct points: `chord_param_count_odd` — **exactly `n(n−4)` ordered `(i, k)` pairs**.
The unordered family count per odd class is the 4-fold quotient `n(n−4)/4` (the `i ↔ j`
swap and `k ↔ k+h`), matching the probe; the even-class analogue (four more exclusions,
`n(n−8)`) and the cross-class summation to `n(n−4)²/8` are the named follow-up.

All results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References

* Issue #357 (the census closed-forms comment; per-class targets pinned by probe);
  `TwoPlusAntipodalChordLaw.lean` (the law + `completion_count`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.ChordFamilyCount

variable {m : ℕ}

/-- `2^(m−1)` is nonzero in `ZMod (2^m)`. -/
theorem half_ne_zero (hm : 1 ≤ m) :
    ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) ≠ 0 := by
  intro h0
  rw [ZMod.natCast_eq_zero_iff] at h0
  have hlt : 2 ^ (m - 1) < 2 ^ m := Nat.pow_lt_pow_right one_lt_two (by omega)
  have hpos : 0 < 2 ^ (m - 1) := Nat.two_pow_pos _
  exact absurd (Nat.le_of_dvd hpos h0) (not_le.mpr hlt)

/-- `2^(m−1)` is self-negative in `ZMod (2^m)`: `h + h = 0`. -/
theorem half_add_half (hm : 1 ≤ m) :
    ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) = 0 := by
  rw [← Nat.cast_add, ZMod.natCast_eq_zero_iff]
  have h : 2 ^ (m - 1) + 2 ^ (m - 1) = 2 ^ m := by
    have h := pow_succ 2 (m - 1)
    rw [Nat.sub_add_cancel hm] at h
    omega
  rw [h]

/-- An odd natural is nonzero in `ZMod (2^m)` for `m ≥ 1`. -/
theorem oddCast_ne_zero (hm : 1 ≤ m) {d : ℕ} (hd : d % 2 = 1) :
    ((d : ℕ) : ZMod (2 ^ m)) ≠ 0 := by
  intro h0
  rw [ZMod.natCast_eq_zero_iff] at h0
  have h2 : 2 ∣ d := dvd_trans (dvd_pow_self 2 (by omega : m ≠ 0)) h0
  omega

/-- The `ZMod 2` projection of `ZMod (2^m)`. -/
noncomputable def proj (m : ℕ) (hm : m ≠ 0) : ZMod (2 ^ m) →+* ZMod 2 :=
  ZMod.castHom (dvd_pow_self 2 hm) (ZMod 2)

/-- **Odd unsolvability**: `2x = 2y + d` has no solutions in `ZMod (2^m)` for odd `d` —
the pair-collision degeneracy of the chord parametrization is vacuous on odd classes. -/
theorem oddCast_ne_double (hm : 1 ≤ m) {d : ℕ} (hd : d % 2 = 1)
    (x y : ZMod (2 ^ m)) : 2 * x ≠ 2 * y + (d : ZMod (2 ^ m)) := by
  intro heq
  have h := congrArg (proj m (by omega)) heq
  simp only [map_add, map_mul, map_ofNat, map_natCast] at h
  have h2 : (2 : ZMod 2) = 0 := by decide
  rw [h2, zero_mul, zero_mul, zero_add] at h
  have hd2 : ((d : ℕ) : ZMod 2) ≠ 0 := by
    intro h0
    rw [ZMod.natCast_eq_zero_iff] at h0
    omega
  exact hd2 h.symm

/-- **Odd-shift unsolvability**: `2x = 2y + d + 2^(m−1)` has no solutions for odd `d`,
`m ≥ 2` — the horizontal degeneracy is vacuous on odd classes. -/
theorem oddCast_ne_double_half (hm : 2 ≤ m) {d : ℕ} (hd : d % 2 = 1)
    (x y : ZMod (2 ^ m)) :
    2 * x ≠ 2 * y + (d : ZMod (2 ^ m)) + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) := by
  intro heq
  have h := congrArg (proj m (by omega)) heq
  simp only [map_add, map_mul, map_ofNat, map_natCast] at h
  have h2 : (2 : ZMod 2) = 0 := by decide
  have hh2 : ((2 ^ (m - 1) : ℕ) : ZMod 2) = 0 := by
    rw [ZMod.natCast_eq_zero_iff]
    exact dvd_pow_self 2 (by omega : m - 1 ≠ 0)
  rw [h2, zero_mul, zero_mul, zero_add, hh2, add_zero] at h
  have hd2 : ((d : ℕ) : ZMod 2) ≠ 0 := by
    intro h0
    rw [ZMod.natCast_eq_zero_iff] at h0
    omega
  exact hd2 h.symm

/-- An odd natural differs from `2^(m−1)` in `ZMod (2^m)` for `m ≥ 2`. -/
theorem oddCast_ne_half (hm : 2 ≤ m) {d : ℕ} (hd : d % 2 = 1) :
    ((d : ℕ) : ZMod (2 ^ m)) ≠ ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) := by
  intro heq
  have h := congrArg (proj m (by omega)) heq
  simp only [map_natCast] at h
  have hd2 : ((d : ℕ) : ZMod 2) ≠ 0 := by
    intro h0
    rw [ZMod.natCast_eq_zero_iff] at h0
    omega
  have hh2 : ((2 ^ (m - 1) : ℕ) : ZMod 2) = 0 := by
    rw [ZMod.natCast_eq_zero_iff]
    exact dvd_pow_self 2 (by omega : m - 1 ≠ 0)
  rw [hh2] at h
  exact hd2 h

/-- The four excluded completion points of a chord base `i`. -/
def exclusions (m : ℕ) (d : ℕ) (i : ZMod (2 ^ m)) : Finset (ZMod (2 ^ m)) :=
  {i, i + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)), i + (d : ZMod (2 ^ m)),
    i + ((d : ZMod (2 ^ m)) + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)))}

/-- For odd `d` and `m ≥ 2` the four excluded points are pairwise distinct. -/
theorem card_exclusions (hm : 2 ≤ m) {d : ℕ} (hd : d % 2 = 1) (i : ZMod (2 ^ m)) :
    (exclusions m d i).card = 4 := by
  have h1 : 1 ≤ m := by omega
  have hh0 := half_ne_zero h1
  have hd0 := oddCast_ne_zero h1 hd
  have hdh := oddCast_ne_half hm hd
  have hhh := half_add_half h1
  have hdh0 : (d : ZMod (2 ^ m)) + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) ≠ 0 := by
    intro h0
    apply hdh
    have h := congrArg (· + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))) h0
    simp only [zero_add] at h
    rw [add_assoc, hhh, add_zero] at h
    exact h
  unfold exclusions
  rw [card_insert_of_notMem, card_insert_of_notMem, card_insert_of_notMem,
    card_singleton]
  · -- i + d ∉ {i + (d + h)}
    simp only [mem_singleton]
    intro h
    rw [← add_assoc] at h
    exact hh0 (left_eq_add.mp h)
  · -- i + h ∉ {i + d, i + (d + h)}
    simp only [mem_insert, mem_singleton]
    push Not
    constructor
    · intro h
      exact hdh (add_left_cancel h).symm
    · intro h
      have h' := add_left_cancel h
      -- h = d + h forces d = 0
      apply hd0
      have h2 := congrArg (· + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))) h'
      simp only at h2
      rw [hhh, add_assoc, hhh, add_zero] at h2
      exact h2.symm
  · -- i ∉ {i + h, i + d, i + (d + h)}
    simp only [mem_insert, mem_singleton]
    push Not
    refine ⟨fun h => hh0 (left_eq_add.mp h),
      fun h => hd0 (left_eq_add.mp h),
      fun h => hdh0 (left_eq_add.mp h)⟩

/-- **THE ODD-CLASS CHORD COUNT.** For every odd class `d` at scale `n = 2^m`, `m ≥ 2`:
the parametrized chord-law solution set — pairs `(i, k)` of chord base point and
antipodal completion with the completion disjoint from the chord pairs and the
degeneracies excluded — has **exactly `n(n−4)` elements**. The unordered family count
per odd class is the 4-fold quotient `n(n−4)/4`, the probe-pinned target. -/
theorem chord_param_count_odd (hm : 2 ≤ m) {d : ℕ} (hd : d % 2 = 1) :
    ((univ : Finset (ZMod (2 ^ m) × ZMod (2 ^ m))).filter (fun p =>
        p.2 ∉ exclusions m d p.1
        ∧ 2 * p.2 ≠ 2 * p.1 + (d : ZMod (2 ^ m))
        ∧ 2 * p.2 ≠ 2 * p.1 + (d : ZMod (2 ^ m))
            + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)))).card
      = 2 ^ m * (2 ^ m - 4) := by
  haveI : NeZero (2 ^ m) := ⟨(Nat.two_pow_pos m).ne'⟩
  have h1 : 1 ≤ m := by omega
  -- the degeneracy conjuncts are vacuous for odd d
  have hvac : ∀ p : ZMod (2 ^ m) × ZMod (2 ^ m),
      (p.2 ∉ exclusions m d p.1
        ∧ 2 * p.2 ≠ 2 * p.1 + (d : ZMod (2 ^ m))
        ∧ 2 * p.2 ≠ 2 * p.1 + (d : ZMod (2 ^ m))
            + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)))
      ↔ p.2 ∉ exclusions m d p.1 :=
    fun p => ⟨fun h => h.1, fun h =>
      ⟨h, oddCast_ne_double h1 hd p.2 p.1, oddCast_ne_double_half hm hd p.2 p.1⟩⟩
  have hfc : ((univ : Finset (ZMod (2 ^ m) × ZMod (2 ^ m))).filter (fun p =>
        p.2 ∉ exclusions m d p.1
        ∧ 2 * p.2 ≠ 2 * p.1 + (d : ZMod (2 ^ m))
        ∧ 2 * p.2 ≠ 2 * p.1 + (d : ZMod (2 ^ m))
            + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))))
      = (univ : Finset (ZMod (2 ^ m) × ZMod (2 ^ m))).filter
          (fun p => p.2 ∉ exclusions m d p.1) :=
    Finset.filter_congr fun p _ => hvac p
  rw [hfc]
  -- fiber over the first coordinate
  rw [Finset.card_eq_sum_card_fiberwise
    (f := Prod.fst) (t := (univ : Finset (ZMod (2 ^ m)))) (fun x _ => mem_univ _)]
  have hfiber : ∀ i0 : ZMod (2 ^ m),
      (((univ : Finset (ZMod (2 ^ m) × ZMod (2 ^ m))).filter
          (fun p => p.2 ∉ exclusions m d p.1)).filter (fun p => p.1 = i0)).card
        = ((univ : Finset (ZMod (2 ^ m))).filter
            (fun k => k ∉ exclusions m d i0)).card := by
    intro i0
    apply Finset.card_nbij (fun p => p.2)
    · intro p hp
      simp only [Finset.coe_filter, Set.mem_setOf_eq, mem_filter, mem_univ,
        true_and] at hp ⊢
      rw [← hp.2]
      exact hp.1
    · intro p hp q hq hpq
      simp only [Finset.coe_filter, Set.mem_setOf_eq, mem_filter, mem_univ,
        true_and] at hp hq
      exact Prod.ext (hp.2.trans hq.2.symm) hpq
    · intro k hk
      simp only [Finset.coe_filter, Set.mem_setOf_eq, mem_univ,
        true_and] at hk
      exact ⟨(i0, k), by simp [hk], rfl⟩
  rw [Finset.sum_congr rfl fun i0 _ => hfiber i0]
  have hcount : ∀ i0 : ZMod (2 ^ m),
      ((univ : Finset (ZMod (2 ^ m))).filter (fun k => k ∉ exclusions m d i0)).card
        = 2 ^ m - 4 := by
    intro i0
    have hsd : (univ : Finset (ZMod (2 ^ m))).filter (fun k => k ∉ exclusions m d i0)
        = univ \ exclusions m d i0 := by
      ext k
      simp [mem_sdiff]
    rw [hsd, card_sdiff, Finset.inter_univ, card_univ, ZMod.card,
      card_exclusions hm hd i0]
  rw [Finset.sum_congr rfl fun i0 _ => hcount i0, Finset.sum_const, card_univ,
    ZMod.card, smul_eq_mul]

/-! ## Source audit -/

#print axioms oddCast_ne_double
#print axioms card_exclusions
#print axioms chord_param_count_odd

end ArkLib.ProximityGap.ChordFamilyCount
