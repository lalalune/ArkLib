/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DeBruijnWeightedTwoPrime

/-!
# Issue #232 — ℤ-RELATIONS, stage 1 (O109a): the ℤ-weighted de Bruijn
# classification at two-prime moduli, by the shift trick

The Schoenberg/Rédei **relation theorem** says the lattice of ℤ-linear relations
among the `n`-th roots of unity is spanned by the rotated full prime packets —
for EVERY `n`, including 3+-prime moduli where the ℕ-cone (packet
decomposition) form is refuted (O105's witness at `n = 30`).  The ℤ-side door
into 3+-prime territory is therefore open while the ℕ-door is closed.

Probe (`scripts/probes/probe_schoenberg_z_relations.py`, exit 0): the packet
lattice is a saturated sublattice of rank `n − φ(n)` (all Smith invariants `1`)
at `n = 12, 36, 30, 60, 90, 105, 210` — two-, three-, and four-prime moduli,
squarefree and not.

This file lands the **two-prime case** as a corollary of the ℕ-classification
(O103), by the shift trick: given a vanishing ℤ-combination `w`, add `c·𝟙` for
`c` large (the all-ones vector `𝟙` is itself a vanishing combination since
`Σ_{e<n} ζ^e = 0`), classify the resulting ℕ-combination by O103, and subtract
the constant back inside a coefficient function.

* `debruijn_int_two_prime` — **the iff**: `Σ_{e<n} w_e ζ^e = 0  ↔
  ∃ A B : ℕ → ℤ, w_e = A(e % n/p) + B(e % n/q)` on `[0, n)`, `n = p^a·q^b`.
* `packet_part_eq_zero_int` — the ℤ-converse engine (positive/negative-part
  split of the ℕ-engine).

Stages 2–3 (the coprime equal-thread-sum split and the squarefree three-prime
assembly) are the named continuation.
-/

namespace DeBruijnIntRelations

open Finset

variable {L : Type*} [Field L]

/-- A ℤ-weighted root sum splits as the difference of the ℕ-sums of its
positive and negative parts. -/
lemma int_sum_split (w : ℕ → ℤ) (n : ℕ) (f : ℕ → L) :
    ∑ e ∈ Finset.range n, (w e : L) * f e
      = (∑ e ∈ Finset.range n, (((w e).toNat : ℕ) : L) * f e)
        - ∑ e ∈ Finset.range n, ((((-(w e)).toNat : ℕ)) : L) * f e := by
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [← sub_mul]
  congr 1
  have h := Int.toNat_sub_toNat_neg (w e)
  have h2 := congrArg (fun z : ℤ => (z : L)) h
  push_cast at h2
  exact h2.symm

/-- **The ℤ-converse engine**: a ℤ-valued `μ_u`-coset combination kills the full
power sum (positive/negative split of the ℕ-engine). -/
lemma packet_part_eq_zero_int {n u : ℕ} (hu : 1 < u) (hun : u ∣ n) (hn : 0 < n)
    {ζ : L} (hζ : IsPrimitiveRoot ζ n) (A : ℕ → ℤ) :
    ∑ e ∈ Finset.range n, (A (e % (n / u)) : L) * ζ ^ e = 0 := by
  rw [int_sum_split (fun e => A (e % (n / u))) n (ζ ^ ·)]
  have hpos := DeBruijnWeightedTwoPrime.packet_part_eq_zero (L := L) hu hun hn hζ
    (fun r => (A r).toNat)
  have hneg := DeBruijnWeightedTwoPrime.packet_part_eq_zero (L := L) hu hun hn hζ
    (fun r => (-(A r)).toNat)
  rw [hpos, hneg, sub_zero]

/-- **THE ℤ-WEIGHTED DE BRUIJN CLASSIFICATION AT TWO-PRIME MODULI** (O109a; the
Schoenberg/Rédei relation theorem at `n = p^a·q^b`): a ℤ-combination of `n`-th
roots of unity vanishes iff it is a ℤ-combination of rotated full prime packets
— concretely, iff the weight splits as `A(e % n/p) + B(e % n/q)` with
ℤ-coefficient functions. -/
theorem debruijn_int_two_prime [CharZero L] {p q a b : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (ha : 0 < a) (hb : 0 < b)
    {ζ : L} (hζ : IsPrimitiveRoot ζ (p ^ a * q ^ b)) (w : ℕ → ℤ) :
    (∑ e ∈ Finset.range (p ^ a * q ^ b), (w e : L) * ζ ^ e = 0) ↔
      ∃ A B : ℕ → ℤ, ∀ e < p ^ a * q ^ b,
        w e = A (e % (p ^ (a - 1) * q ^ b)) + B (e % (p ^ a * q ^ (b - 1))) := by
  have hnpos : 0 < p ^ a * q ^ b :=
    Nat.mul_pos (pow_pos hp.pos a) (pow_pos hq.pos b)
  have hn1 : 1 < p ^ a * q ^ b :=
    lt_of_lt_of_le (Nat.one_lt_pow ha.ne' hp.one_lt)
      (Nat.le_mul_of_pos_right _ (pow_pos hq.pos b))
  have hdivp : (p ^ a * q ^ b) / p = p ^ (a - 1) * q ^ b := by
    have h2 : p * p ^ (a - 1) = p ^ a := by
      rw [← pow_succ']
      congr 1
      omega
    have hform : p ^ a * q ^ b = p * (p ^ (a - 1) * q ^ b) := by
      rw [← h2]; ring
    rw [hform, Nat.mul_div_cancel_left _ hp.pos]
  have hdivq : (p ^ a * q ^ b) / q = p ^ a * q ^ (b - 1) := by
    have h2 : q * q ^ (b - 1) = q ^ b := by
      rw [← pow_succ']
      congr 1
      omega
    have hform : p ^ a * q ^ b = q * (p ^ a * q ^ (b - 1)) := by
      rw [← h2]; ring
    rw [hform, Nat.mul_div_cancel_left _ hq.pos]
  constructor
  · intro hsum
    -- the shift: w + c·𝟙 is an ℕ-weight with vanishing sum
    set c : ℕ := (Finset.range (p ^ a * q ^ b)).sup (fun e => (w e).natAbs)
      with hc
    have hbound : ∀ e < p ^ a * q ^ b, 0 ≤ w e + c := by
      intro e he
      have h1 : (w e).natAbs ≤ c :=
        Finset.le_sup (f := fun e => (w e).natAbs) (Finset.mem_range.mpr he)
      omega
    have hcast : ∀ e < p ^ a * q ^ b, (((w e + c).toNat : ℕ) : ℤ) = w e + c :=
      fun e he => Int.toNat_of_nonneg (hbound e he)
    have husum : ∑ e ∈ Finset.range (p ^ a * q ^ b),
        (((w e + c).toNat : ℕ) : L) * ζ ^ e = 0 := by
      have hgeom : ∑ e ∈ Finset.range (p ^ a * q ^ b), ζ ^ e = 0 :=
        hζ.geom_sum_eq_zero hn1
      calc ∑ e ∈ Finset.range (p ^ a * q ^ b), (((w e + c).toNat : ℕ) : L) * ζ ^ e
          = ∑ e ∈ Finset.range (p ^ a * q ^ b), ((w e : L) + (c : L)) * ζ ^ e := by
            refine Finset.sum_congr rfl fun e he => ?_
            congr 1
            have h := congrArg (fun z : ℤ => (z : L))
              (hcast e (Finset.mem_range.mp he))
            push_cast at h
            exact h
        _ = (∑ e ∈ Finset.range (p ^ a * q ^ b), (w e : L) * ζ ^ e)
            + (c : L) * ∑ e ∈ Finset.range (p ^ a * q ^ b), ζ ^ e := by
            simp only [add_mul]
            rw [Finset.sum_add_distrib, Finset.mul_sum]
        _ = 0 := by rw [hsum, hgeom, mul_zero, add_zero]
    obtain ⟨A', B', hAB⟩ :=
      (DeBruijnWeightedTwoPrime.debruijn_weighted_two_prime hp hq hpq ha hb hζ
        (fun e => (w e + c).toNat)).mp husum
    refine ⟨fun r => (A' r : ℤ) - c, fun r => (B' r : ℤ), fun e he => ?_⟩
    have h1 := hAB e he
    have h2 := hcast e he
    dsimp only
    omega
  · rintro ⟨A, B, hAB⟩
    have hsplit : ∑ e ∈ Finset.range (p ^ a * q ^ b), (w e : L) * ζ ^ e
        = (∑ e ∈ Finset.range (p ^ a * q ^ b),
            (A (e % (p ^ (a - 1) * q ^ b)) : L) * ζ ^ e)
          + ∑ e ∈ Finset.range (p ^ a * q ^ b),
              (B (e % (p ^ a * q ^ (b - 1))) : L) * ζ ^ e := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun e he => ?_
      rw [hAB e (Finset.mem_range.mp he)]
      push_cast
      ring
    have hA0 := packet_part_eq_zero_int hp.one_lt
      (dvd_mul_of_dvd_left (dvd_pow_self p ha.ne') _) hnpos hζ A
    have hB0 := packet_part_eq_zero_int hq.one_lt
      (dvd_mul_of_dvd_right (dvd_pow_self q hb.ne') _) hnpos hζ B
    rw [hdivp] at hA0
    rw [hdivq] at hB0
    rw [hsplit, hA0, hB0, add_zero]

end DeBruijnIntRelations

#print axioms DeBruijnIntRelations.int_sum_split
#print axioms DeBruijnIntRelations.packet_part_eq_zero_int
#print axioms DeBruijnIntRelations.debruijn_int_two_prime
