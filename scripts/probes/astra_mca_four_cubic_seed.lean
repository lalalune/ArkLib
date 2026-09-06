/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Fin.VecNotation
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic

/-!
# The exact four-cubic order-eight seed

The four sources in `docs/kb/astra_mca_four_cubic-2026-09-06.md` are constructed
by explicit field operations. Their six differences factor over the actual
powers of a primitive eighth root, with nonzero leading factors. The resulting
root characterizations give every equality and inequality in the eight-row
partition table. The three nonzero sources, and all six differences, have
natural degree exactly three. The normalization agrees with the checker;
no interpolation polynomial or seed identity is assumed.

The algebraic factorization proofs use only `eta ^ 4 = -1`. Nonvanishing and
order-eight indexing use `IsPrimitiveRoot eta 8`. This isolates the seed from
the production generator's large exponent: the file does not assert a
production-domain instantiation or the final MCA bound.

Validation status at creation: source awaiting Lean CI; the local toolchain
and `.lake` cache were absent. The companion exact symbolic script checks the
integer polynomial multipliers used in the `linear_combination` proofs, but
that script is not a kernel receipt.
-/

set_option autoImplicit false
set_option maxRecDepth 10000

noncomputable section
namespace AstraMcaFourCubicSeed
open Polynomial

/-- The six unordered source pairs, in the order of the written certificate. -/
inductive Pair
  | p01 | p02 | p03 | p12 | p13 | p23
  deriving DecidableEq

/-- The lower source index of a pair. -/
def leftIndex : Pair → Fin 4
  | .p01 | .p02 | .p03 => 0
  | .p12 | .p13 => 1
  | .p23 => 2

/-- The higher source index of a pair. -/
def rightIndex : Pair → Fin 4
  | .p01 => 1
  | .p02 | .p12 => 2
  | .p03 | .p13 | .p23 => 3

/-- The first root exponent in a pair difference. -/
def rootA : Pair → ℕ
  | .p01 | .p02 | .p12 => 0
  | .p03 | .p13 => 1
  | .p23 => 3

/-- The second root exponent in a pair difference. -/
def rootB : Pair → ℕ
  | .p01 => 1
  | .p02 => 3
  | .p03 => 2
  | .p12 | .p13 | .p23 => 6

/-- The third root exponent in a pair difference. -/
def rootC : Pair → ℕ
  | .p01 => 5
  | .p02 => 4
  | .p03 => 3
  | .p12 | .p13 | .p23 => 7

section RingIdentities
variable {R : Type*} [CommRing R]

/-- Twice the normalization coefficient of the second nonzero source. -/
def a (e : R) : R := 1 - e + e ^ 2 - e ^ 3

/-- Twice the normalization coefficient of the third nonzero source. -/
def b (e : R) : R := 2 - e + e ^ 3

private theorem algebra_pair12 (e x : R) (h4 : e ^ 4 = -1) :
    a e * ((x - 1) * (x - e ^ 3) * (x + 1)) -
      2 * ((x - 1) * (x - e) * (x + e)) =
    (a e - 2) * ((x - 1) * (x + e ^ 2) * (x + e ^ 3)) := by
  dsimp [a]
  linear_combination
    (e ^ 4 * x - e ^ 4 - e ^ 3 * x + e ^ 3 +
      2 * e ^ 2 * x ^ 2 - 2 * e ^ 2 - e * x ^ 2 + e * x + x ^ 2 - x) * h4

private theorem algebra_pair13 (e x : R) (h4 : e ^ 4 = -1) :
    b e * ((x - e) * (x - e ^ 2) * (x - e ^ 3)) -
      2 * ((x - 1) * (x - e) * (x + e)) =
    (b e - 2) * ((x - e) * (x + e ^ 2) * (x + e ^ 3)) := by
  dsimp [b]
  linear_combination
    (2 * e ^ 3 * x - 2 * e ^ 2 * x ^ 2 + 2 * e ^ 2 * x -
      2 * e ^ 2 - 2 * e * x ^ 2 + 2 * x ^ 2) * h4

private theorem algebra_pair23 (e x : R) (h4 : e ^ 4 = -1) :
    b e * ((x - e) * (x - e ^ 2) * (x - e ^ 3)) -
      a e * ((x - 1) * (x - e ^ 3) * (x + 1)) =
    (b e - a e) * ((x - e ^ 3) * (x + e ^ 2) * (x + e ^ 3)) := by
  dsimp [a, b]
  linear_combination
    (2 * e ^ 7 - e ^ 6 + 2 * e ^ 5 * x - e ^ 5 + e ^ 4 +
      e ^ 3 * x - e ^ 3 - 2 * e ^ 2 * x ^ 2 + e ^ 2 * x -
      2 * e * x ^ 2 - e * x + x) * h4

/-- The five nonconstant pair scalars have explicit inverse-product
certificates equal to two. This prevents characteristic-specific vanishing. -/
theorem scalar_inverse_products (e : R) (h4 : e ^ 4 = -1) :
    a e * (1 + e) = 2 ∧
    b e * (2 + e - e ^ 3) = 2 ∧
    (a e - 2) * (e ^ 3 - 1) = 2 ∧
    (b e - 2) * (b e - 2) = 2 ∧
    (b e - a e) * (-1 - 2 * e - e ^ 2) = 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> dsimp [a, b]
  · linear_combination -h4
  · linear_combination (2 - e ^ 2) * h4
  · linear_combination (-e ^ 2 + e - 1) * h4
  · linear_combination (e ^ 2 - 2) * h4
  · linear_combination (-2 * e - 3) * h4

end RingIdentities

section Seed
variable {F : Type*} [Field F]

/-- The monic cubic with the three specified power roots. -/
def triple (eta : F) (i j k : ℕ) : F[X] :=
  (X - C (eta ^ i)) * (X - C (eta ^ j)) * (X - C (eta ^ k))

/-- The first monic cubic in the written construction. -/
def r1 (eta : F) : F[X] := triple eta 0 1 5

/-- The second monic cubic in the written construction. -/
def r2 (eta : F) : F[X] := triple eta 0 3 4

/-- The third monic cubic in the written construction. -/
def r3 (eta : F) : F[X] := triple eta 1 2 3

/-- The sources after multiplication by the common nonzero scalar two. -/
def rawSeed (eta : F) : Fin 4 → F[X] :=
  ![0, C 2 * r1 eta, C (a eta) * r2 eta, C (b eta) * r3 eta]

/-- The actual normalized sources; `seed eta 1 = r1 eta` is proved below. -/
def seed (eta : F) (i : Fin 4) : F[X] :=
  C ((2 : F)⁻¹) * rawSeed eta i

/-- The six leading factors before the common normalization. -/
def rawScalar (eta : F) : Pair → F
  | .p01 => 2
  | .p02 => a eta
  | .p03 => b eta
  | .p12 => a eta - 2
  | .p13 => b eta - 2
  | .p23 => b eta - a eta

/-- The six leading factors of the normalized pair differences. -/
def pairScalar (eta : F) (p : Pair) : F := (2 : F)⁻¹ * rawScalar eta p

/-- The exact monic root factor of one pair difference. -/
def pairFactor (eta : F) (p : Pair) : F[X] :=
  triple eta (rootA p) (rootB p) (rootC p)

private theorem pow_five (eta : F) (h4 : eta ^ 4 = -1) : eta ^ 5 = -eta := by
  calc
    eta ^ 5 = eta ^ 4 * eta := by ring
    _ = -eta := by rw [h4]; ring

private theorem pow_six (eta : F) (h4 : eta ^ 4 = -1) : eta ^ 6 = -(eta ^ 2) := by
  calc
    eta ^ 6 = eta ^ 4 * eta ^ 2 := by ring
    _ = -(eta ^ 2) := by rw [h4]; ring

private theorem pow_seven (eta : F) (h4 : eta ^ 4 = -1) : eta ^ 7 = -(eta ^ 3) := by
  calc
    eta ^ 7 = eta ^ 4 * eta ^ 3 := by ring
    _ = -(eta ^ 3) := by rw [h4]; ring

/-- All six factorization identities before normalization. They are proved
as polynomial identities, rather than inferred from evaluation data. -/
theorem raw_pair_factorization (eta : F) (h4 : eta ^ 4 = -1) (p : Pair) :
    rawSeed eta (rightIndex p) - rawSeed eta (leftIndex p) =
      C (rawScalar eta p) * pairFactor eta p := by
  have h5 := pow_five eta h4
  have h6 := pow_six eta h4
  have h7 := pow_seven eta h4
  have h4C : (C eta : F[X]) ^ 4 = -1 := by
    simpa using congrArg (C : F → F[X]) h4
  cases p with
  | p01 => simp [rawSeed, leftIndex, rightIndex, rawScalar, pairFactor, rootA, rootB, rootC, r1]
  | p02 => simp [rawSeed, leftIndex, rightIndex, rawScalar, pairFactor, rootA, rootB, rootC, r2]
  | p03 => simp [rawSeed, leftIndex, rightIndex, rawScalar, pairFactor, rootA, rootB, rootC, r3]
  | p12 =>
    simpa [rawSeed, leftIndex, rightIndex, rawScalar, pairFactor, rootA, rootB, rootC,
      r1, r2, triple, h4, h5, h6, h7, a, sub_neg_eq_add] using
      algebra_pair12 (C eta : F[X]) X h4C
  | p13 =>
    simpa [rawSeed, leftIndex, rightIndex, rawScalar, pairFactor, rootA, rootB, rootC,
      r1, r3, triple, h4, h5, h6, h7, b, sub_neg_eq_add] using
      algebra_pair13 (C eta : F[X]) X h4C
  | p23 =>
    simpa [rawSeed, leftIndex, rightIndex, rawScalar, pairFactor, rootA, rootB, rootC,
      r2, r3, triple, h4, h5, h6, h7, a, b, sub_neg_eq_add] using
      algebra_pair23 (C eta : F[X]) X h4C

/-- Every difference factors with exactly the advertised three power roots. -/
theorem pair_factorization (eta : F) (h4 : eta ^ 4 = -1) (p : Pair) :
    seed eta (rightIndex p) - seed eta (leftIndex p) =
      C (pairScalar eta p) * pairFactor eta p := by
  calc
    seed eta (rightIndex p) - seed eta (leftIndex p) =
        C ((2 : F)⁻¹) * (rawSeed eta (rightIndex p) - rawSeed eta (leftIndex p)) := by
      simp only [seed]
      ring
    _ = C ((2 : F)⁻¹) * (C (rawScalar eta p) * pairFactor eta p) := by
      rw [raw_pair_factorization eta h4 p]
    _ = C (pairScalar eta p) * pairFactor eta p := by
      simp [pairScalar, map_mul, mul_assoc]

/-- A primitive eighth root has fourth power minus one. -/
theorem pow_four (eta : F) (h : IsPrimitiveRoot eta 8) : eta ^ 4 = -1 := by
  have hs : eta ^ 4 * eta ^ 4 = 1 := by
    rw [← pow_add]
    exact h.pow_eq_one
  rcases mul_self_eq_one_iff.mp hs with h1 | h1
  · exact absurd h1 (h.pow_ne_one_of_pos_of_lt (by decide) (by decide))
  · exact h1

/-- The existence of a primitive eighth root excludes characteristic two. -/
theorem two_ne_zero (eta : F) (h : IsPrimitiveRoot eta 8) : (2 : F) ≠ 0 := by
  intro h2
  have h4 := pow_four eta h
  have he : eta ^ 4 = 1 := by linear_combination h4 - h2
  exact h.pow_ne_one_of_pos_of_lt (by decide) (by decide) he

/-- None of the six pair scalars vanishes. -/
theorem rawScalar_ne_zero (eta : F) (h4 : eta ^ 4 = -1)
    (h2 : (2 : F) ≠ 0) (p : Pair) : rawScalar eta p ≠ 0 := by
  obtain ⟨ha, hb, ha2, hb2, hba⟩ := scalar_inverse_products eta h4
  have hn (c d : F) (he : c * d = 2) : c ≠ 0 := by
    intro hc
    rw [hc, zero_mul] at he
    exact h2 he.symm
  cases p with
  | p01 => exact h2
  | p02 => exact hn _ _ ha
  | p03 => exact hn _ _ hb
  | p12 => exact hn _ _ ha2
  | p13 => exact hn _ _ hb2
  | p23 => exact hn _ _ hba

/-- Normalization preserves all six nonzero residual factors. -/
theorem pairScalar_ne_zero (eta : F) (h : IsPrimitiveRoot eta 8) (p : Pair) :
    pairScalar eta p ≠ 0 :=
  mul_ne_zero (inv_ne_zero (two_ne_zero eta h))
    (rawScalar_ne_zero eta (pow_four eta h) (two_ne_zero eta h) p)

@[simp] theorem seed_zero (eta : F) : seed eta 0 = 0 := by
  simp [seed, rawSeed]

/-- The common normalization leaves the first monic cubic exactly unchanged. -/
theorem seed_one (eta : F) (h : IsPrimitiveRoot eta 8) : seed eta 1 = r1 eta := by
  have h2 := two_ne_zero eta h
  calc
    seed eta 1 = C ((2 : F)⁻¹ * 2) * r1 eta := by
      simp [seed, rawSeed, map_mul, mul_assoc]
    _ = r1 eta := by rw [inv_mul_cancel₀ h2]; simp

/-- Complete root characterization of every pair difference, over the
whole field. Consequently there are no unlisted residual zeros. -/
theorem pair_eval_eq_iff (eta : F) (h : IsPrimitiveRoot eta 8) (p : Pair) (x : F) :
    (seed eta (leftIndex p)).eval x = (seed eta (rightIndex p)).eval x ↔
      x = eta ^ rootA p ∨ x = eta ^ rootB p ∨ x = eta ^ rootC p := by
  calc
    (seed eta (leftIndex p)).eval x = (seed eta (rightIndex p)).eval x ↔
        (seed eta (rightIndex p) - seed eta (leftIndex p)).eval x = 0 := by
      rw [eval_sub, sub_eq_zero]
      exact eq_comm
    _ ↔ x = eta ^ rootA p ∨ x = eta ^ rootB p ∨ x = eta ^ rootC p := by
      rw [pair_factorization eta (pow_four eta h) p]
      simp [pairFactor, triple, pairScalar_ne_zero eta h p,
        mul_eq_zero, sub_eq_zero, or_assoc]

/-- The six complete equality tests on all eight domain powers. This is
an indexed form of the entire eight-row partition table in the certificate. -/
theorem pair_power_eval_eq_iff (eta : F) (h : IsPrimitiveRoot eta 8)
    (p : Pair) (j : Fin 8) :
    (seed eta (leftIndex p)).eval (eta ^ j.val) =
        (seed eta (rightIndex p)).eval (eta ^ j.val) ↔
      j.val = rootA p ∨ j.val = rootB p ∨ j.val = rootC p := by
  have ha : rootA p < 8 := by cases p <;> decide
  have hb : rootB p < 8 := by cases p <;> decide
  have hc : rootC p < 8 := by cases p <;> decide
  have hp (k : ℕ) (hk : k < 8) : eta ^ j.val = eta ^ k ↔ j.val = k :=
    ⟨h.pow_inj j.isLt hk, fun he => by rw [he]⟩
  rw [pair_eval_eq_iff eta h p, hp _ ha, hp _ hb, hp _ hc]

/-- A product of three monic linear factors always has degree three. -/
theorem triple_natDegree (eta : F) (i j k : ℕ) : (triple eta i j k).natDegree = 3 := by
  have hi := X_sub_C_ne_zero (eta ^ i)
  have hj := X_sub_C_ne_zero (eta ^ j)
  have hk := X_sub_C_ne_zero (eta ^ k)
  unfold triple
  rw [natDegree_mul (mul_ne_zero hi hj) hk, natDegree_mul hi hj]
  simp only [natDegree_X_sub_C]
  norm_num

/-- Every one of the six pair differences is a nonzero cubic. -/
theorem pair_natDegree (eta : F) (h : IsPrimitiveRoot eta 8) (p : Pair) :
    (seed eta (rightIndex p) - seed eta (leftIndex p)).natDegree = 3 := by
  rw [pair_factorization eta (pow_four eta h) p,
    natDegree_C_mul (pairScalar_ne_zero eta h p)]
  exact triple_natDegree eta _ _ _

/-- None of the four source polynomials coincide. -/
theorem pair_ne (eta : F) (h : IsPrimitiveRoot eta 8) (p : Pair) :
    seed eta (leftIndex p) ≠ seed eta (rightIndex p) := by
  intro he
  have hd := pair_natDegree eta h p
  rw [he, sub_self] at hd
  norm_num at hd

/-- The three nonzero normalized sources have exact natural degree three. -/
theorem seed_natDegree (eta : F) (h : IsPrimitiveRoot eta 8)
    (i : Fin 4) (hi : i ≠ 0) : (seed eta i).natDegree = 3 := by
  fin_cases i
  · exact (hi rfl).elim
  · simpa [leftIndex, rightIndex] using pair_natDegree eta h Pair.p01
  · simpa [leftIndex, rightIndex] using pair_natDegree eta h Pair.p02
  · simpa [leftIndex, rightIndex] using pair_natDegree eta h Pair.p03

/-- The monic source factors are nonzero at the normalizing point. -/
theorem normalization_denominators (eta : F) (h : IsPrimitiveRoot eta 8) :
    (r1 eta).eval (eta ^ 6) ≠ 0 ∧
    (r2 eta).eval (eta ^ 6) ≠ 0 ∧
    (r3 eta).eval (eta ^ 6) ≠ 0 := by
  have hn (k : ℕ) (hk : k < 8) (hk6 : k ≠ 6) : eta ^ 6 - eta ^ k ≠ 0 := by
    intro he
    have he' := h.pow_inj (by decide : 6 < 8) hk (sub_eq_zero.mp he)
    exact hk6 he'.symm
  refine ⟨?_, ?_, ?_⟩ <;> simp only [r1, r2, r3, triple, eval_mul, eval_sub, eval_X, eval_C]
  · exact mul_ne_zero (mul_ne_zero (hn 0 (by decide) (by decide))
      (hn 1 (by decide) (by decide))) (hn 5 (by decide) (by decide))
  · exact mul_ne_zero (mul_ne_zero (hn 0 (by decide) (by decide))
      (hn 3 (by decide) (by decide))) (hn 4 (by decide) (by decide))
  · exact mul_ne_zero (mul_ne_zero (hn 1 (by decide) (by decide))
      (hn 2 (by decide) (by decide))) (hn 3 (by decide) (by decide))

/-- Exact recovery of the checker normalization, including both denominators. -/
theorem seed_normalization (eta : F) (h : IsPrimitiveRoot eta 8) :
    seed eta 0 = 0 ∧ seed eta 1 = r1 eta ∧
    seed eta 2 = C ((r1 eta).eval (eta ^ 6) / (r2 eta).eval (eta ^ 6)) * r2 eta ∧
    seed eta 3 = C ((r1 eta).eval (eta ^ 6) / (r3 eta).eval (eta ^ 6)) * r3 eta := by
  obtain ⟨_, hr2, hr3⟩ := normalization_denominators eta h
  have h12 : (seed eta 1).eval (eta ^ 6) = (seed eta 2).eval (eta ^ 6) := by
    apply (pair_eval_eq_iff eta h Pair.p12 (eta ^ 6)).mpr
    exact Or.inr (Or.inl rfl)
  have h13 : (seed eta 1).eval (eta ^ 6) = (seed eta 3).eval (eta ^ 6) := by
    apply (pair_eval_eq_iff eta h Pair.p13 (eta ^ 6)).mpr
    exact Or.inr (Or.inl rfl)
  have hc2 : (2 : F)⁻¹ * a eta =
      (r1 eta).eval (eta ^ 6) / (r2 eta).eval (eta ^ 6) := by
    apply (eq_div_iff hr2).mpr
    rw [seed_one eta h] at h12
    simpa [seed, rawSeed, mul_assoc] using h12.symm
  have hc3 : (2 : F)⁻¹ * b eta =
      (r1 eta).eval (eta ^ 6) / (r3 eta).eval (eta ^ 6) := by
    apply (eq_div_iff hr3).mpr
    rw [seed_one eta h] at h13
    simpa [seed, rawSeed, mul_assoc] using h13.symm
  refine ⟨seed_zero eta, seed_one eta h, ?_, ?_⟩
  · calc
      seed eta 2 = C ((2 : F)⁻¹ * a eta) * r2 eta := by
        simp [seed, rawSeed, map_mul, mul_assoc]
      _ = _ := by rw [hc2]
  · calc
      seed eta 3 = C ((2 : F)⁻¹ * b eta) * r3 eta := by
        simp [seed, rawSeed, map_mul, mul_assoc]
      _ = _ := by rw [hc3]

/-- The three nonzero cubics have no common zero anywhere in the field. -/
theorem no_common_zero (eta : F) (h : IsPrimitiveRoot eta 8) (x : F) :
    ¬ ((seed eta 1).eval x = 0 ∧ (seed eta 2).eval x = 0 ∧
      (seed eta 3).eval x = 0) := by
  rintro ⟨h1, h2, h3⟩
  have h1r := (pair_eval_eq_iff eta h Pair.p01 x).mp (by
    simpa [leftIndex, rightIndex] using h1.symm)
  have h2r := (pair_eval_eq_iff eta h Pair.p02 x).mp (by
    simpa [leftIndex, rightIndex] using h2.symm)
  have h3r := (pair_eval_eq_iff eta h Pair.p03 x).mp (by
    simpa [leftIndex, rightIndex] using h3.symm)
  change x = eta ^ 0 ∨ x = eta ^ 1 ∨ x = eta ^ 5 at h1r
  change x = eta ^ 0 ∨ x = eta ^ 3 ∨ x = eta ^ 4 at h2r
  change x = eta ^ 1 ∨ x = eta ^ 2 ∨ x = eta ^ 3 at h3r
  rcases h1r with h1r | h1r | h1r <;>
    rcases h2r with h2r | h2r | h2r <;>
    rcases h3r with h3r | h3r | h3r
  all_goals
    have he12 := h.pow_inj (by decide) (by decide) (h1r.symm.trans h2r)
    have he13 := h.pow_inj (by decide) (by decide) (h1r.symm.trans h3r)
    norm_num at he12 he13

end Seed

#print axioms scalar_inverse_products
#print axioms raw_pair_factorization
#print axioms pair_factorization
#print axioms pairScalar_ne_zero
#print axioms pair_eval_eq_iff
#print axioms pair_power_eval_eq_iff
#print axioms seed_natDegree
#print axioms seed_normalization
#print axioms no_common_zero

end AstraMcaFourCubicSeed
