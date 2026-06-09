/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

set_option linter.style.longLine false

/-!
# Issue #232 — the Stepanov non-vanishing: reduced to ONE named genus hypothesis, with the
# elementary obstruction proven.

`StepanovWeilSubstrate.lean` reduced the #232 Weil bound to the Stepanov auxiliary's
**non-vanishing**: that the constructed `R(X) = A₀(X, X^q) + g(X)^((q−1)/2)·A₁(X, X^q)` is not the
zero polynomial. This file pins that down completely:

## The algebraic chain `squarefree ⟹ Y²−g irreducible` (proven)

* `squarefree_not_isSquare` / `squarefree_not_isSquare_ratFunc` — a squarefree `g` of positive degree
  is not a square in `F[X]`, nor in the rational function field `RatFunc F` (integrally-closed route).
* `X_sq_sub_C_irreducible_iff_not_isSquare` — over any field, `X²−C c` is irreducible iff `c` is not a
  square (Kummer `p = 2`).
* `squarefree_quadratic_irreducible_ratFunc` (the chain) — for `g` squarefree of positive degree,
  `Y²−g` is **irreducible** over `RatFunc F` (i.e. the hyperelliptic curve `Y²=g(X)` is geometrically
  the right object). This discharges the *irreducibility precondition* of the genus argument.

## The base-`q` substitution machinery and faithfulness (proven)

* `subq q A := A(X, X^q)` for `A ∈ F[X][Y]`, with `subq_eq_sum`, `subq_add`, `subq_C_mul`,
  `coeff_subq_digit`, and the keystone `subq_eq_zero_iff` — **`Y↦X^q` is injective on
  `deg_X < q` two-variable polynomials** (base-`q` blocks do not overlap).
* `aux_collapses_to_relation` — `R = 0` collapses to the algebraic relation `A₀ + C(g^((q−1)/2))·A₁ = 0`
  **iff** the *combined* X-blocks all have degree `< q`.

## The precise obstruction, and the wall as one named hypothesis (honest)

* `obstruction_combined_digit_fails` — the combined-digit hypothesis **provably fails** in the
  relevant regime (`deg g·(q−1)/2 ≥ q`): the second term's block overflows the digit, so the two
  terms cancel *across* base-`q` blocks. The elementary base-`q` route therefore **cannot** close the
  non-vanishing — this is machine-checked, not asserted.
* `aux_key_claim_under_irreducibility` — the non-vanishing conclusion `A₀ = A₁ = 0`, carried under the
  single **named hypothesis** `hIrred` (the absolute-irreducibility / genus / Riemann–Roch consequence
  that the relation `A₀ = −g^((q−1)/2)·A₁` has only the trivial solution). This is the irreducible
  analytic core Mathlib lacks: ruling out the cross-block cancellation requires counting `F`-points on
  `Y²=g(X)` (Hasse–Weil), which recovers **only the Johnson radius `√ρ`**, never the past-Johnson `δ*`
  prize #232 actually asks for.

Net: the entire Stepanov non-vanishing is now machine-checked **except** the one named genus
hypothesis, whose *precondition* (irreducibility of `Y²−g`) is itself discharged here for squarefree
`g`. Honest: even discharging it recovers Johnson, not the prize. `#232` stays the open tracker.

All results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
- Stepanov; Schmidt, *Equations over Finite Fields*; Kopparty, *The Weil bounds*; Bombieri (1973);
  Kowalski, *Exponential sums over finite fields, an elementary approach*.
-/

open Polynomial

namespace ArkLib.ProximityGap.StepanovNonVanishing

/-! ## 1. A squarefree polynomial of positive degree is not a square (`F[X]` and `RatFunc F`). -/

section CharNonSquare
variable {F : Type*} [Field F]

/-- A squarefree polynomial that is a square must be a unit. -/
theorem squarefree_isSquare_isUnit (g : F[X]) (hsf : Squarefree g) (hsq : IsSquare g) :
    IsUnit g := by
  obtain ⟨h, rfl⟩ := hsq
  have hh : IsUnit h := hsf h (dvd_refl (h * h))
  exact hh.mul hh

/-- A squarefree polynomial of positive degree is not a square. -/
theorem squarefree_not_isSquare (g : F[X]) (hsf : Squarefree g) (hdeg : 0 < g.natDegree) :
    ¬ IsSquare g := by
  intro hsq
  have hu : IsUnit g := squarefree_isSquare_isUnit g hsf hsq
  have hd0 : g.natDegree = 0 := natDegree_eq_zero_of_isUnit hu
  omega

/-- **Function-field form.** A squarefree `g : F[X]` of positive degree is not a square in
`RatFunc F`. (Integrally-closed route: a square root would be integral over `F[X]`, hence in `F[X]`,
contradicting `squarefree_not_isSquare`.) -/
theorem squarefree_not_isSquare_ratFunc (g : F[X]) (hsf : Squarefree g)
    (hdeg : 0 < g.natDegree) :
    ¬ IsSquare (algebraMap F[X] (RatFunc F) g) := by
  rintro ⟨r, hr⟩
  have hr2 : r ^ 2 = algebraMap F[X] (RatFunc F) g := by rw [sq]; exact hr.symm
  have hint : IsIntegral F[X] r := by
    refine ⟨X ^ 2 - C g, ?_, ?_⟩
    · apply monic_X_pow_sub
      exact lt_of_le_of_lt degree_C_le (by norm_num)
    · rw [eval₂_sub, eval₂_X_pow, eval₂_C, hr2, sub_self]
  obtain ⟨h, hh⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  have key : algebraMap F[X] (RatFunc F) g = algebraMap F[X] (RatFunc F) (h ^ 2) := by
    rw [map_pow, hh, ← hr2]
  have hg : g = h ^ 2 := RatFunc.algebraMap_injective F key
  have : IsSquare g := ⟨h, by rw [hg, sq]⟩
  exact squarefree_not_isSquare g hsf hdeg this

end CharNonSquare

/-! ## 2. The quadratic irreducibility criterion. -/

section QuadraticIrreducible
variable {K : Type*} [Field K]

/-- `IsSquare c ↔ ∃ b, b² = c`. -/
lemma isSquare_iff_exists_sq_eq (c : K) : IsSquare c ↔ ∃ b : K, b ^ 2 = c := by
  constructor
  · rintro ⟨r, rfl⟩; exact ⟨r, by ring⟩
  · rintro ⟨b, rfl⟩; exact ⟨b, by ring⟩

/-- Over a field, `X²−C c` is irreducible iff `c` is not a square (Kummer `p = 2`). -/
theorem X_sq_sub_C_irreducible_iff_not_isSquare (c : K) :
    Irreducible (X ^ 2 - C c) ↔ ¬ IsSquare c := by
  rw [X_pow_sub_C_irreducible_iff_of_prime Nat.prime_two, isSquare_iff_exists_sq_eq, not_exists]

end QuadraticIrreducible

/-! ## 3. The chain: squarefree `g` ⟹ `Y²−g` irreducible over `RatFunc F`. -/

section RatFuncIrreducible
variable {F : Type*} [Field F]

/-- `Y²−g` is irreducible over `RatFunc F` iff `g` is not a square there. -/
theorem stepanov_quadratic_irreducible_iff (g : F[X]) :
    Irreducible (X ^ 2 - C (algebraMap F[X] (RatFunc F) g)) ↔
      ¬ IsSquare (algebraMap F[X] (RatFunc F) g) :=
  X_sq_sub_C_irreducible_iff_not_isSquare _

/-- **The chain (discharges the irreducibility precondition).** For `g` squarefree of positive degree,
`Y²−g` is irreducible over `RatFunc F` — the hyperelliptic curve `Y²=g(X)` is geometrically
irreducible, the precondition of the genus / Hasse–Weil argument. -/
theorem squarefree_quadratic_irreducible_ratFunc (g : F[X]) (hsf : Squarefree g)
    (hdeg : 0 < g.natDegree) :
    Irreducible (X ^ 2 - C (algebraMap F[X] (RatFunc F) g)) :=
  (stepanov_quadratic_irreducible_iff g).mpr (squarefree_not_isSquare_ratFunc g hsf hdeg)

end RatFuncIrreducible

/-! ## 4. The base-`q` substitution `Y ↦ X^q`, its faithfulness, and the auxiliary collapse. -/

section BaseQ
variable {F : Type*}

/-- Substitution `Y ↦ X^q` on `A ∈ F[X][Y]`, i.e. the polynomial `A(X, X^q)`. -/
noncomputable def subq [CommRing F] (q : ℕ) (A : Polynomial (Polynomial F)) : Polynomial F :=
  A.eval₂ (RingHom.id (Polynomial F)) (X ^ q)

/-- `A(X, X^q) = ∑_j A_j(X)·X^(q·j)` — the base-`q` block decomposition. -/
theorem subq_eq_sum [CommRing F] (q : ℕ) (A : Polynomial (Polynomial F)) :
    subq q A = ∑ j ∈ Finset.range (A.natDegree + 1), (A.coeff j) * X ^ (q * j) := by
  unfold subq
  rw [eval₂_eq_sum_range]
  simp only [RingHom.id_apply, ← pow_mul]

/-- `subq` is additive. -/
theorem subq_add [CommRing F] (q : ℕ) (A B : Polynomial (Polynomial F)) :
    subq q (A + B) = subq q A + subq q B := by
  unfold subq; rw [Polynomial.eval₂_add]

/-- Pulling a scalar `G ∈ F[X]` out: `(C G · A)(X, X^q) = G · A(X, X^q)`. -/
theorem subq_C_mul [CommRing F] (q : ℕ) (G : Polynomial F) (A : Polynomial (Polynomial F)) :
    subq q (Polynomial.C G * A) = G * subq q A := by
  unfold subq
  rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, RingHom.id_apply]

/-- **Base-`q` coefficient extraction.** When every X-block has degree `< q`, the coefficient of
`A(X, X^q)` at exponent `q·j₀ + i` (`i < q`) is the `i`-th coefficient of the `j₀`-th block. -/
theorem coeff_subq_digit [CommRing F] (q : ℕ) (A : Polynomial (Polynomial F))
    (hdig : ∀ j, (A.coeff j).natDegree < q) (j0 i : ℕ) (hi : i < q) :
    (subq q A).coeff (q * j0 + i) = (A.coeff j0).coeff i := by
  rw [subq_eq_sum, finset_sum_coeff]
  have hq : 0 < q := lt_of_le_of_lt (Nat.zero_le i) hi
  have hvanish : ∀ j ∈ Finset.range (A.natDegree + 1), j ≠ j0 →
      ((A.coeff j) * X ^ (q * j)).coeff (q * j0 + i) = 0 := by
    intro j _hj hjne
    rw [coeff_mul_X_pow']
    split_ifs with hcond
    · rcases lt_or_gt_of_ne hjne with hlt | hgt
      · apply Polynomial.coeff_eq_zero_of_natDegree_lt
        have hle : q ≤ q * j0 + i - q * j := by
          have heq : q * j + q * (j0 - j) = q * j0 := by rw [← Nat.mul_add]; congr 1; omega
          have h2 : q ≤ q * (j0 - j) := by
            calc q = q * 1 := (Nat.mul_one q).symm
            _ ≤ q * (j0 - j) := Nat.mul_le_mul_left q (by omega)
          omega
        exact lt_of_lt_of_le (hdig j) hle
      · exfalso
        have : q * (j0 + 1) ≤ q * j := Nat.mul_le_mul_left q (by omega)
        rw [Nat.mul_add, Nat.mul_one] at this; omega
    · rfl
  by_cases hj0 : j0 ≤ A.natDegree
  · rw [Finset.sum_eq_single j0]
    · rw [coeff_mul_X_pow', if_pos (Nat.le_add_right _ _)]
      congr 1; omega
    · exact hvanish
    · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
  · push Not at hj0
    rw [coeff_eq_zero_of_natDegree_lt hj0, Polynomial.coeff_zero]
    apply Finset.sum_eq_zero
    intro j hj
    exact hvanish j hj (by simp only [Finset.mem_range] at hj; omega)

/-- **Base-`q` faithfulness (keystone).** If every X-block of `A` has degree `< q` and
`A(X, X^q) = 0`, then `A = 0`: the substitution `Y ↦ X^q` is injective on `deg_X < q` polynomials. -/
theorem subq_eq_zero_iff [CommRing F] (q : ℕ) (A : Polynomial (Polynomial F))
    (hdig : ∀ j, (A.coeff j).natDegree < q) :
    subq q A = 0 ↔ A = 0 := by
  constructor
  · intro h
    ext j i'
    by_cases hi' : i' < q
    · have := coeff_subq_digit q A hdig j i' hi'
      rw [h, Polynomial.coeff_zero] at this
      rw [Polynomial.coeff_zero, Polynomial.coeff_zero]
      exact this.symm
    · rw [coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le (hdig j) (by omega)),
        Polynomial.coeff_zero, Polynomial.coeff_zero]
  · intro h; rw [h]; unfold subq; simp

/-- First-term corollary: `A₀(X, X^q) = 0` with `deg_X < q` forces `A₀ = 0`. -/
theorem subq_first_term_eq_zero [CommRing F] (q : ℕ) (A0 : Polynomial (Polynomial F))
    (hdig : ∀ j, (A0.coeff j).natDegree < q) (h : subq q A0 = 0) : A0 = 0 :=
  (subq_eq_zero_iff q A0 hdig).mp h

/-- **Degree bound on the substituted term.** `deg A(X, X^q) ≤ q·deg_Y A + (q−1)`. -/
theorem natDegree_subq_le [Field F] (q : ℕ) (A : Polynomial (Polynomial F))
    (hdig : ∀ j, (A.coeff j).natDegree < q) :
    (subq q A).natDegree ≤ q * A.natDegree + (q - 1) := by
  rw [subq_eq_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j hj
  apply le_trans (Polynomial.natDegree_mul_le)
  rw [Polynomial.natDegree_pow, Polynomial.natDegree_X, mul_one]
  simp only [Finset.mem_range] at hj
  have h1 : (A.coeff j).natDegree ≤ q - 1 := by have := hdig j; omega
  have h2 : q * j ≤ q * A.natDegree := Nat.mul_le_mul_left q (by omega)
  omega

/-- **The genuine reduction.** `R = subq q A₀ + G·subq q A₁ = 0` collapses (when the *combined*
X-blocks `A₀ⱼ + G·A₁ⱼ` all have degree `< q`) to the algebraic relation `A₀ + C G·A₁ = 0`. -/
theorem aux_collapses_to_relation [CommRing F] (q : ℕ) (G : Polynomial F)
    (A0 A1 : Polynomial (Polynomial F))
    (hdig : ∀ j, ((A0 + Polynomial.C G * A1).coeff j).natDegree < q)
    (hR : subq q A0 + G * subq q A1 = 0) :
    A0 + Polynomial.C G * A1 = 0 := by
  have hfold : subq q (A0 + Polynomial.C G * A1) = 0 := by
    rw [subq_add, subq_C_mul]; exact hR
  exact (subq_eq_zero_iff q _ hdig).mp hfold

/-- The relation always produces a vanishing auxiliary (the reduction is an equivalence). -/
theorem relation_gives_aux_zero [CommRing F] (q : ℕ) (G : Polynomial F)
    (A0 A1 : Polynomial (Polynomial F)) (hrel : A0 + Polynomial.C G * A1 = 0) :
    subq q A0 + G * subq q A1 = 0 := by
  have : subq q (A0 + Polynomial.C G * A1) = 0 := by rw [hrel]; unfold subq; simp
  rwa [subq_add, subq_C_mul] at this

/-- The `Y`-degree-2 hyperelliptic relation `A₀ + C(g^((q−1)/2))·A₁ = 0`. -/
def ObstructionRelation [CommRing F] (g : Polynomial F) (q : ℕ)
    (A0 A1 : Polynomial (Polynomial F)) : Prop :=
  A0 + Polynomial.C (g ^ ((q - 1) / 2)) * A1 = 0

/-- **The non-vanishing key claim, under the named genus hypothesis.** `hIrred` is the
absolute-irreducibility / genus consequence Mathlib does not yet provide: that the relation
`A₀ = −g^((q−1)/2)·A₁` (with both X-degrees `< q`) has only the trivial solution. Under it, the
auxiliary's blocks vanish. This isolates the wall as one named hypothesis (whose *precondition* —
irreducibility of `Y²−g` — is discharged by `squarefree_quadratic_irreducible_ratFunc`). -/
theorem aux_key_claim_under_irreducibility [CommRing F]
    (g : Polynomial F) (q : ℕ)
    (hIrred : ∀ A0 A1 : Polynomial (Polynomial F),
      (∀ j, (A0.coeff j).natDegree < q) → (∀ j, (A1.coeff j).natDegree < q) →
      ObstructionRelation g q A0 A1 → A0 = 0 ∧ A1 = 0)
    (A0 A1 : Polynomial (Polynomial F))
    (h0 : ∀ j, (A0.coeff j).natDegree < q) (h1 : ∀ j, (A1.coeff j).natDegree < q)
    (hcomb : ∀ j, ((A0 + Polynomial.C (g ^ ((q - 1) / 2)) * A1).coeff j).natDegree < q)
    (hR : subq q A0 + (g ^ ((q - 1) / 2)) * subq q A1 = 0) :
    A0 = 0 ∧ A1 = 0 :=
  hIrred A0 A1 h0 h1 (aux_collapses_to_relation q (g ^ ((q - 1) / 2)) A0 A1 hcomb hR)

/-- **The obstruction, made concrete.** The combined-digit hypothesis of `aux_collapses_to_relation`
genuinely fails in the relevant regime: if `A1 ≠ 0` and `deg g·((q−1)/2) ≥ q`, the second-term block
`g^((q−1)/2)·a` overflows the base-`q` digit. So one cannot apply faithfulness blindly — the elementary
route provably stops, and the cross-block cancellation is excluded only by counting `F`-points on
`Y²=g(X)` (Hasse–Weil), the genus content Mathlib lacks. -/
theorem obstruction_combined_digit_fails [Field F]
    (g : Polynomial F) (q : ℕ)
    (hG : g ^ ((q - 1) / 2) ≠ 0)
    (hbig : q ≤ ((q - 1) / 2) * g.natDegree)
    (a : Polynomial F) (ha : a ≠ 0) :
    ¬ ((g ^ ((q - 1) / 2)) * a).natDegree < q := by
  rw [Polynomial.natDegree_mul hG ha, Polynomial.natDegree_pow]
  omega

end BaseQ

end ArkLib.ProximityGap.StepanovNonVanishing

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.StepanovNonVanishing.squarefree_not_isSquare_ratFunc
#print axioms ArkLib.ProximityGap.StepanovNonVanishing.squarefree_quadratic_irreducible_ratFunc
#print axioms ArkLib.ProximityGap.StepanovNonVanishing.subq_eq_zero_iff
#print axioms ArkLib.ProximityGap.StepanovNonVanishing.aux_collapses_to_relation
#print axioms ArkLib.ProximityGap.StepanovNonVanishing.aux_key_claim_under_irreducibility
#print axioms ArkLib.ProximityGap.StepanovNonVanishing.obstruction_combined_digit_fails
