/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic

/-!
# Common-root polynomial carriers for the composed MCA sources

For an actual finite set `Z` of common roots, `locator Z` is the monic product
of its linear factors. For an arbitrary seed polynomial `W`, the carrier is
`p = B * W.comp (X ^ s)` and its second component is `q = X * p`.

This file proves the exact locator degree and zero set, the carrier evaluation
and equality formulas, and degree bounds for seeds of degree at most three or
seven. The bounds include the zero seed and require no interpolant or
production-sized polynomial expansion. They are generic polynomial facts;
no received word, direction count, or final MCA theorem is asserted here.

Validation status at creation: Lean source awaiting CI. No local Lean runtime
or mathlib cache was available when the source was written.
-/

set_option autoImplicit false

noncomputable section
namespace AstraMcaScaledPolynomials
open Polynomial
open scoped BigOperators

variable {F : Type*} [Field F]

/-- The actual monic split polynomial supported on a finite set of roots. -/
def locator (Z : Finset F) : F[X] := ∏ z ∈ Z, (X - C z)

/-- The first polynomial component of a composed, commonly scaled source. -/
def scaledP (B W : F[X]) (s : ℕ) : F[X] := B * W.comp (X ^ s)

/-- The second polynomial component, collinear with the first at each point. -/
def scaledQ (B W : F[X]) (s : ℕ) : F[X] := X * scaledP B W s

/-- The common-root polynomial is monic, including for the empty root set. -/
theorem locator_monic (Z : Finset F) : (locator Z).Monic := by
  simpa only [locator] using Polynomial.monic_prod_X_sub_C id Z

/-- The locator is never the zero polynomial. -/
theorem locator_ne_zero (Z : Finset F) : locator Z ≠ 0 := (locator_monic Z).ne_zero

/-- Each selected root consumes exactly one degree. -/
theorem locator_natDegree (Z : Finset F) : (locator Z).natDegree = Z.card := by
  classical
  unfold locator
  induction Z using Finset.induction_on with
  | empty => simp
  | @insert x Z hx ih =>
    have hne : (∏ z ∈ Z, (X - C z : F[X])) ≠ 0 :=
      (Polynomial.monic_prod_X_sub_C id Z).ne_zero
    rw [Finset.prod_insert hx, natDegree_mul (X_sub_C_ne_zero x) hne,
      natDegree_X_sub_C, ih, Finset.card_insert_of_notMem hx]
    omega

/-- Evaluation retains the actual field elements used as common roots. -/
theorem locator_eval (Z : Finset F) (x : F) :
    (locator Z).eval x = ∏ z ∈ Z, (x - z) := by
  simp [locator, eval_prod]

/-- The locator vanishes exactly at its selected roots. -/
theorem locator_eval_eq_zero_iff (Z : Finset F) (x : F) :
    (locator Z).eval x = 0 ↔ x ∈ Z := by
  classical
  rw [locator_eval, Finset.prod_eq_zero_iff]
  simp only [sub_eq_zero]
  constructor
  · rintro ⟨z, hz, hxz⟩
    exact hxz.symm ▸ hz
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- Outside the selected roots the common factor can be cancelled. -/
theorem locator_eval_ne_zero_iff (Z : Finset F) (x : F) :
    (locator Z).eval x ≠ 0 ↔ x ∉ Z := by
  exact not_congr (locator_eval_eq_zero_iff Z x)

/-- Exact evaluation of the first component through the power map. -/
@[simp] theorem scaledP_eval (B W : F[X]) (s : ℕ) (x : F) :
    (scaledP B W s).eval x = B.eval x * W.eval (x ^ s) := by
  simp [scaledP, eval_comp]

/-- The two component values lie on the line of slope `x`. -/
@[simp] theorem scaledQ_eval (B W : F[X]) (s : ℕ) (x : F) :
    (scaledQ B W s).eval x = x * (scaledP B W s).eval x := by
  simp [scaledQ]

/-- Carrier values on a specified power fiber. -/
theorem eval_on_fiber (B W : F[X]) (s : ℕ) (x t : F) (hx : x ^ s = t) :
    ((scaledP B W s).eval x, (scaledQ B W s).eval x) =
      (B.eval x * W.eval t, x * (B.eval x * W.eval t)) := by
  simp [hx]

/-- Every source pair vanishes simultaneously at a selected common root. -/
theorem eval_at_common_root (Z : Finset F) (W : F[X]) (s : ℕ) (x : F)
    (hx : x ∈ Z) :
    (scaledP (locator Z) W s).eval x = 0 ∧
      (scaledQ (locator Z) W s).eval x = 0 := by
  have hz := (locator_eval_eq_zero_iff Z x).mpr hx
  simp [hz]

/-- Equality of first components is exactly equality of seed values whenever
the common factor does not vanish. -/
theorem scaledP_eval_eq_iff (B U V : F[X]) (s : ℕ) (x : F)
    (hB : B.eval x ≠ 0) :
    (scaledP B U s).eval x = (scaledP B V s).eval x ↔
      U.eval (x ^ s) = V.eval (x ^ s) := by
  simp only [scaledP_eval]
  exact ⟨mul_left_cancel₀ hB, congrArg (B.eval x * ·)⟩

/-- At a nonzero domain point, equality of second components has the same
seed equality test. -/
theorem scaledQ_eval_eq_iff (B U V : F[X]) (s : ℕ) (x : F)
    (hx : x ≠ 0) (hB : B.eval x ≠ 0) :
    (scaledQ B U s).eval x = (scaledQ B V s).eval x ↔
      U.eval (x ^ s) = V.eval (x ^ s) := by
  rw [scaledQ_eval, scaledQ_eval]
  constructor
  · intro he
    exact (scaledP_eval_eq_iff B U V s x hB).mp (mul_left_cancel₀ hx he)
  · intro he
    exact congrArg (x * ·) ((scaledP_eval_eq_iff B U V s x hB).mpr he)

/-- Equality of the complete local pair is already determined by its first
component, even at zero or at a common root. -/
theorem local_pair_eq_iff_first (B U V : F[X]) (s : ℕ) (x : F) :
    ((scaledP B U s).eval x, (scaledQ B U s).eval x) =
        ((scaledP B V s).eval x, (scaledQ B V s).eval x) ↔
      (scaledP B U s).eval x = (scaledP B V s).eval x := by
  constructor
  · intro he
    exact congrArg Prod.fst he
  · intro he
    simp only [scaledQ_eval]
    rw [he]

/-- Common scaling and composition preserve the full seed equality classes
at every point outside the actual locator roots. -/
theorem local_pair_eq_iff (Z : Finset F) (U V : F[X]) (s : ℕ) (x : F)
    (hx : x ∉ Z) :
    ((scaledP (locator Z) U s).eval x, (scaledQ (locator Z) U s).eval x) =
        ((scaledP (locator Z) V s).eval x, (scaledQ (locator Z) V s).eval x) ↔
      U.eval (x ^ s) = V.eval (x ^ s) := by
  rw [local_pair_eq_iff_first]
  exact scaledP_eval_eq_iff (locator Z) U V s x
    ((locator_eval_ne_zero_iff Z x).mpr hx)

/-- The equality-class formula can be used directly with a fiber label. -/
theorem local_pair_eq_on_fiber_iff (Z : Finset F) (U V : F[X]) (s : ℕ)
    (x t : F) (hx : x ∉ Z) (hpow : x ^ s = t) :
    ((scaledP (locator Z) U s).eval x, (scaledQ (locator Z) U s).eval x) =
        ((scaledP (locator Z) V s).eval x, (scaledQ (locator Z) V s).eval x) ↔
      U.eval t = V.eval t := by
  simpa only [hpow] using local_pair_eq_iff Z U V s x hx

/-- If some seed value is nonzero, the simultaneous zeros of all carriers
are exactly the selected roots of the common factor. -/
theorem common_zero_iff_mem {I : Type*} (Z : Finset F) (W : I → F[X])
    (s : ℕ) (x : F) (hW : ∃ i, (W i).eval (x ^ s) ≠ 0) :
    (∀ i, (scaledP (locator Z) (W i) s).eval x = 0) ↔ x ∈ Z := by
  classical
  constructor
  · intro hall
    by_contra hx
    obtain ⟨i, hi⟩ := hW
    have hB := (locator_eval_ne_zero_iff Z x).mpr hx
    have hz := hall i
    rw [scaledP_eval] at hz
    exact hi ((mul_eq_zero.mp hz).resolve_left hB)
  · intro hx i
    exact (eval_at_common_root Z (W i) s x hx).1

/-- The reciprocal direction cancels every carrier value at a nonzero
coordinate. Nonowner residuals are supplied separately by the equality API. -/
theorem reciprocal_cancellation (B W : F[X]) (s : ℕ) (x : F) (hx : x ≠ 0) :
    (scaledP B W s).eval x + (-x⁻¹) * (scaledQ B W s).eval x = 0 := by
  rw [scaledQ_eval]
  calc
    (scaledP B W s).eval x + (-x⁻¹) * (x * (scaledP B W s).eval x) =
        (1 - x⁻¹ * x) * (scaledP B W s).eval x := by ring
    _ = 0 := by rw [inv_mul_cancel₀ hx]; simp

/-- Degree growth under scaling and composition; this also covers `W = 0`. -/
theorem scaledP_natDegree_le (B W : F[X]) (s : ℕ) :
    (scaledP B W s).natDegree ≤ B.natDegree + W.natDegree * s := by
  have hc : (W.comp (X ^ s)).natDegree ≤ W.natDegree * s := by
    calc
      (W.comp (X ^ s)).natDegree ≤ W.natDegree * (X ^ s : F[X]).natDegree :=
        natDegree_comp_le
      _ = W.natDegree * s := by rw [natDegree_X_pow]
  exact natDegree_mul_le.trans (Nat.add_le_add_left hc B.natDegree)

/-- Multiplication by `X` consumes at most one additional degree. -/
theorem scaledQ_natDegree_le (B W : F[X]) (s : ℕ) :
    (scaledQ B W s).natDegree ≤ B.natDegree + W.natDegree * s + 1 := by
  have hp := scaledP_natDegree_le B W s
  have hq : (scaledQ B W s).natDegree ≤ 1 + (scaledP B W s).natDegree := by
    simpa only [scaledQ, natDegree_X] using
      (natDegree_mul_le (p := (X : F[X])) (q := scaledP B W s))
  omega

/-- An abstract degree budget for an arbitrary common polynomial. -/
theorem scaled_degree_budget (B W : F[X]) (s r d : ℕ)
    (hB : B.natDegree ≤ r) (hW : W.natDegree ≤ d) :
    (scaledP B W s).natDegree ≤ r + d * s ∧
      (scaledQ B W s).natDegree ≤ r + d * s + 1 := by
  have hp := scaledP_natDegree_le B W s
  have hq := scaledQ_natDegree_le B W s
  have hm := Nat.mul_le_mul_right s hW
  omega

/-- The degree cost of an actual common-root set is exactly its cardinality. -/
theorem locator_degree_budget (Z : Finset F) (W : F[X]) (s d : ℕ)
    (hW : W.natDegree ≤ d) :
    (scaledP (locator Z) W s).natDegree ≤ Z.card + d * s ∧
      (scaledQ (locator Z) W s).natDegree ≤ Z.card + d * s + 1 := by
  exact scaled_degree_budget (locator Z) W s Z.card d
    (le_of_eq (locator_natDegree Z)) hW

/-- Degree-seven seeds with at most `s - 2` common roots fit dimensions
`8 * s`: the first component has degree at most `8 * s - 2`, and the second
has degree at most `8 * s - 1`. -/
theorem degree_seven_budget (Z : Finset F) (W : F[X]) (s : ℕ)
    (hs : 2 ≤ s) (hZ : Z.card ≤ s - 2) (hW : W.natDegree ≤ 7) :
    (scaledP (locator Z) W s).natDegree ≤ 8 * s - 2 ∧
      (scaledQ (locator Z) W s).natDegree ≤ 8 * s - 1 := by
  obtain ⟨hp, hq⟩ := locator_degree_budget Z W s 7 hW
  omega

/-- The corresponding degree budget for the existing cubic seed. -/
theorem degree_three_budget (Z : Finset F) (W : F[X]) (s : ℕ)
    (hs : 2 ≤ s) (hZ : Z.card ≤ s - 2) (hW : W.natDegree ≤ 3) :
    (scaledP (locator Z) W s).natDegree ≤ 4 * s - 2 ∧
      (scaledQ (locator Z) W s).natDegree ≤ 4 * s - 1 := by
  obtain ⟨hp, hq⟩ := locator_degree_budget Z W s 3 hW
  omega

#print axioms locator_natDegree
#print axioms locator_eval_eq_zero_iff
#print axioms scaledP_eval
#print axioms eval_on_fiber
#print axioms local_pair_eq_iff
#print axioms common_zero_iff_mem
#print axioms reciprocal_cancellation
#print axioms scaledP_natDegree_le
#print axioms scaledQ_natDegree_le
#print axioms degree_seven_budget
#print axioms degree_three_budget

end AstraMcaScaledPolynomials
