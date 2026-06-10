/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.LamLeungTwoPow

/-!
# Fold branches of polynomial errors are coefficient slices (issue #232)

The branch-accounting program (DISPROOF_LOG O56–O59) tracks valued errors down the
2-adic tower via the even/odd folds `foldVal`/`foldValOdd`. This file proves that for a
**polynomial error** `e = f.eval` on a negation-closed domain (char ≠ 2, `0 ∉ D`), the
two branches are — up to the unit twist `y` — evaluations of the *coefficient slices*
of `f`:

* `eval_evenSlice` / `eval_oddSlice` — `f(x) + f(−x) = (evenSlice f)(x²)` and
  `f(x) − f(−x) = x·(oddSlice f)(x²)`, where `evenSlice f = contract 2 (f + f∘(−X))`
  collects the even-exponent coefficients (scaled by 2) and `oddSlice` the odd ones;
* `foldVal_polyeval` / `foldValOdd_polyeval` — `foldVal D f.eval (x₀²) = (evenSlice f)(x₀²)`
  and `foldValOdd D f.eval (x₀²) = x₀²·(oddSlice f)(x₀²)`;
* `foldVal_ne_zero_iff` / `foldValOdd_ne_zero_iff` — **branch aliveness = slice
  nonvanishing** (the twist drops out since `y ≠ 0`).

Since every valued error on a domain of size `n` interpolates to a unique polynomial of
degree `< n`, this translates the branch tree into plain coefficient combinatorics:
iterating, the depth-`ℓ` branches correspond to the residue classes of coefficient
exponents mod `2^ℓ` (under the ceiling-halving digit code: an odd fold maps exponent
`e ↦ (e+1)/2` because of the `y`-twist, an even fold maps `e ↦ e/2`), and a branch is
alive iff its class contains a nonzero coefficient — verified exhaustively at n = 16
(`scripts/probes/probe_fold_slices.py`). The open branch-count distribution question
(O59) is thereby the joint distribution of (evaluation weight, 2-adic coefficient
spread) over low-degree polynomials.
-/

namespace LamLeungTwoPow

open Polynomial Finset

variable {F : Type*} [Field F]

/-! Part 1: even/odd coefficient slices via expand/contract -/

theorem coeff_comp_neg_X (f : F[X]) (n : ℕ) :
    (f.comp (-X)).coeff n = (-1) ^ n * f.coeff n := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq => rw [add_comp, coeff_add, hp, hq, coeff_add]; ring
  | monomial k a =>
    have hC : ((-1 : F[X])) ^ k = C ((-1 : F) ^ k) := by
      rw [map_pow, map_neg, map_one]
    rw [monomial_comp, neg_pow, ← mul_assoc, hC, ← C_mul, coeff_C_mul, coeff_X_pow,
      coeff_monomial]
    by_cases h : n = k
    · subst h; simp [mul_comm]
    · simp [h, Ne.symm h]

theorem expand_contract_of_even_support {h : F[X]}
    (hodd : ∀ n, ¬ 2 ∣ n → h.coeff n = 0) :
    Polynomial.expand F 2 (Polynomial.contract 2 h) = h := by
  ext n
  rw [coeff_expand (by norm_num : 0 < 2)]
  by_cases hd : 2 ∣ n
  · rw [if_pos hd, coeff_contract (by norm_num : (2:ℕ) ≠ 0)]
    obtain ⟨m, rfl⟩ := hd
    rw [Nat.mul_div_cancel_left m (by norm_num : 0 < 2)]
    congr 1
    omega
  · rw [if_neg hd, hodd n hd]

/-- The even coefficient slice: `evenSlice f` collects the even-exponent coefficients,
scaled by 2 — `(evenSlice f).eval (x²) = f(x) + f(−x)`. -/
noncomputable def evenSlice (f : F[X]) : F[X] :=
  Polynomial.contract 2 (f + f.comp (-X))

/-- The odd coefficient slice: `(oddSlice f).eval (x²) · x = f(x) − f(−x)`. -/
noncomputable def oddSlice (f : F[X]) : F[X] :=
  Polynomial.contract 2 (Polynomial.divX (f - f.comp (-X)))

theorem eval_evenSlice (f : F[X]) (x : F) :
    (evenSlice f).eval (x ^ 2) = f.eval x + f.eval (-x) := by
  have hodd : ∀ n, ¬ 2 ∣ n → (f + f.comp (-X)).coeff n = 0 := by
    intro n hn
    rw [coeff_add, coeff_comp_neg_X]
    have hodd' : Odd n := Nat.odd_iff.mpr (by omega)
    rw [hodd'.neg_one_pow]
    ring
  have key := expand_contract_of_even_support hodd
  calc (evenSlice f).eval (x ^ 2)
      = (Polynomial.expand F 2 (evenSlice f)).eval x := by rw [expand_eval]
    _ = (f + f.comp (-X)).eval x := by rw [evenSlice, key]
    _ = f.eval x + f.eval (-x) := by
        rw [eval_add, eval_comp]
        simp

theorem eval_oddSlice (f : F[X]) (x : F) :
    x * (oddSlice f).eval (x ^ 2) = f.eval x - f.eval (-x) := by
  set h : F[X] := f - f.comp (-X) with hh
  have heven : ∀ n, ¬ 2 ∣ n → (Polynomial.divX h).coeff n = 0 := by
    intro n hn
    rw [coeff_divX, hh, coeff_sub, coeff_comp_neg_X]
    have hsucc : Even (n + 1) := Nat.even_add_one.mpr (by
      intro he
      exact hn (even_iff_two_dvd.mp he))
    rw [hsucc.neg_one_pow]
    ring
  have h0 : h.coeff 0 = 0 := by
    rw [hh, coeff_sub, coeff_comp_neg_X]
    ring
  have key := expand_contract_of_even_support heven
  have heval : h.eval x = (Polynomial.divX h).eval x * x := by
    conv_lhs => rw [← Polynomial.divX_mul_X_add h]
    rw [h0, map_zero, add_zero, eval_mul, eval_X]
  calc x * (oddSlice f).eval (x ^ 2)
      = x * (Polynomial.expand F 2 (oddSlice f)).eval x := by rw [expand_eval]
    _ = x * (Polynomial.divX h).eval x := by rw [oddSlice, key]
    _ = h.eval x := by rw [heval]; ring
    _ = f.eval x - f.eval (-x) := by rw [hh, eval_sub, eval_comp]; simp

/-! Part 2: the fold of a polynomial error IS the slice evaluation -/

variable [DecidableEq F]

/-- On a negation-closed domain avoiding 0 (char ≠ 2), the squaring fiber over `x₀²`
is exactly the antipodal pair. -/
theorem fiber_eq_pair {D : Finset F} (hneg : ∀ x ∈ D, -x ∈ D)
    {x₀ : F} (hx₀ : x₀ ∈ D) :
    D.filter (fun x => x ^ 2 = x₀ ^ 2) = {x₀, -x₀} := by
  apply Finset.Subset.antisymm
  · intro x hx
    have hxy : x ^ 2 = x₀ ^ 2 := (Finset.mem_filter.mp hx).2
    have hfac : (x - x₀) * (x + x₀) = 0 := by linear_combination hxy
    rcases mul_eq_zero.mp hfac with h | h
    · exact Finset.mem_insert.mpr (Or.inl (by linear_combination h))
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (by linear_combination h)))
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact Finset.mem_filter.mpr ⟨hx₀, rfl⟩
    · rw [Finset.mem_singleton.mp hx]
      exact Finset.mem_filter.mpr ⟨hneg x₀ hx₀, by ring⟩

/-- **The even fold of a polynomial error is the even coefficient slice.** -/
theorem foldVal_polyeval {D : Finset F} (hneg : ∀ x ∈ D, -x ∈ D) (h0 : (0 : F) ∉ D)
    (h2 : (2 : F) ≠ 0) (f : F[X]) {x₀ : F} (hx₀ : x₀ ∈ D) :
    foldVal D (fun x => f.eval x) (x₀ ^ 2) = (evenSlice f).eval (x₀ ^ 2) := by
  have hne : x₀ ≠ -x₀ := by
    intro hcontra
    apply h0
    have h2x : (2 : F) * x₀ = 0 := by linear_combination hcontra
    rcases mul_eq_zero.mp h2x with h | h
    · exact absurd h h2
    · rwa [← h]
  rw [foldVal, fiber_eq_pair hneg hx₀, Finset.sum_pair hne, eval_evenSlice]

/-- **The odd fold of a polynomial error is the odd coefficient slice, twisted by `y`.** -/
theorem foldValOdd_polyeval {D : Finset F} (hneg : ∀ x ∈ D, -x ∈ D) (h0 : (0 : F) ∉ D)
    (h2 : (2 : F) ≠ 0) (f : F[X]) {x₀ : F} (hx₀ : x₀ ∈ D) :
    foldValOdd D (fun x => f.eval x) (x₀ ^ 2) = x₀ ^ 2 * (oddSlice f).eval (x₀ ^ 2) := by
  have hne : x₀ ≠ -x₀ := by
    intro hcontra
    apply h0
    have h2x : (2 : F) * x₀ = 0 := by linear_combination hcontra
    rcases mul_eq_zero.mp h2x with h | h
    · exact absurd h h2
    · rwa [← h]
  rw [foldValOdd, fiber_eq_pair hneg hx₀, Finset.sum_pair hne]
  have hodd := eval_oddSlice f x₀
  calc f.eval x₀ * x₀ + f.eval (-x₀) * -x₀
      = x₀ * (f.eval x₀ - f.eval (-x₀)) := by ring
    _ = x₀ * (x₀ * (oddSlice f).eval (x₀ ^ 2)) := by rw [hodd]
    _ = x₀ ^ 2 * (oddSlice f).eval (x₀ ^ 2) := by ring

/-- **Branch aliveness = slice nonvanishing** (one level): the even branch is alive at
`y = x₀²` iff the even slice evaluates nonzero there; same for the odd branch (the unit
twist `y ≠ 0` drops out). -/
theorem foldVal_ne_zero_iff {D : Finset F} (hneg : ∀ x ∈ D, -x ∈ D) (h0 : (0 : F) ∉ D)
    (h2 : (2 : F) ≠ 0) (f : F[X]) {x₀ : F} (hx₀ : x₀ ∈ D) :
    foldVal D (fun x => f.eval x) (x₀ ^ 2) ≠ 0 ↔ (evenSlice f).eval (x₀ ^ 2) ≠ 0 := by
  rw [foldVal_polyeval hneg h0 h2 f hx₀]

theorem foldValOdd_ne_zero_iff {D : Finset F} (hneg : ∀ x ∈ D, -x ∈ D) (h0 : (0 : F) ∉ D)
    (h2 : (2 : F) ≠ 0) (f : F[X]) {x₀ : F} (hx₀ : x₀ ∈ D) :
    foldValOdd D (fun x => f.eval x) (x₀ ^ 2) ≠ 0 ↔ (oddSlice f).eval (x₀ ^ 2) ≠ 0 := by
  rw [foldValOdd_polyeval hneg h0 h2 f hx₀]
  have hx₀0 : x₀ ≠ 0 := fun h => h0 (h ▸ hx₀)
  constructor
  · intro hne hzero
    exact hne (by rw [hzero, mul_zero])
  · intro hne hzero
    exact hne (by
      rcases mul_eq_zero.mp hzero with h | h
      · exact absurd (pow_eq_zero_iff (by norm_num : 2 ≠ 0) |>.mp h) hx₀0
      · exact h)

end LamLeungTwoPow
