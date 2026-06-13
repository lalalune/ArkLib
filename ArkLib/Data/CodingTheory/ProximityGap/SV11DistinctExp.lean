/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SV11JetStructure
import ArkLib.Data.CodingTheory.ProximityGap.HasseMultiplicityBridge
import Mathlib.LinearAlgebra.Matrix.Nondegenerate

/-!
# The heart of SV11 Prop 3.2, reduced to the binomial determinant (#389)

The sharp `|R ∩ (R+c)| ≲ t^{2/3}` Stepanov bound uses the richer `DB²` generator family
`x^a·x^{tb₀}·(x−c)^{tb₁}`, whose linear independence (Shkredov–Vyugin Prop 3.2) is *not* a
distinct-degree statement (the `b₀+b₁` degrees collide) — so the distinct-degree non-vanishing
certificate does not cover it. SV11 prove it by a "factor out the minimal `(X−c)^t` power and recurse"
argument; the **base of each recursion step** is exactly:

> a polynomial `P = ∑ coef(i)·X^{m i}` with distinct exponents, divisible by `(X−c)^{#monomials}` and
> `c ≠ 0`, is zero.

This file proves that base case (`distinct_exp_dvd_eq_zero`) and, crucially, reduces it to the
**already-proven binomial determinant** `det_choose_ne_zero`: the `l` order-of-vanishing conditions at
`c` form a linear system `B ⬝ᵥ (coef(i)·c^{m i}) = 0` whose matrix `B = [C(mᵢ, k)]` is nonsingular
(distinct exponents in `F`), forcing the coefficients to vanish.

So the remaining input to the sharp split-case bound is **not a new wall**: its hard core reduces to a
binomial determinant that is already machine-checked in-tree. What remains is the (mechanical) recursion
wrapping this base case over the `b₁`-layers.

Axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

open Polynomial Finset Matrix

namespace ProximityGap.BinomialDet

variable {F : Type*} [Field F]

/-- **Distinct-exponent polynomial divisible by `(X−c)^{#monomials}` is zero.** If `P = ∑_{i<l}
coef(i)·X^{m i}` has its `l` exponents distinct in `F`, `c ≠ 0`, and `(X−c)^l ∣ P`, then every
`coef(i) = 0`. The `l` order-of-vanishing conditions at `c` form a binomial linear system whose matrix
is nonsingular by `det_choose_ne_zero` — this is the heart of the SV11 Prop 3.2 independence of the
`DB²` generator family (the remaining input to the sharp `O(t^{2/3})` bound), reduced to the already-
proven binomial determinant. -/
theorem distinct_exp_dvd_eq_zero {l : ℕ} (c : F) (hc : c ≠ 0) (m : Fin l → ℕ)
    (hinj : Function.Injective (fun i => (m i : F))) (coef : Fin l → F)
    (hdvd : (X - C c) ^ l ∣ ∑ i, Polynomial.C (coef i) * X ^ (m i)) :
    ∀ i, coef i = 0 := by
  classical
  set P : F[X] := ∑ i, Polynomial.C (coef i) * X ^ (m i) with hP
  -- the l vanishing conditions: ∀ k < l, (hasseDeriv k P).eval c = 0
  have hcond : ∀ k : Fin l, (hasseDeriv (k : ℕ) P).eval c = 0 := by
    intro k
    by_cases hP0 : P = 0
    · rw [hP0]; simp
    · have hrm : l ≤ P.rootMultiplicity c := (le_rootMultiplicity_iff hP0).mpr hdvd
      exact (ArkLib.CodingTheory.HasseMultiplicityBridge.le_rootMultiplicity_iff_hasseDeriv hP0 c l).mp
        hrm (k : ℕ) (k.isLt)
  -- expand each condition: (hasseDeriv k P).eval c = ∑_i coef i * C(m i, k) * c^(m i - k)
  have hexpand : ∀ k : Fin l,
      (hasseDeriv (k : ℕ) P).eval c
        = ∑ i, coef i * ((m i).choose (k : ℕ) : F) * c ^ (m i - (k : ℕ)) := by
    intro k
    rw [hP, map_sum, eval_finset_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← smul_eq_C_mul, map_smul, smul_eq_C_mul, eval_C_mul, hasseDeriv_X_pow_eval]
    ring
  -- the binomial matrix B (transpose of det_choose's matrix), nonsingular
  set B : Matrix (Fin l) (Fin l) F := Matrix.of (fun k i => ((m i).choose (k : ℕ) : F)) with hB
  have hdetB : B.det ≠ 0 := by
    have : B = (Matrix.of (fun i a : Fin l => ((m i).choose (a : ℕ) : F)))ᵀ := by
      ext k i; simp [hB, Matrix.transpose_apply, Matrix.of_apply]
    rw [this, Matrix.det_transpose]
    exact det_choose_ne_zero m hinj
  -- d i := coef i * c^(m i) is in the kernel of B
  set d : Fin l → F := fun i => coef i * c ^ (m i) with hd
  have hker : B *ᵥ d = 0 := by
    funext k
    simp only [Matrix.mulVec, dotProduct, hB, hd, Matrix.of_apply, Pi.zero_apply]
    -- ∑_i C(m i, k) * (coef i * c^(m i)) = c^k * (hasseDeriv k P).eval c = 0
    have hck : ∑ i, ((m i).choose (k : ℕ) : F) * (coef i * c ^ (m i))
        = c ^ (k : ℕ) * (hasseDeriv (k : ℕ) P).eval c := by
      rw [hexpand k, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rcases Nat.lt_or_ge (m i) (k : ℕ) with hlt | hle
      · rw [Nat.choose_eq_zero_of_lt hlt]; push_cast; ring
      · rw [show c ^ (m i) = c ^ (k : ℕ) * c ^ (m i - (k : ℕ)) by
          rw [← pow_add, Nat.add_sub_cancel' hle]]
        ring
    rw [hck, hcond k, mul_zero]
  -- B nonsingular ⟹ d = 0 ⟹ coef = 0
  have hd0 : d = 0 := Matrix.eq_zero_of_mulVec_eq_zero hdetB hker
  intro i
  have : coef i * c ^ (m i) = 0 := by have := congrFun hd0 i; simpa [hd] using this
  exact (mul_eq_zero.mp this).resolve_right (pow_ne_zero _ hc)

/-- **Layered independence (the SV11 Prop 3.2 recursion).** If `∑_{b<N} (X−c)^{tb}·P b = 0`, `c ≠ 0`,
`t ≥ 1`, and each `P b` has the base-case property `(X−c)^t ∣ P b → P b = 0` (which the distinct-exponent
layers satisfy via `distinct_exp_dvd_eq_zero`), then every `P b = 0`. Peel `b = 0`: `(X−c)^t ∣ P 0` so
`P 0 = 0`; cancel `(X−c)^t` and recurse on the shifted family. This is the recursion wrapping the
binomial-determinant base case into the full independence of the `DB²` generator family. -/
theorem layered_indep {N : ℕ} (c : F) (hc : c ≠ 0) (t : ℕ) (ht : 1 ≤ t) (P : ℕ → F[X])
    (hP : ∀ b, ((X - C c) ^ t ∣ P b) → P b = 0)
    (hsum : ∑ b ∈ Finset.range N, (X - C c) ^ (t * b) * P b = 0) :
    ∀ b ∈ Finset.range N, P b = 0 := by
  have hdne : ((X - C c) ^ t : F[X]) ≠ 0 := pow_ne_zero t (X_sub_C_ne_zero c)
  induction N generalizing P with
  | zero => intro b hb; simp at hb
  | succ N ih =>
    rw [Finset.sum_range_succ'] at hsum
    set R : F[X] := ∑ i ∈ Finset.range N, (X - C c) ^ (t * i) * P (i + 1) with hR
    have hfact : ∑ i ∈ Finset.range N, (X - C c) ^ (t * (i + 1)) * P (i + 1)
        = (X - C c) ^ t * R := by
      rw [hR, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Nat.mul_succ, pow_add]; ring
    rw [hfact, Nat.mul_zero, pow_zero, one_mul] at hsum
    -- hsum : (X-c)^t * R + P 0 = 0
    have hdvdP0 : (X - C c) ^ t ∣ P 0 := ⟨-R, by linear_combination hsum⟩
    have hP0 : P 0 = 0 := hP 0 hdvdP0
    have hR0 : R = 0 := by
      have : (X - C c) ^ t * R = 0 := by rw [hP0, add_zero] at hsum; exact hsum
      exact (mul_eq_zero.mp this).resolve_left hdne
    have hrec : ∀ b ∈ Finset.range N, P (b + 1) = 0 :=
      ih (fun b => P (b + 1)) (fun b => hP (b + 1)) hR0
    intro b hb
    rw [Finset.mem_range] at hb
    rcases Nat.eq_zero_or_pos b with hb0 | hbpos
    · rw [hb0]; exact hP0
    · obtain ⟨b', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hbpos.ne'
      exact hrec b' (Finset.mem_range.mpr (by omega))

end ProximityGap.BinomialDet

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.BinomialDet.distinct_exp_dvd_eq_zero
#print axioms ProximityGap.BinomialDet.layered_indep
