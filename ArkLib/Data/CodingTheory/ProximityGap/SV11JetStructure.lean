/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SV11GeneratorFamily
import Mathlib.Algebra.Polynomial.Taylor

/-!
# The order-`M` jet of the SV11 generator at a rep point (#389)

The sharp Garcia–Voloch / Heath-Brown–Konyagin Stepanov bound on `|R ∩ (R+c)|` needs the *order of
vanishing* of the Wronskian of the generators `g_{a,b}(X) = X^a (X−c)^{tb}` at the rep points, which
is governed by the rank of the **jet-evaluation map** `g ↦ (D_0 g(y), D_1 g(y), …, D_{M-1} g(y))`.

This file computes that jet exactly. Via Hasse–Leibniz (`hasseDeriv_mul`) and the two factor jets
(`hasseDeriv_X_pow_eval`, `hasseDeriv_X_sub_C_pow_eval` — the latter from `taylor_coeff` +
`coeff_X_add_C_pow`), at a rep point `(y−c)^t = 1`:

  `(y−c)^i · (D_i g_{a,b})(y) = ∑_{j+k=i} C(a,j)·C(tb,k)·y^{a−j}·(y−c)^j`   (`sv11Gen_hasseDeriv_eval_mul`).

The crucial structural fact this exposes: the `b`-dependence enters **only** through the binomials
`C(tb,k)` with `k ≤ i` — polynomials in `b` of degree `≤ i`. So across the `B` values of `b`, the
order-`M` jet map has `b`-rank `≤ M` (not `B`). This rank deficiency is exactly the "free" high-order
vanishing the Stepanov auxiliary exploits, and the input to the Wronskian degree-reduction giving the
sharp `O(n^{2/3})` exponent. Generalises the order-0 (`sv11Gen_eval_of_pow_eq_one`) and order-1
(`sv11Gen_deriv_eval_mul`) bricks to all orders.

Axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

open Polynomial Finset

namespace ProximityGap.BinomialDet

variable {F : Type*} [Field F]

/-- Hasse derivative of a shifted power, evaluated: `(D_k (X−c)^m)(y) = C(m,k)·(y−c)^{m−k}`. -/
theorem hasseDeriv_X_sub_C_pow_eval (c y : F) (m k : ℕ) :
    (hasseDeriv k ((X - C c) ^ m)).eval y = (m.choose k : F) * (y - c) ^ (m - k) := by
  rw [← Polynomial.taylor_coeff, Polynomial.taylor_apply, pow_comp, sub_comp, X_comp, C_comp,
    show (X + C y) - C c = X + C (y - c) by rw [map_sub]; ring, coeff_X_add_C_pow, mul_comm]

/-- Hasse derivative of `X^a`, evaluated: `(D_j X^a)(y) = C(a,j)·y^{a−j}`. -/
theorem hasseDeriv_X_pow_eval (y : F) (a j : ℕ) :
    (hasseDeriv j ((X : F[X]) ^ a)).eval y = (a.choose j : F) * y ^ (a - j) := by
  rw [X_pow_eq_monomial, hasseDeriv_monomial, mul_one, eval_monomial]

/-- **The general order-`i` jet of the SV11 generator at a rep point (Hasse–Leibniz).** At a rep
point `(y−c)^t = 1`,
`(y−c)^i · (D_i g_{a,b})(y) = ∑_{j+k=i} C(a,j)·C(tb,k)·y^{a−j}·(y−c)^j`.
The `b`-dependence enters only through the binomials `C(tb,k)` (polynomials in `b` of degree `k ≤ i`),
so the order-`M` jet map has `b`-rank `≤ M` — the structure governing the Wronskian's multiplicity at
rep points. Generalises the order-0 (`b`-collapse) and order-1 (`tb`-weighting) bricks. -/
theorem sv11Gen_hasseDeriv_eval_mul (c y : F) {t : ℕ} (a b i : ℕ) (h : (y - c) ^ t = 1) :
    (hasseDeriv i (sv11Gen c t (a, b))).eval y * (y - c) ^ i
      = ∑ p ∈ Finset.antidiagonal i,
          (a.choose p.1 : F) * ((t * b).choose p.2 : F) * y ^ (a - p.1) * (y - c) ^ p.1 := by
  have hpow : (y - c) ^ (t * b) = 1 := by rw [pow_mul, h, one_pow]
  unfold sv11Gen
  rw [hasseDeriv_mul, eval_finset_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.mem_antidiagonal] at hp
  rw [eval_mul, hasseDeriv_X_pow_eval, hasseDeriv_X_sub_C_pow_eval]
  rcases Nat.lt_or_ge (t * b) p.2 with hlt | hle
  · rw [Nat.choose_eq_zero_of_lt hlt]; push_cast; ring
  · have hpw : (y - c) ^ (t * b - p.2) * (y - c) ^ i = (y - c) ^ p.1 := by
      rw [← pow_add, show t * b - p.2 + i = t * b + p.1 by omega, pow_add, hpow, one_mul]
    calc (a.choose p.1 : F) * y ^ (a - p.1)
            * ((t * b).choose p.2 * (y - c) ^ (t * b - p.2)) * (y - c) ^ i
        = (a.choose p.1 : F) * ((t * b).choose p.2) * y ^ (a - p.1)
            * ((y - c) ^ (t * b - p.2) * (y - c) ^ i) := by ring
      _ = _ := by rw [hpw]

end ProximityGap.BinomialDet


-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.BinomialDet.hasseDeriv_X_sub_C_pow_eval
#print axioms ProximityGap.BinomialDet.sv11Gen_hasseDeriv_eval_mul
