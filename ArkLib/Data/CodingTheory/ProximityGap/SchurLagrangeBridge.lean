/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.LinearAlgebra.Lagrange

/-!
# The Schur/Lagrange bridge (#407, GRIND THREAD T2)

The `z^k`-coefficient (= top coefficient, since `#S = k+1`) of the Lagrange interpolant of
the data `{(v i, (v i)^b)}_{i ∈ S}` over a `(k+1)`-subset `S` is the **divided difference of
the monomial `x^b`**:

  **`(interpolate S v (·^b)).coeff k = Σ_{i ∈ S} (v i)^b / ∏_{j ∈ S \ {i}} (v i − v j)`.**

This is a *character-sum-free*, *list-decoding-free* identity, derived purely from
`Lagrange.interpolate` and `leadingCoeff_basis`. The right-hand side is the classical
**complete homogeneous symmetric polynomial** `h_{b−k}(v_S)` (for `b ≥ k`), via the Schur /
Jacobi–Trudi divided-difference law `[x_{i_0},…,x_{i_k}] x^b = h_{b−k}(x_{i_0},…,x_{i_k})`.
The anchors proven here pin the first three Schur values:
`h_{<0} = 0` (`dividedDifferencePow_eq_zero_of_lt`), `h_0 = 1` (`dividedDifferencePow_eq_one`),
`h_1 = e_1 = Σ v_i` (`dividedDifferencePow_card_eq_sum`).

So the bad-α criterion of a two-monomial pencil `x^k + α x^b` (the Action–Orbit object) — bad
at agreement `k+1` ⟺ the deg-`<k` agreeing codeword has its `z^k`-coefficient cancelling the
pencil's — becomes the **vanishing of a Schur polynomial** `h_{b−k}(v_S) = 0`, i.e. the
elementary/complete-symmetric vanishing the unified open core `K` counts. This file lands the
exact coefficient identity (the general Schur bridge), generalising the special ladder-stack
identity `residual_ladder_schur` (which is the `b = k+1`/`h_1 = e_1` instance — matched here by
`dividedDifferencePow_card_eq_sum`).
-/

open Finset Polynomial

namespace ProximityGap.SchurLagrange

variable {F : Type*} [Field F] {ι : Type*} [DecidableEq ι]
variable {s : Finset ι} {v : ι → F}

/-- **Top-coefficient of a Lagrange interpolant = sum of weighted values.**
For an injective node map `v` on `s`, the coefficient of degree `#s − 1` of the interpolant of
`r` is `Σ_{i ∈ s} r i · (∏_{j ∈ s.erase i} (v i − v j))⁻¹`. This is the divided-difference /
top-coefficient identity, the substrate of the Schur bridge. -/
theorem interpolate_coeff_top (hvs : Set.InjOn v s) (r : ι → F) :
    (Lagrange.interpolate s v r).coeff (#s - 1)
      = ∑ i ∈ s, r i * (∏ j ∈ s.erase i, (v i - v j))⁻¹ := by
  rw [Lagrange.interpolate_apply, finset_sum_coeff]
  refine Finset.sum_congr rfl fun i hi => ?_
  -- the basis polynomial `Lagrange.basis s v i` has natDegree `#s − 1`, so the coeff at `#s − 1`
  -- is its leading coefficient
  rw [coeff_C_mul, ← Lagrange.natDegree_basis hvs hi, ← Polynomial.leadingCoeff,
    Lagrange.leadingCoeff_basis hvs hi]

/-- **The divided difference of `x^b` over the node set `s`** (the `0`-th divided-difference
operator applied to `x ↦ x^b`): `[s] x^b := Σ_{i ∈ s} (v i)^b / ∏_{j ∈ s.erase i} (v i − v j)`.
By `interpolate_coeff_top` (with `r i = (v i)^b`) this equals the top (`#s−1`) coefficient of the
Lagrange interpolant of the monomial data `{(v i, (v i)^b)}_{i ∈ s}`. -/
noncomputable def dividedDifferencePow (s : Finset ι) (v : ι → F) (b : ℕ) : F :=
  ∑ i ∈ s, (v i) ^ b * (∏ j ∈ s.erase i, (v i - v j))⁻¹

/-- **The Schur/Lagrange bridge.** The `z^{#s−1}`-coefficient of the Lagrange interpolant of the
monomial data `{(v i, (v i)^b)}_{i ∈ s}` is the divided difference of `x^b` over `s`. With
`#s = k+1` this is the `z^k`-coefficient; for `b ≥ k` the divided difference is the complete
homogeneous symmetric polynomial `h_{b−k}(v_s)` (Schur / Jacobi–Trudi). This converts the
two-monomial bad-α criterion into Schur-vanishing — character-sum-free. -/
theorem interpolate_pow_coeff_top (hvs : Set.InjOn v s) (b : ℕ) :
    (Lagrange.interpolate s v (fun i => (v i) ^ b)).coeff (#s - 1)
      = dividedDifferencePow s v b :=
  interpolate_coeff_top hvs _

/-- **Bridge anchor, `b < #s − 1`: the divided difference vanishes** (= `h_{b−k}` with the
"negative degree" reading `b < k`). When `b < #s − 1` the monomial `x^b` already has degree
`< #s − 1`, so it is its own interpolant and its top coefficient is `0`. -/
theorem dividedDifferencePow_eq_zero_of_lt (hvs : Set.InjOn v s) {b : ℕ} (hb : b < #s - 1) :
    dividedDifferencePow s v b = 0 := by
  rw [← interpolate_pow_coeff_top hvs b]
  have hdeg : ((X : F[X]) ^ b).degree < #s := lt_of_le_of_lt (degree_X_pow_le b) (by
    have : (#s - 1 : ℕ) < #s := by omega
    exact_mod_cast lt_of_le_of_lt (by exact_mod_cast hb.le) (by exact_mod_cast this))
  have hinterp : Lagrange.interpolate s v (fun i => (v i) ^ b) = (X : F[X]) ^ b := by
    refine (Lagrange.eq_interpolate_of_eval_eq _ hvs hdeg fun i _ => ?_).symm
    simp
  rw [hinterp, coeff_X_pow]
  exact if_neg (by omega)

/-- **Bridge anchor, `b = #s − 1`: the divided difference is `1`** (= `h_0(v_s) = 1`). The
monomial `x^{#s−1}` is its own interpolant (degree `< #s`) and is monic, so its top coefficient
is `1`. -/
theorem dividedDifferencePow_eq_one (hvs : Set.InjOn v s) (hs : s.Nonempty) :
    dividedDifferencePow s v (#s - 1) = 1 := by
  rw [← interpolate_pow_coeff_top hvs (#s - 1)]
  have hdeg : ((X : F[X]) ^ (#s - 1)).degree < #s := by
    rw [degree_X_pow]
    have : (#s - 1 : ℕ) < #s := Nat.sub_lt (Finset.card_pos.mpr hs) one_pos
    exact_mod_cast this
  have hinterp : Lagrange.interpolate s v (fun i => (v i) ^ (#s - 1)) = (X : F[X]) ^ (#s - 1) := by
    refine (Lagrange.eq_interpolate_of_eval_eq _ hvs hdeg fun i _ => ?_).symm
    simp
  rw [hinterp, coeff_X_pow, if_pos rfl]

/-- **Bridge anchor, `b = #s`: the divided difference is the point sum `e_1(v_s) = h_1(v_s)`.**
This is the first nontrivial Schur value (`h_1 = e_1`) and the exact match to the in-tree
ladder law `residual_ladder_schur` (`e_t(x^{k+1}) = (Σ points) · e_t(x^k)`, here at the top
column). The divided difference of `x^{#s}` over a `#s`-set is `Σ_{i ∈ s} v i`. -/
theorem dividedDifferencePow_card_eq_sum (hvs : Set.InjOn v s) (hs : s.Nonempty) :
    dividedDifferencePow s v (#s) = ∑ i ∈ s, v i := by
  rw [← interpolate_pow_coeff_top hvs (#s)]
  set P : F[X] := ∏ i ∈ s, (X - C (v i)) with hP
  have hPmonic : P.Monic := monic_prod_of_monic _ _ fun i _ => monic_X_sub_C _
  have hPdeg : P.natDegree = #s := by
    rw [hP, natDegree_prod_of_monic _ _ fun i _ => monic_X_sub_C _]; simp
  -- `X^{#s} − P` has degree `< #s`: both are monic of degree `#s`, so the top terms cancel.
  set R : F[X] := (X : F[X]) ^ (#s) - P with hR
  have hXdeg : ((X : F[X]) ^ (#s)).degree = (#s : WithBot ℕ) := degree_X_pow _
  have hPdeg' : P.degree = (#s : WithBot ℕ) := by
    rw [degree_eq_natDegree hPmonic.ne_zero, hPdeg]
  have hRdeg : R.degree < #s := by
    rw [hR]
    refine lt_of_lt_of_le (degree_sub_lt ?_ (pow_ne_zero _ X_ne_zero) ?_) (le_of_eq hXdeg)
    · rw [hXdeg, hPdeg']
    · rw [(monic_X_pow (#s)).leadingCoeff, hPmonic.leadingCoeff]
  -- `R` agrees with `x^{#s}` on every node (since `P` vanishes there).
  have hinterp : Lagrange.interpolate s v (fun i => (v i) ^ (#s)) = R := by
    refine (Lagrange.eq_interpolate_of_eval_eq _ hvs hRdeg fun i hi => ?_).symm
    have hPz : P.eval (v i) = 0 := by
      rw [hP, eval_prod]
      exact Finset.prod_eq_zero hi (by simp)
    simp [hR, hPz]
  rw [hinterp, hR, coeff_sub, coeff_X_pow,
    if_neg (by have := Finset.card_pos.mpr hs; omega),
    show P.coeff (#s - 1) = -∑ i ∈ s, v i from by
      have h := prod_X_sub_C_coeff_card_pred s v (Finset.card_pos.mpr hs); simpa using h]
  ring

end ProximityGap.SchurLagrange

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.SchurLagrange.interpolate_coeff_top
#print axioms ProximityGap.SchurLagrange.interpolate_pow_coeff_top
#print axioms ProximityGap.SchurLagrange.dividedDifferencePow_eq_zero_of_lt
#print axioms ProximityGap.SchurLagrange.dividedDifferencePow_eq_one
#print axioms ProximityGap.SchurLagrange.dividedDifferencePow_card_eq_sum