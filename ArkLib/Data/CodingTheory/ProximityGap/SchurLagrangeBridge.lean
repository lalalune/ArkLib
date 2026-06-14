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

/-- **The general Schur recurrence (the `e ↔ h` / Newton engine of the bridge).**
The divided differences of the monomials `x^b` over a fixed node set `s` (`N := #s`) obey the
linear recurrence whose characteristic polynomial is `P = ∏_{i∈s}(X − v i)`: for every `b ≥ N`,

  `[s] x^b  =  − Σ_{m < N} P.coeff m · [s] x^{b − N + m}`.

Since `P.coeff m = (−1)^{N−m} e_{N−m}(v_s)`, this is exactly the elementary↔complete-homogeneous
relation `Σ_{j=0}^{N} (−1)^j e_j(v_s) · h_{d−j}(v_s) = 0`. Together with the anchors
(`dividedDifferencePow_eq_zero_of_lt` = `h_{<0}=0`, `dividedDifferencePow_eq_one` = `h_0=1`) it
pins **every** Schur value `h_{b−N+1}(v_s)`, character-sum-free — the engine driving the
two-monomial bad-α criterion `h_{b−k}(v_S) = 0`. The proof is purely the root identity
`(v i)^N = −Σ_{m<N} P.coeff m (v i)^m` (from `P(v i) = 0`, `P` monic of degree `N`), summed
against the divided-difference weights. -/
theorem dividedDifferencePow_recurrence (b : ℕ) (hb : #s ≤ b) :
    dividedDifferencePow s v b
      = - ∑ m ∈ range #s, (∏ i ∈ s, (X - C (v i))).coeff m
            * dividedDifferencePow s v (b - #s + m) := by
  classical
  set P : F[X] := ∏ i ∈ s, (X - C (v i)) with hP
  have hPmonic : P.Monic := monic_prod_of_monic _ _ fun i _ => monic_X_sub_C _
  have hPdeg : P.natDegree = #s := by
    rw [hP, natDegree_prod_of_monic _ _ fun i _ => monic_X_sub_C _]; simp
  have hcoeff_top : P.coeff (#s) = 1 := by rw [← hPdeg]; exact hPmonic.coeff_natDegree
  -- root identity: `(v i)^#s = − Σ_{m<#s} P.coeff m · (v i)^m` for every node.
  have hroot : ∀ i ∈ s, (v i) ^ #s = - ∑ m ∈ range #s, P.coeff m * (v i) ^ m := by
    intro i hi
    have hz : P.eval (v i) = 0 := by
      rw [hP, eval_prod]; exact Finset.prod_eq_zero hi (by simp)
    have hsum : P.eval (v i)
        = (∑ m ∈ range #s, P.coeff m * (v i) ^ m) + (v i) ^ #s := by
      rw [eval_eq_sum_range, hPdeg, Finset.sum_range_succ, hcoeff_top, one_mul]
    rw [hz] at hsum
    exact eq_neg_of_add_eq_zero_right hsum.symm
  -- per-node expansion of `(v i)^b`, then weight by `w i` and sum.
  have lhs_eq : ∀ i ∈ s,
      (v i) ^ b * (∏ j ∈ s.erase i, (v i - v j))⁻¹
        = - ∑ m ∈ range #s,
            P.coeff m * ((v i) ^ (b - #s + m) * (∏ j ∈ s.erase i, (v i - v j))⁻¹) := by
    intro i hi
    have hexp : (v i) ^ b = - ∑ m ∈ range #s, P.coeff m * (v i) ^ (b - #s + m) := by
      have h1 : (v i) ^ b = (v i) ^ (b - #s) * (v i) ^ (#s) := by
        rw [← pow_add, Nat.sub_add_cancel hb]
      rw [h1, hroot i hi, mul_neg, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun m _ => by ring
    rw [hexp, neg_mul, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun m _ => by ring
  calc dividedDifferencePow s v b
      = ∑ i ∈ s, - ∑ m ∈ range #s,
          P.coeff m * ((v i) ^ (b - #s + m) * (∏ j ∈ s.erase i, (v i - v j))⁻¹) := by
        rw [dividedDifferencePow]; exact Finset.sum_congr rfl lhs_eq
    _ = - ∑ i ∈ s, ∑ m ∈ range #s,
          P.coeff m * ((v i) ^ (b - #s + m) * (∏ j ∈ s.erase i, (v i - v j))⁻¹) := by
        rw [Finset.sum_neg_distrib]
    _ = - ∑ m ∈ range #s, ∑ i ∈ s,
          P.coeff m * ((v i) ^ (b - #s + m) * (∏ j ∈ s.erase i, (v i - v j))⁻¹) := by
        rw [Finset.sum_comm]
    _ = - ∑ m ∈ range #s, P.coeff m * dividedDifferencePow s v (b - #s + m) := by
        congr 1
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [dividedDifferencePow, Finset.mul_sum]


/-- **Bridge anchor, `b = #s + 1`: the second Schur value `h_2(v_s) = e_1² − e_2`.** A direct
corollary of `dividedDifferencePow_recurrence` + the three anchors: in the recurrence for
`b = #s+1` only the top two summands survive (`[s]x^{1+m} = 0` for `1+m < #s−1`), leaving
`[s]x^{#s+1} = −(P.coeff (#s−2) · h_0 + P.coeff (#s−1) · h_1)` with `h_0 = 1`, `h_1 = Σ v_i`,
`P.coeff (#s−1) = −Σ v_i`. Here `e_2 = P.coeff (#s−2)` (Vieta). This extends the Schur ledger
to the fourth value `h_2`, character-sum-free. -/
theorem dividedDifferencePow_card_add_one (hvs : Set.InjOn v s) (hs : 2 ≤ #s) :
    dividedDifferencePow s v (#s + 1)
      = (∑ i ∈ s, v i) ^ 2 - (∏ i ∈ s, (X - C (v i))).coeff (#s - 2) := by
  classical
  have hsne : s.Nonempty := Finset.card_pos.mp (by omega)
  set P : F[X] := ∏ i ∈ s, (X - C (v i)) with hP
  rw [dividedDifferencePow_recurrence (#s + 1) (by omega)]
  rw [← hP]
  -- the dd-index `(#s+1) - #s + m` is `1 + m`
  have hidx : ∀ m, (#s + 1) - #s + m = 1 + m := fun m => by omega
  simp only [hidx]
  -- peel the top two terms of `range #s = range ((#s-2)+1+1)`
  have hrw : (#s : ℕ) = (#s - 2) + 1 + 1 := by omega
  conv_lhs => rw [hrw]
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  -- the low block vanishes: for m < #s-2, `[s]x^{1+m} = 0`
  have hlow : ∀ m ∈ Finset.range (#s - 2),
      P.coeff m * dividedDifferencePow s v (1 + m) = 0 := by
    intro m hm
    have : dividedDifferencePow s v (1 + m) = 0 := by
      apply dividedDifferencePow_eq_zero_of_lt hvs
      have := Finset.mem_range.mp hm; omega
    rw [this, mul_zero]
  rw [Finset.sum_eq_zero hlow, zero_add]
  -- evaluate the two surviving anchors
  have h1 : (1 : ℕ) + (#s - 2) = #s - 1 := by omega
  have h2 : (1 : ℕ) + (#s - 2 + 1) = #s := by omega
  rw [h1, h2, dividedDifferencePow_eq_one hvs hsne,
      dividedDifferencePow_card_eq_sum hvs hsne, mul_one]
  -- `(#s-2)+1 = #s-1`, and `P.coeff (#s-1) = -Σ v_i`
  have hcard_pred : P.coeff (#s - 1) = - ∑ i ∈ s, v i := by
    have h := prod_X_sub_C_coeff_card_pred s v (Finset.card_pos.mpr hsne); simpa using h
  have hcc : (#s - 2 + 1) = #s - 1 := by omega
  rw [hcc, hcard_pred]
  ring


/-- **Bridge anchor, `b = #s + 2`: the third Schur value `h_3 = e_1³ − 2 e_1 e_2 + e_3`.**
The recurrence at `b = #s+2` leaves the top **three** summands (anchors `h_0=1`, `h_1=Σv_i`,
`h_2` = `dividedDifferencePow_card_add_one`); with `e_2 = P.coeff (#s−2)`, `e_3 = −P.coeff (#s−3)`,
`P.coeff (#s−1) = −Σv_i` this collapses to
`[s]x^{#s+2} = (Σv_i)³ − 2·(Σv_i)·P.coeff (#s−2) − P.coeff (#s−3)`.
Extends the character-sum-free Schur ledger to the fifth value `h_3`. -/
theorem dividedDifferencePow_card_add_two (hvs : Set.InjOn v s) (hs : 3 ≤ #s) :
    dividedDifferencePow s v (#s + 2)
      = (∑ i ∈ s, v i) ^ 3
        - 2 * (∑ i ∈ s, v i) * (∏ i ∈ s, (X - C (v i))).coeff (#s - 2)
        - (∏ i ∈ s, (X - C (v i))).coeff (#s - 3) := by
  classical
  have hsne : s.Nonempty := Finset.card_pos.mp (by omega)
  set P : F[X] := ∏ i ∈ s, (X - C (v i)) with hP
  rw [dividedDifferencePow_recurrence (#s + 2) (by omega), ← hP]
  have hidx : ∀ m, (#s + 2) - #s + m = 2 + m := fun m => by omega
  simp only [hidx]
  have hrw : (#s : ℕ) = (#s - 3) + 1 + 1 + 1 := by omega
  conv_lhs => rw [hrw]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
  -- low block vanishes
  have hlow : ∀ m ∈ Finset.range (#s - 3),
      P.coeff m * dividedDifferencePow s v (2 + m) = 0 := by
    intro m hm
    have : dividedDifferencePow s v (2 + m) = 0 := by
      apply dividedDifferencePow_eq_zero_of_lt hvs
      have := Finset.mem_range.mp hm; omega
    rw [this, mul_zero]
  rw [Finset.sum_eq_zero hlow, zero_add]
  -- normalise the dd-indices to the anchors
  have ha : (2 : ℕ) + (#s - 3) = #s - 1 := by omega
  have hb : (2 : ℕ) + (#s - 3 + 1) = #s := by omega
  have hc : (2 : ℕ) + (#s - 3 + 1 + 1) = #s + 1 := by omega
  rw [ha, hb, hc, dividedDifferencePow_eq_one hvs hsne,
      dividedDifferencePow_card_eq_sum hvs hsne,
      dividedDifferencePow_card_add_one hvs (by omega), mul_one]
  -- normalise the coeff-indices and use Vieta for P.coeff (#s-1)
  have hcc1 : (#s - 3 + 1) = #s - 2 := by omega
  have hcc2 : (#s - 3 + 1 + 1) = #s - 1 := by omega
  have hcard_pred : P.coeff (#s - 1) = - ∑ i ∈ s, v i := by
    have h := prod_X_sub_C_coeff_card_pred s v (Finset.card_pos.mpr hsne); simpa using h
  rw [hcc1, hcc2, hcard_pred]
  ring

end ProximityGap.SchurLagrange

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.SchurLagrange.interpolate_coeff_top
#print axioms ProximityGap.SchurLagrange.interpolate_pow_coeff_top
#print axioms ProximityGap.SchurLagrange.dividedDifferencePow_eq_zero_of_lt
#print axioms ProximityGap.SchurLagrange.dividedDifferencePow_eq_one
#print axioms ProximityGap.SchurLagrange.dividedDifferencePow_card_eq_sum
#print axioms ProximityGap.SchurLagrange.dividedDifferencePow_recurrence
#print axioms ProximityGap.SchurLagrange.dividedDifferencePow_card_add_one
#print axioms ProximityGap.SchurLagrange.dividedDifferencePow_card_add_two
