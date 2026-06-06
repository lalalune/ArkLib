/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.Polynomial.RationalFunctionsCore
import Mathlib

/-!
# `Λ`-weight calculus on the ring of regular elements `𝒪`

This file builds the arithmetic toolkit for the bivariate `Λ`-weight on the ring of regular
elements `𝒪 H` (`weight_Λ_over_𝒪`), as required by the App.-A.4 weight induction of [BCIKS20]
(brick **L3** of the proximity-prize DAG, feeding the Claim A.2 weight bound for the Hensel
numerators `β_t`).

The polynomial-level weight calculus already lives in
`ArkLib.Data.Polynomial.RationalFunctions` (`weight_Λ_add_le`, `weight_Λ_mul_le`,
`weight_Λ_sum_le`, …). Here we lift those facts across the quotient
`𝒪 H = F[X][X] ⧸ span {H_tilde' H}` using the workhorse `weight_Λ_over_𝒪_le_of_mk_eq`, and we
add the facts the App.-A.4 induction consumes:

* sub-additivity under `+`/`-`/`∑` (bound by `max`/`sup`),
* sub-multiplicativity under `*`/`^` (bound by `+`/`•`),
* the weights of `0`, `1`, scalar (`C`) and `W = liftToFunctionField H.leadingCoeff` multiples,
* monotonicity of the weight in the degree parameter `D`.

The weight is `WithBot ℕ`-valued; `⊥` (the weight of `0`) is the additive bottom and we are careful
to keep the bounds true in that algebra (e.g. the `max`/`+` bounds hold with `⊥` absorbed
correctly). No new `sorry`/`admit`/`axiom`/`native_decide`: every lemma below is kernel-clean and
reduces to the in-tree polynomial calculus.

All names live in `namespace ArkLib`; the in-tree objects are opened from
`BCIKS20AppendixA`. This file does **not** edit the (0-sorry) `RationalFunctions.lean`.
-/

namespace ArkLib

open Polynomial Polynomial.Bivariate BCIKS20AppendixA

variable {F : Type} [Field F]

/-! ### Reduction-invariant rephrasing of the canonical representative

`weight_Λ_over_𝒪 hH a D` is by definition `weight_Λ (canonicalRepOf𝒪 hH a) H D`, and the canonical
representative is the unique `mk`-preimage of `a` of degree `< deg (H_tilde' H)`. The key bridge
already proven in-tree is `weight_Λ_over_𝒪_le_of_mk_eq`: *any* representative bounds the weight.
We use it pervasively. -/

/-- The `𝒪`-weight of `a` is bounded by the polynomial weight of its own canonical representative
(in fact they are equal by definition); recorded as a `≤` for uniform downstream use. -/
lemma weight_Λ_over_𝒪_le_canonicalRep {H : F[X][Y]} (hH : 0 < H.natDegree)
    (a : 𝒪 H) (D : ℕ) :
    weight_Λ_over_𝒪 hH a D ≤ weight_Λ (canonicalRepOf𝒪 hH a) H D :=
  le_of_eq rfl

/-- The canonical representative is a `mk`-preimage of the element it represents, so it is a valid
witness for `weight_Λ_over_𝒪_le_of_mk_eq`. -/
lemma weight_Λ_over_𝒪_eq_canonicalRep {H : F[X][Y]} (hH : 0 < H.natDegree)
    (a : 𝒪 H) (D : ℕ) :
    weight_Λ_over_𝒪 hH a D = weight_Λ (canonicalRepOf𝒪 hH a) H D := rfl

/-! ### `0` and `1` -/

/-- The `𝒪`-weight of `0` is `⊥` (restated from the in-tree `weight_Λ_over_𝒪_zero`). -/
@[simp]
lemma weight_Λ_over_𝒪_zero' {H : F[X][Y]} (hH : 0 < H.natDegree) (D : ℕ) :
    weight_Λ_over_𝒪 hH (0 : 𝒪 H) D = ⊥ :=
  weight_Λ_over_𝒪_zero hH D

/-- The `𝒪`-weight of `1` is `≤ 0`: the constant `1` has a degree-`0` `F[X]`-coefficient and no
`Y`-power contribution. -/
lemma weight_Λ_over_𝒪_one_le {H : F[X][Y]} {D : ℕ}
    (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree) :
    weight_Λ_over_𝒪 hH (1 : 𝒪 H) D ≤ (0 : WithBot ℕ) := by
  -- `1 = mk (C 1)`, and `Λ (C 1) ≤ (C 1).natDegree = 0`.
  have hmk : (Ideal.Quotient.mk (Ideal.span {H_tilde' H}) (Polynomial.C 1 : F[X][Y]) : 𝒪 H)
      = (1 : 𝒪 H) := by
    rw [Polynomial.C_1, map_one]
  refine (weight_Λ_over_𝒪_le_of_mk_eq hD hH hmk).trans ?_
  refine (weight_Λ_C_le H D 1).trans ?_
  simp

/-! ### Additive sub-additivity

The weight of a sum is bounded by the `max` of the summands' weights. This is the `WithBot`-`max`
form (note `⊥` is the bottom, so `max` is the correct join). -/

/-- Sub-additivity of the `𝒪`-weight under addition: `Λ(a + b) ≤ max (Λ a) (Λ b)`. -/
lemma weight_Λ_over_𝒪_add_le {H : F[X][Y]} {D : ℕ}
    (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree) (a b : 𝒪 H) :
    weight_Λ_over_𝒪 hH (a + b) D ≤
      max (weight_Λ_over_𝒪 hH a D) (weight_Λ_over_𝒪 hH b D) := by
  classical
  -- Represent `a + b` by the *sum of canonical representatives*.
  set ra := canonicalRepOf𝒪 hH a with hra
  set rb := canonicalRepOf𝒪 hH b with hrb
  have hmk : (Ideal.Quotient.mk (Ideal.span {H_tilde' H}) (ra + rb) : 𝒪 H) = a + b := by
    rw [RingHom.map_add, hra, hrb, mk_canonicalRepOf𝒪, mk_canonicalRepOf𝒪]
  refine (weight_Λ_over_𝒪_le_of_mk_eq hD hH hmk).trans ?_
  refine (weight_Λ_add_le ra rb H D).trans ?_
  -- `weight_Λ ra = weight_Λ_over_𝒪 a` etc. by definition.
  exact le_of_eq (by rw [weight_Λ_over_𝒪_eq_canonicalRep, weight_Λ_over_𝒪_eq_canonicalRep])

/-- Sub-additivity of the `𝒪`-weight under negation: it is invariant. -/
@[simp]
lemma weight_Λ_over_𝒪_neg {H : F[X][Y]} {D : ℕ} (hH : 0 < H.natDegree) (a : 𝒪 H) :
    weight_Λ_over_𝒪 hH (-a) D = weight_Λ_over_𝒪 hH a D := by
  classical
  -- The canonical representative of `-a` is `-(canonicalRepOf𝒪 a)` (degree `< deg H_tilde'`).
  have hdeg : (-(canonicalRepOf𝒪 hH a)).degree < (H_tilde' H).degree := by
    rw [Polynomial.degree_neg]; exact canonicalRepOf𝒪_degree_lt hH a
  have hmk : (Ideal.Quotient.mk (Ideal.span {H_tilde' H}) (-(canonicalRepOf𝒪 hH a)) : 𝒪 H)
      = -a := by
    rw [RingHom.map_neg, mk_canonicalRepOf𝒪]
  rw [weight_Λ_over_𝒪_eq_canonicalRep (a := -a)]
  rw [show canonicalRepOf𝒪 hH (-a) = -(canonicalRepOf𝒪 hH a) by
        rw [← hmk] at *
        rw [canonicalRepOf𝒪_mk_eq_self_of_degree_lt hH hdeg]]
  rw [weight_Λ_neg, weight_Λ_over_𝒪_eq_canonicalRep]

/-- Sub-additivity of the `𝒪`-weight under subtraction: `Λ(a - b) ≤ max (Λ a) (Λ b)`. -/
lemma weight_Λ_over_𝒪_sub_le {H : F[X][Y]} {D : ℕ}
    (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree) (a b : 𝒪 H) :
    weight_Λ_over_𝒪 hH (a - b) D ≤
      max (weight_Λ_over_𝒪 hH a D) (weight_Λ_over_𝒪 hH b D) := by
  rw [sub_eq_add_neg]
  refine (weight_Λ_over_𝒪_add_le hD hH a (-b)).trans ?_
  rw [weight_Λ_over_𝒪_neg]

/-- The `𝒪`-weight of a finite sum is bounded by the `sup` of the summands' weights. -/
lemma weight_Λ_over_𝒪_sum_le {ι : Type} {H : F[X][Y]} {D : ℕ}
    (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    (s : Finset ι) (f : ι → 𝒪 H) :
    weight_Λ_over_𝒪 hH (∑ i ∈ s, f i) D ≤
      s.sup (fun i => weight_Λ_over_𝒪 hH (f i) D) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sup_insert]
      exact (weight_Λ_over_𝒪_add_le hD hH _ _).trans (max_le_max le_rfl ih)

/-! ### Multiplicative sub-multiplicativity

The weight of a product is bounded by the sum of weights. In `WithBot ℕ`, `⊥ + x = ⊥`, so the
bound is automatically correct when either factor is `0`. -/

/-- Sub-multiplicativity of the `𝒪`-weight: `Λ(a · b) ≤ Λ a + Λ b`. This is the central
inequality the App.-A.4 induction telescopes. -/
lemma weight_Λ_over_𝒪_mul_le {H : F[X][Y]} {D : ℕ}
    (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree) (a b : 𝒪 H) :
    weight_Λ_over_𝒪 hH (a * b) D ≤
      weight_Λ_over_𝒪 hH a D + weight_Λ_over_𝒪 hH b D := by
  classical
  set ra := canonicalRepOf𝒪 hH a with hra
  set rb := canonicalRepOf𝒪 hH b with hrb
  have hmk : (Ideal.Quotient.mk (Ideal.span {H_tilde' H}) (ra * rb) : 𝒪 H) = a * b := by
    rw [RingHom.map_mul, hra, hrb, mk_canonicalRepOf𝒪, mk_canonicalRepOf𝒪]
  refine (weight_Λ_over_𝒪_le_of_mk_eq hD hH hmk).trans ?_
  refine (weight_Λ_mul_le ra rb H D).trans ?_
  exact le_of_eq (by rw [weight_Λ_over_𝒪_eq_canonicalRep, weight_Λ_over_𝒪_eq_canonicalRep])

/-- Sub-multiplicativity for powers: `Λ(a ^ n) ≤ n • Λ a` (with `0 • Λ a = 0`, matching
`weight_Λ_over_𝒪_one_le`). -/
lemma weight_Λ_over_𝒪_pow_le {H : F[X][Y]} {D : ℕ}
    (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree) (a : 𝒪 H) (n : ℕ) :
    weight_Λ_over_𝒪 hH (a ^ n) D ≤ n • weight_Λ_over_𝒪 hH a D := by
  induction n with
  | zero =>
      simp only [pow_zero, zero_smul]
      exact weight_Λ_over_𝒪_one_le hD hH
  | succ n ih =>
      rw [pow_succ, succ_nsmul]
      refine (weight_Λ_over_𝒪_mul_le hD hH _ _).trans ?_
      exact add_le_add ih le_rfl

/-! ### Scalar (`C`) and `W`-multiples

The constants `F[X]` lift into `𝒪 H` as `mk ∘ C`; their weight is bounded by their `F[X]`-degree.
In particular `W = liftToFunctionField H.leadingCoeff` corresponds to the regular element
`mk (C H.leadingCoeff)`, whose weight is `≤ (H.leadingCoeff).natDegree ≤ D - d_H`. -/

/-- The `𝒪`-weight of the image of a scalar `C c` is bounded by `c.natDegree`. -/
lemma weight_Λ_over_𝒪_C_le {H : F[X][Y]} {D : ℕ}
    (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree) (c : F[X]) :
    weight_Λ_over_𝒪 hH
        (Ideal.Quotient.mk (Ideal.span {H_tilde' H}) (Polynomial.C c) : 𝒪 H) D ≤
      (WithBot.some c.natDegree : WithBot ℕ) := by
  refine (weight_Λ_over_𝒪_le_of_mk_eq hD hH (r := Polynomial.C c) rfl).trans ?_
  exact weight_Λ_C_le H D c

/-- A scalar multiple `mk (C c) * a` raises the weight by at most `c.natDegree`. -/
lemma weight_Λ_over_𝒪_C_mul_le {H : F[X][Y]} {D : ℕ}
    (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree) (c : F[X]) (a : 𝒪 H) :
    weight_Λ_over_𝒪 hH
        ((Ideal.Quotient.mk (Ideal.span {H_tilde' H}) (Polynomial.C c) : 𝒪 H) * a) D ≤
      (WithBot.some c.natDegree : WithBot ℕ) + weight_Λ_over_𝒪 hH a D := by
  refine (weight_Λ_over_𝒪_mul_le hD hH _ a).trans ?_
  exact add_le_add (weight_Λ_over_𝒪_C_le hD hH c) le_rfl

/-- The regular element `W = mk (C H.leadingCoeff)` realizing `liftToFunctionField H.leadingCoeff`.
This is the in-tree `W` of Claim A.2 as an element of `𝒪 H`. -/
noncomputable def W_reg (H : F[X][Y]) : 𝒪 H :=
  Ideal.Quotient.mk (Ideal.span {H_tilde' H}) (Polynomial.C H.leadingCoeff)

/-- `W_reg` indeed maps to `liftToFunctionField H.leadingCoeff = W` in `𝕃 H`. -/
lemma embeddingOf𝒪Into𝕃_W_reg (H : F[X][Y]) :
    embeddingOf𝒪Into𝕃 H (W_reg H) = liftToFunctionField (H := H) H.leadingCoeff := by
  rw [W_reg, embeddingOf𝒪Into𝕃_mk, liftBivariate_C]

/-- `Λ(W) ≤ D − d_H` (the `Λ(W)` bound of App.-A A.2): the weight of the regular `W` is bounded by
the `F[X]`-degree of the leading coefficient, which is `≤ D − d_H` under the total-degree bound. -/
lemma weight_Λ_over_𝒪_W_reg_le {H : F[X][Y]} {D : ℕ}
    (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree) :
    weight_Λ_over_𝒪 hH (W_reg H) D ≤
      (WithBot.some (D - H.natDegree) : WithBot ℕ) := by
  refine (weight_Λ_over_𝒪_C_le hD hH H.leadingCoeff).trans ?_
  rw [WithBot.coe_le_coe]
  -- `(H.leadingCoeff).natDegree = (H.coeff H.natDegree).natDegree ≤ D - H.natDegree`.
  have hlead : H.leadingCoeff = H.coeff H.natDegree := rfl
  rw [hlead]
  exact natDegree_coeff_le_of_totalDegree_le H hD H.natDegree

/-- A `W`-multiple `W_reg * a` raises the weight by at most `D − d_H`. -/
lemma weight_Λ_over_𝒪_W_reg_mul_le {H : F[X][Y]} {D : ℕ}
    (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree) (a : 𝒪 H) :
    weight_Λ_over_𝒪 hH (W_reg H * a) D ≤
      (WithBot.some (D - H.natDegree) : WithBot ℕ) + weight_Λ_over_𝒪 hH a D := by
  refine (weight_Λ_over_𝒪_mul_le hD hH _ a).trans ?_
  exact add_le_add (weight_Λ_over_𝒪_W_reg_le hD hH) le_rfl

/-! ### `T`-generator weight

`β_0 = T = mk X` in App.-A.4. Its weight is `Λ(X) = 1·(D + 1 − d_H)` (the `Y`-power contribution of
a single `Y`), giving the `weight(T) = (D + 1 − d_H)` base case of the induction. -/

/-- The `𝒪`-weight of the generator `T = mk X` is bounded by `D + 1 − d_H` (the single-`Y`-power
contribution). This is the `β_0` base case of the App.-A.4 weight induction. -/
lemma weight_Λ_over_𝒪_T_le {H : F[X][Y]} {D : ℕ}
    (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree) :
    weight_Λ_over_𝒪 hH
        (Ideal.Quotient.mk (Ideal.span {H_tilde' H}) (Polynomial.X : F[X][Y]) : 𝒪 H) D ≤
      (WithBot.some (D + 1 - Bivariate.natDegreeY H) : WithBot ℕ) := by
  refine (weight_Λ_over_𝒪_le_of_mk_eq hD hH (r := (Polynomial.X : F[X][Y])) rfl).trans ?_
  -- `Λ(X) = Λ(X^1) ≤ 1·(D + 1 − d_H)`.
  rw [show (Polynomial.X : F[X][Y]) = (Polynomial.X : F[X][Y]) ^ 1 from (pow_one _).symm]
  refine (weight_Λ_X_pow_le H D 1).trans ?_
  rw [WithBot.coe_le_coe, one_mul]

/-! ### Monotonicity in the degree parameter `D`

The per-`Y`-power contribution is `D + 1 − natDegreeY H`, monotone non-decreasing in `D` (truncated
subtraction). Hence the whole weight is monotone in `D`. This lets the induction relax `D` upward
when threading the `Λ(W) ≤ D − d_H`, `Λ(ξ) ≤ (d−1)(D − d_H + 1)` budgets. -/

/-- The polynomial `Λ`-weight is monotone non-decreasing in the degree parameter `D`. -/
lemma weight_Λ_mono_D {f H : F[X][Y]} {D D' : ℕ} (hDD : D ≤ D') :
    weight_Λ f H D ≤ weight_Λ f H D' := by
  classical
  refine Finset.sup_le (fun n hn => ?_)
  refine le_trans ?_ (le_weight_Λ_of_mem_support hn)
  rw [WithBot.coe_le_coe]
  have hm : D + 1 - Bivariate.natDegreeY H ≤ D' + 1 - Bivariate.natDegreeY H := by omega
  exact Nat.add_le_add_right (Nat.mul_le_mul_left n hm) _

/-- The `𝒪`-weight is monotone non-decreasing in the degree parameter `D`. -/
lemma weight_Λ_over_𝒪_mono_D {H : F[X][Y]} (hH : 0 < H.natDegree) (a : 𝒪 H)
    {D D' : ℕ} (hDD : D ≤ D') :
    weight_Λ_over_𝒪 hH a D ≤ weight_Λ_over_𝒪 hH a D' := by
  rw [weight_Λ_over_𝒪_eq_canonicalRep, weight_Λ_over_𝒪_eq_canonicalRep]
  exact weight_Λ_mono_D hDD

/-! ### Numeric `WithBot`-bound packaging for the induction

The App.-A.4 induction works with explicit `ℕ`-budgets `b` such that `Λ a ≤ (b : WithBot ℕ)`.
These helpers compose `+`/`max` of such budgets cleanly, keeping everything in `ℕ` and casting at
the boundary. They are the exact shape `weight_Λ_over_𝒪 hH (β_t) D ≤ (2t+1)·d_R·D` is proved in. -/

/-- If `Λ a ≤ (ba : WithBot ℕ)` and `Λ b ≤ (bb : WithBot ℕ)` then `Λ(a·b) ≤ (ba + bb : ℕ)`. -/
lemma weight_Λ_over_𝒪_mul_le_of_le {H : F[X][Y]} {D : ℕ}
    (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree) {a b : 𝒪 H} {ba bb : ℕ}
    (ha : weight_Λ_over_𝒪 hH a D ≤ (WithBot.some ba : WithBot ℕ))
    (hb : weight_Λ_over_𝒪 hH b D ≤ (WithBot.some bb : WithBot ℕ)) :
    weight_Λ_over_𝒪 hH (a * b) D ≤ (WithBot.some (ba + bb) : WithBot ℕ) := by
  refine (weight_Λ_over_𝒪_mul_le hD hH a b).trans ?_
  rw [WithBot.coe_add]
  exact add_le_add ha hb

/-- If `Λ a ≤ (ba : WithBot ℕ)` and `Λ b ≤ (bb : WithBot ℕ)` then `Λ(a + b) ≤ (max ba bb : ℕ)`. -/
lemma weight_Λ_over_𝒪_add_le_of_le {H : F[X][Y]} {D : ℕ}
    (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree) {a b : 𝒪 H} {ba bb : ℕ}
    (ha : weight_Λ_over_𝒪 hH a D ≤ (WithBot.some ba : WithBot ℕ))
    (hb : weight_Λ_over_𝒪 hH b D ≤ (WithBot.some bb : WithBot ℕ)) :
    weight_Λ_over_𝒪 hH (a + b) D ≤ (WithBot.some (max ba bb) : WithBot ℕ) := by
  refine (weight_Λ_over_𝒪_add_le hD hH a b).trans ?_
  rw [show (WithBot.some (max ba bb) : WithBot ℕ) =
        max (WithBot.some ba : WithBot ℕ) (WithBot.some bb) from WithBot.coe_max ba bb]
  exact max_le_max ha hb

/-- If `Λ a ≤ (b : WithBot ℕ)` then `Λ(a ^ n) ≤ (n · b : ℕ)`. -/
lemma weight_Λ_over_𝒪_pow_le_of_le {H : F[X][Y]} {D : ℕ}
    (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree) {a : 𝒪 H} {b : ℕ}
    (ha : weight_Λ_over_𝒪 hH a D ≤ (WithBot.some b : WithBot ℕ)) (n : ℕ) :
    weight_Λ_over_𝒪 hH (a ^ n) D ≤ (WithBot.some (n * b) : WithBot ℕ) := by
  induction n with
  | zero =>
      rw [pow_zero, Nat.zero_mul]
      refine (weight_Λ_over_𝒪_one_le hD hH).trans ?_
      norm_cast
  | succ n ih =>
      rw [pow_succ, Nat.succ_mul]
      exact weight_Λ_over_𝒪_mul_le_of_le hD hH ih ha

/-- The `(2t+1)·d_R·D` weight target of Claim A.2 as a `WithBot ℕ`-bound transfers along `≤`:
if a witness's weight is `≤` the tight `1 + (t+1)Λ(W) + e_t·Λ(ξ)` budget and that budget is `≤
(2t+1)·d_R·D`, the Claim A.2 bound holds. This is the `L10`-collapse shape. -/
lemma weight_Λ_over_𝒪_le_trans_nat {H : F[X][Y]} {D : ℕ} {a : 𝒪 H} {b c : ℕ}
    (hH : 0 < H.natDegree)
    (hab : weight_Λ_over_𝒪 hH a D ≤ (WithBot.some b : WithBot ℕ)) (hbc : b ≤ c) :
    weight_Λ_over_𝒪 hH a D ≤ (WithBot.some c : WithBot ℕ) :=
  hab.trans (WithBot.coe_le_coe.mpr hbc)

#print axioms weight_Λ_over_𝒪_mul_le
#print axioms weight_Λ_over_𝒪_add_le
#print axioms weight_Λ_over_𝒪_sub_le
#print axioms weight_Λ_over_𝒪_pow_le
#print axioms weight_Λ_over_𝒪_sum_le
#print axioms weight_Λ_over_𝒪_C_le
#print axioms weight_Λ_over_𝒪_C_mul_le
#print axioms weight_Λ_over_𝒪_W_reg_le
#print axioms weight_Λ_over_𝒪_W_reg_mul_le
#print axioms embeddingOf𝒪Into𝕃_W_reg
#print axioms weight_Λ_over_𝒪_T_le
#print axioms weight_Λ_mono_D
#print axioms weight_Λ_over_𝒪_mono_D
#print axioms weight_Λ_over_𝒪_one_le
#print axioms weight_Λ_over_𝒪_neg
#print axioms weight_Λ_over_𝒪_mul_le_of_le
#print axioms weight_Λ_over_𝒪_add_le_of_le
#print axioms weight_Λ_over_𝒪_pow_le_of_le
#print axioms weight_Λ_over_𝒪_le_trans_nat

end ArkLib
