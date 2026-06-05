/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# General mixed Hasse-derivative numerator coefficient (brick **L2b-general**)

This file extends the *concrete* trivariate Hasse-derivative coefficient of brick L2b
(`ArkLib.ToMathlib.HasseDerivNumeratorConcrete`, which delivered the `i₁ = 0` **line** case) to the
general `i₁ > 0` case: the **mixed** trivariate Hasse derivative `∆^{i₁}_X ∆^{Σλ}_Y R(x₀, α₀, Z)` of
the BCIKS20 Appendix-A.4 recursion (A.1), together with the proof that — once its honest App-A
`W`-divisibility input is supplied — it has the `W`-power-numerator form
`HasWPowerNumerator (A_{i₁,λ}) (d − δ − Σλ)` that brick L7's `betaRec`/`Bcoeff` interface consumes.

## What App.-A.4 needs and what is proven here

In App.-A.4 the Hasse-derivative coefficient that the β-recursion multiplies/sums is

```
  A_{i₁,λ} = (Σλ choose λ₁,…) · ∆^{i₁}_X ∆^{Σλ}_Y R(x₀, α₀, Z)  =  B_{i₁,λ} / W^{d − δ_{i₁,0} − Σλ}
```

with `α₀ = T/W ∈ 𝕃` the canonical root, `W = liftToFunctionField H.leadingCoeff`, `d = R.natDegree`,
`δ_{0,0} = 1` (else `0`), `Σλ` the size of the `Y`-Hasse-derivative, numerator `B_{i₁,λ} ∈ 𝒪`.
The `i₁ = 0` line was proven in full in `HasseDerivNumeratorConcrete`; here we name the **inner-`X`**
Hasse derivative (order `i₁`) that the general term applies *before* the `X`-specialization, prove its
degree-and-coefficient facts kernel-clean, and feed the two genuine inputs to the brick-L2b derivation
`genHasseCoeff_hasWPowerNumerator_of_clearing` (re-used from `HasseDerivNumeratorConcrete`).

The mixed-derivative numerator is

```
  genHasseDerivNumerPoly x₀ R i₁ σ
    := hasseDeriv σ (Bivariate.evalX (C x₀) (innerXHasse i₁ R))   : F[X][Y]
```

i.e. apply the inner-`X` Hasse derivative `∆^{i₁}_X` (coefficient-wise on the `Y`-layer, on the `X`
variable that is then specialized), specialize `X = x₀`, then take the outer-`Y` Hasse derivative
`∆^{σ}_Y`.  Evaluating this `F[X][Y]` at `α₀ = T/W` realizes `∆^{i₁}_X ∆^{σ}_Y R(x₀, α₀, Z)`.  This
strictly generalizes the line numerator: `genHasseDerivNumerPoly x₀ R 0 σ = hasseDerivYNumerPoly x₀ R σ`
(`hasseDeriv 0 = id`).

### What is proven (all kernel-clean, no `sorry`/`admit`/`axiom`/`native_decide`)

* `innerXHasse_coeff`, `innerXHasse_natDegree_le`, `innerXHasse_zero` — the inner-`X` Hasse derivative
  acts coefficient-wise on the `Y`-layer (`(innerXHasse i₁ p).coeff n = hasseDeriv i₁ (p.coeff n)`),
  does not raise the `Y`-degree, and reduces to the identity at order `0`.
* `genHasseDerivNumerPoly_natDegree_le` — the `Y`-degree bound `d − σ` after the mixed derivative
  (both variables handled by mathlib `Polynomial.natDegree_hasseDeriv_le`).
* `genHasseDerivNumerPoly_coeff_top` — the relevant cleared coefficient at index `d − σ` equals
  `(d choose σ) · evalX(x₀)(∆^{i₁}_X R).coeff d`, exposing the single `W`-divisibility obligation.
* `genHasseDerivNumerPoly_eq_line_of_zero` — the `i₁ = 0` reduction to the verified line numerator.
* `genHasseCoeff` — the concrete general coefficient `A_{i₁,σ} ∈ 𝕃` (single-block multinomial `= 1`).
* `genHasseCoeff_hasWPowerNumerator_of_dvd_top` — **the general `W`-power-numerator theorem**: given the
  one genuine App-A divisibility input (`W ∣` the inner-`X`-derived top `Y`-coefficient — the
  `W^{i₁+δ}` prefactor save of recursion (A.1)), it produces `HasWPowerNumerator (A_{i₁,σ}) (d−σ−1)`.
* `genHasseCoeff_mem_regularElms_set_of_dvd` / `genHasseCoeff_mem_regularElms_set` — the L7-facing
  `hA`/`Bcoeff` composition, threading the recursion's `𝒪`-side divisibility witness to land in `𝒪`.

### Residual hypothesis (isolated, NOT a sorry)

The single residual is the App-A `W`-divisibility of the inner-`X`-derived top `Y`-coefficient
`hdvd_top : H.leadingCoeff ∣ (Bivariate.evalX (C x₀) (innerXHasse i₁ R)).coeff R.natDegree`.  In the
`i₁ = 0` line case this is *exactly* `Hypotheses.leadingCoeff_dvd_evalX_coeff_natDegree` (so the line
theorem `lineHasseCoeff_hasWPowerNumerator` is recovered with the hypothesis discharged from
`Hypotheses`, see `genHasseCoeff_zero_hasWPowerNumerator`).  For `i₁ > 0` it is the genuine
trivariate content (the `W^{i₁+δ}·ξ^{2i₁+Σλ−2}` prefactor of (A.1)); we take it as an explicit named
hypothesis rather than a `sorry`.

This file does **not** edit any existing file.  All names live in `namespace ArkLib`.
-/

import ArkLib.ToMathlib.HasseDerivNumeratorConcrete
import ArkLib.ToMathlib.HasseDerivNumerators
import ArkLib.Data.Polynomial.RationalFunctions
import Mathlib

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2

namespace ArkLib

variable {F : Type} [Field F]

/-! ### The inner-`X` Hasse derivative (coefficient-wise on the `Y`-layer)

`R : F[X][X][Y]` is `((F[X])[X])[Y]`: its `Y`-coefficients live in `(F[X])[X]`, whose `X` variable is
the one specialized by `Bivariate.evalX (C x₀)`.  The inner-`X` Hasse derivative `∆^{i₁}_X` of (A.1)
acts on *that* `X` variable, i.e. coefficient-wise (in the `Y`-layer) by `hasseDeriv i₁` on each
`(F[X])[X]`-coefficient.  We name it generically over a commutative semiring `S` (instantiated at
`S = F[X]`) so the coefficient/degree lemmas are the plain mathlib `Polynomial` facts. -/

/-- The order-`i₁` inner-`X` Hasse derivative of a `Polynomial (Polynomial S) = S[X][Y]`, applied
coefficient-wise on the `Y`-layer to each `S[X]`-coefficient. -/
noncomputable def innerXHasse {S : Type} [CommSemiring S] (i₁ : ℕ)
    (p : Polynomial (Polynomial S)) : Polynomial (Polynomial S) :=
  p.sum (fun k c => Polynomial.monomial k (Polynomial.hasseDeriv i₁ c))

/-- The inner-`X` Hasse derivative acts coefficient-wise on the `Y`-layer:
`(∆^{i₁}_X p).coeff n = ∆^{i₁}_X (p.coeff n)`. -/
lemma innerXHasse_coeff {S : Type} [CommSemiring S] (i₁ : ℕ) (p : Polynomial (Polynomial S))
    (n : ℕ) :
    (innerXHasse i₁ p).coeff n = Polynomial.hasseDeriv i₁ (p.coeff n) := by
  unfold innerXHasse
  rw [Polynomial.sum_def, Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_monomial]
  rw [Finset.sum_ite_eq' p.support n (fun k => Polynomial.hasseDeriv i₁ (p.coeff k))]
  by_cases hn : n ∈ p.support
  · simp [hn]
  · simp only [hn, if_false]
    rw [Polynomial.mem_support_iff, not_not] at hn
    rw [hn]; simp

/-- The inner-`X` Hasse derivative does not raise the `Y`-degree:
`natDegree (∆^{i₁}_X p) ≤ p.natDegree`. -/
lemma innerXHasse_natDegree_le {S : Type} [CommSemiring S] (i₁ : ℕ)
    (p : Polynomial (Polynomial S)) :
    (innerXHasse i₁ p).natDegree ≤ p.natDegree := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro m hm
  rw [innerXHasse_coeff, Polynomial.coeff_eq_zero_of_natDegree_lt hm]
  simp

/-- At order `0` the inner-`X` Hasse derivative is the identity (`hasseDeriv 0 = id`). -/
@[simp]
lemma innerXHasse_zero {S : Type} [CommSemiring S] (p : Polynomial (Polynomial S)) :
    innerXHasse 0 p = p := by
  unfold innerXHasse
  simp only [Polynomial.hasseDeriv_zero, LinearMap.id_coe, id_eq]
  exact Polynomial.sum_monomial_eq p

/-! ### The mixed (`i₁`-order inner-`X` + `σ`-order outer-`Y`) Hasse-derivative numerator polynomial

The order-`i₁` inner-`X` Hasse derivative, then `X`-specialization at `x₀`, then order-`σ` outer-`Y`
Hasse derivative of the GS factor `R`.  Evaluating this `F[X][Y]` at `α₀ = T/W` realizes
`∆^{i₁}_X ∆^{σ}_Y R(x₀, α₀, Z)` — the general term of recursion (A.1). -/

/-- The general mixed Hasse-derivative numerator polynomial `∆^{σ}_Y (∆^{i₁}_X R)(x₀,·,Z)` as a
`F[X][Y]`. -/
noncomputable def genHasseDerivNumerPoly (x₀ : F) (R : F[X][X][Y]) (i₁ σ : ℕ) : F[X][Y] :=
  Polynomial.hasseDeriv σ (Bivariate.evalX (Polynomial.C x₀) (innerXHasse i₁ R))

/-- The general numerator reduces to the verified line numerator at inner order `i₁ = 0`. -/
lemma genHasseDerivNumerPoly_eq_line_of_zero (x₀ : F) (R : F[X][X][Y]) (σ : ℕ) :
    genHasseDerivNumerPoly x₀ R 0 σ = hasseDerivYNumerPoly x₀ R σ := by
  unfold genHasseDerivNumerPoly hasseDerivYNumerPoly
  rw [innerXHasse_zero]

/-- The `Y`-degree of the mixed Hasse-derivative numerator drops by (at least) `σ`:
`natDegree (∆^σ_Y (∆^{i₁}_X R)(x₀,·,Z)) ≤ R.natDegree − σ`.  Both Hasse derivatives are bounded by
mathlib `Polynomial.natDegree_hasseDeriv_le`; the inner-`X` derivative and the `X`-specialization do
not raise the `Y`-degree. -/
lemma genHasseDerivNumerPoly_natDegree_le (x₀ : F) (R : F[X][X][Y]) (i₁ σ : ℕ) :
    (genHasseDerivNumerPoly x₀ R i₁ σ).natDegree ≤ R.natDegree - σ := by
  unfold genHasseDerivNumerPoly
  calc (Polynomial.hasseDeriv σ
          (Bivariate.evalX (Polynomial.C x₀) (innerXHasse i₁ R))).natDegree
      ≤ (Bivariate.evalX (Polynomial.C x₀) (innerXHasse i₁ R)).natDegree - σ :=
        Polynomial.natDegree_hasseDeriv_le _ σ
    _ ≤ R.natDegree - σ := by
        have hevalX : (Bivariate.evalX (Polynomial.C x₀) (innerXHasse i₁ R)).natDegree
            ≤ (innerXHasse i₁ R).natDegree := by
          rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
          intro n hn
          have hcoeff : (innerXHasse i₁ R).coeff n = 0 :=
            Polynomial.coeff_eq_zero_of_natDegree_lt hn
          simp [Bivariate.evalX_eq_map, Polynomial.coeff_map, hcoeff]
        have hinner : (innerXHasse i₁ R).natDegree ≤ R.natDegree := innerXHasse_natDegree_le i₁ R
        omega

/-- The relevant cleared coefficient of the mixed numerator, at the App-A index `R.natDegree − σ`:
`(∆^σ_Y (∆^{i₁}_X R)(x₀,·,Z)).coeff (R.natDegree − σ)
  = (R.natDegree choose σ) · (∆^{i₁}_X R)(x₀,·,Z).coeff R.natDegree`.
This exposes the single `W`-divisibility obligation: it suffices that `W` divides the inner-`X`-derived
top `Y`-coefficient `(Bivariate.evalX (C x₀) (∆^{i₁}_X R)).coeff R.natDegree`.  (For `i₁ = 0`,
`∆^{0}_X R = R`, and this is the line-case coefficient `Hypotheses` provides.) -/
lemma genHasseDerivNumerPoly_coeff_top (x₀ : F) (R : F[X][X][Y]) (i₁ σ : ℕ) (hσ : σ ≤ R.natDegree) :
    (genHasseDerivNumerPoly x₀ R i₁ σ).coeff (R.natDegree - σ) =
      ((R.natDegree).choose σ : F[X]) *
        (Bivariate.evalX (Polynomial.C x₀) (innerXHasse i₁ R)).coeff R.natDegree := by
  unfold genHasseDerivNumerPoly
  rw [Polynomial.hasseDeriv_coeff]
  have hsum : R.natDegree - σ + σ = R.natDegree := Nat.sub_add_cancel hσ
  rw [hsum]

/-! ### The general coefficient `A_{i₁,σ}` in `𝕃` and its `W`-power-numerator form -/

/-- The general mixed Hasse-derivative coefficient `A_{i₁,σ} = ∆^{i₁}_X ∆^σ_Y R(x₀, α₀, Z) ∈ 𝕃`,
obtained by evaluating the mixed numerator polynomial at the canonical root `α₀ = T/W`.  (The App-A
multinomial scalar for a single block `λ = (σ)` is `1`.) -/
noncomputable def genHasseCoeff (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [H_irreducible : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]
    (i₁ σ : ℕ) : 𝕃 H :=
  Polynomial.eval₂ liftToFunctionField
    (functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff)
    (genHasseDerivNumerPoly x₀ R i₁ σ)

/-- The general coefficient reduces to the verified line coefficient at inner order `i₁ = 0`. -/
lemma genHasseCoeff_eq_line_of_zero {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]}
    [H_irreducible : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]
    (σ : ℕ) :
    genHasseCoeff x₀ R H 0 σ = lineHasseCoeff x₀ R H σ := by
  unfold genHasseCoeff lineHasseCoeff
  rw [genHasseDerivNumerPoly_eq_line_of_zero]

/-- **Main general theorem.**  Given the one genuine App-A `W`-divisibility input — that `W`
(`= H.leadingCoeff`) divides the inner-`X`-derived top `Y`-coefficient (the `W^{i₁+δ}` prefactor save
of recursion (A.1)) — the general mixed Hasse-derivative coefficient `A_{i₁,σ}` has the
`W`-power-numerator form at the App-A exponent `d − δ − Σλ = R.natDegree − 1 − σ` (with `δ = 1`,
`Σλ = σ`):

  `HasWPowerNumerator (genHasseCoeff x₀ R H i₁ σ) (R.natDegree − σ − 1)`.

The natDegree bound (input (a) of `genHasseCoeff_hasWPowerNumerator_of_clearing`) is proven outright
via `genHasseDerivNumerPoly_natDegree_le`; the divisibility (input (b)) is the supplied `hdvd_top`,
routed through `genHasseDerivNumerPoly_coeff_top`.  Requires `σ + 1 ≤ R.natDegree` (the honest
boundary, as in the line case). -/
lemma genHasseCoeff_hasWPowerNumerator_of_dvd_top {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]}
    [H_irreducible : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]
    {i₁ σ : ℕ} (hσ : σ + 1 ≤ R.natDegree)
    (hdvd_top : H.leadingCoeff ∣
      (Bivariate.evalX (Polynomial.C x₀) (innerXHasse i₁ R)).coeff R.natDegree) :
    HasWPowerNumerator (genHasseCoeff x₀ R H i₁ σ) (R.natDegree - σ - 1) := by
  unfold genHasseCoeff
  set j := R.natDegree - σ - 1 with hj
  have hj1 : j + 1 = R.natDegree - σ := by omega
  refine genHasseCoeff_hasWPowerNumerator_of_clearing (j := j) ?_ ?_
  · -- natDegree bound: `natDegree (mixed numerator) ≤ R.natDegree - σ = j + 1`.
    rw [hj1]; exact genHasseDerivNumerPoly_natDegree_le x₀ R i₁ σ
  · -- `W ∣ (mixed numerator).coeff (j+1) = .coeff (R.natDegree - σ)`.
    rw [hj1, genHasseDerivNumerPoly_coeff_top x₀ R i₁ σ (by omega)]
    rcases hdvd_top with ⟨q, hq⟩
    exact ⟨((R.natDegree).choose σ : F[X]) * q, by rw [hq]; ring⟩

/-- **Line-case discharge.**  For `i₁ = 0` the residual divisibility input is *exactly*
`Hypotheses.leadingCoeff_dvd_evalX_coeff_natDegree`, so the general theorem recovers the verified line
result with the hypothesis discharged from `Hypotheses` (no residual): for `i₁ = 0`,
`HasWPowerNumerator (genHasseCoeff x₀ R H 0 σ) (R.natDegree − σ − 1)`. -/
lemma genHasseCoeff_zero_hasWPowerNumerator {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]}
    [H_irreducible : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) {σ : ℕ} (hσ : σ + 1 ≤ R.natDegree) :
    HasWPowerNumerator (genHasseCoeff x₀ R H 0 σ) (R.natDegree - σ - 1) := by
  refine genHasseCoeff_hasWPowerNumerator_of_dvd_top hσ ?_
  -- `∆^{0}_X R = R`, so the divisibility is the line-case one supplied by `Hypotheses`.
  rw [innerXHasse_zero]
  exact leadingCoeff_dvd_evalX_coeff_natDegree hHyp

/-! ### L7-facing composition (`hA` / `Bcoeff` interface)

L7's `betaRec_succ_mem_of_term_numerators` needs, per recursion term, the per-term `𝕃`-side numerator
form together with the `𝒪`-side divisibility witness the recursion supplies (its `W^{i₁+δ}·ξ^{…}`
prefactor).  We thread the concrete general `A_{i₁,σ}` numerator through L2's closure fact
`hasWPowerNumerator.mem_regularElms_set_of_dvd`. -/

/-- **L7 composition (raw).**  Given the `𝒪`-side divisibility witness `W_𝒪^{d−σ−1} ∣ B` for the
concrete general numerator `B` (the `𝒪`-element with `A_{i₁,σ} · W^{d−σ−1} = embedding B`), the
general coefficient `A_{i₁,σ}` is integral (`∈ regularElms_set H`).  This is the exact `hA`-shaped
fact L7's `betaRec_succ_mem_of_term_numerators` calls per term. -/
lemma genHasseCoeff_mem_regularElms_set_of_dvd {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]}
    [H_irreducible : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]
    {i₁ σ : ℕ} {B : 𝒪 H}
    (hB : genHasseCoeff x₀ R H i₁ σ * W_𝕃 H ^ (R.natDegree - σ - 1) = embeddingOf𝒪Into𝕃 H B)
    (hdvd : W_𝒪 H ^ (R.natDegree - σ - 1) ∣ B) :
    genHasseCoeff x₀ R H i₁ σ ∈ regularElms_set H :=
  hasWPowerNumerator.mem_regularElms_set_of_dvd hB hdvd

/-- **Fully packaged L7 entry point.**  The general coefficient *is* a `HasWPowerNumerator` (from the
main general theorem, given the App-A `W`-divisibility input `hdvd_top`), and given the recursion's
`𝒪`-side divisibility witness on its numerator it lands in `𝒪`.  This bundles the existence of the
numerator `B` with the membership closure, matching L7's `hA`/`Bcoeff` interface in one shot. -/
lemma genHasseCoeff_mem_regularElms_set {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]}
    [H_irreducible : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]
    {i₁ σ : ℕ} (hσ : σ + 1 ≤ R.natDegree)
    (hdvd_top : H.leadingCoeff ∣
      (Bivariate.evalX (Polynomial.C x₀) (innerXHasse i₁ R)).coeff R.natDegree)
    (hdvd : ∀ B : 𝒪 H,
      genHasseCoeff x₀ R H i₁ σ * W_𝕃 H ^ (R.natDegree - σ - 1) = embeddingOf𝒪Into𝕃 H B →
        W_𝒪 H ^ (R.natDegree - σ - 1) ∣ B) :
    genHasseCoeff x₀ R H i₁ σ ∈ regularElms_set H := by
  obtain ⟨B, hB⟩ := genHasseCoeff_hasWPowerNumerator_of_dvd_top hσ hdvd_top
  exact hasWPowerNumerator.mem_regularElms_set_of_dvd hB (hdvd B hB)

end ArkLib

-- Axiom audit: every claimed-done lemma must rest only on `[propext, Classical.choice, Quot.sound]`.
#print axioms ArkLib.innerXHasse_coeff
#print axioms ArkLib.innerXHasse_natDegree_le
#print axioms ArkLib.innerXHasse_zero
#print axioms ArkLib.genHasseDerivNumerPoly_eq_line_of_zero
#print axioms ArkLib.genHasseDerivNumerPoly_natDegree_le
#print axioms ArkLib.genHasseDerivNumerPoly_coeff_top
#print axioms ArkLib.genHasseCoeff_eq_line_of_zero
#print axioms ArkLib.genHasseCoeff_hasWPowerNumerator_of_dvd_top
#print axioms ArkLib.genHasseCoeff_zero_hasWPowerNumerator
#print axioms ArkLib.genHasseCoeff_mem_regularElms_set_of_dvd
#print axioms ArkLib.genHasseCoeff_mem_regularElms_set
