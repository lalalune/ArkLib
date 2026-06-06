/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Concrete Hasse-derivative numerator coefficient (brick **L2b**)

This file delivers the *concrete* trivariate Hasse-derivative coefficient that brick L2
(`ArkLib.ToMathlib.HasseDerivNumerators`) flagged as its residual: the actual `A_{i₁,λ}` of the
BCIKS20 Appendix-A.4 recursion (A.1), *named* in the in-tree `𝒪`/`𝕃` representation, together with
the proof that it has the `W`-power-numerator form `HasWPowerNumerator (A_{i₁,λ}) (d − δ − Σλ)` that
brick L7's `betaRec_mem` interface (`hA`) consumes.

## What App.-A.4 needs and what is proven here

In App.-A.4 the Hasse-derivative coefficient the β-recursion multiplies/sums is

```
  A_{i₁,λ} = (Σλ choose λ₁,…) · ∆^{i₁}_X ∆^{Σλ}_Y R(x₀, α₀, Z)  =  B_{i₁,λ} / W^{d − δ_{i₁,0} − Σλ}
```

with `α₀ = T/W ∈ 𝕃` the canonical root, `W = liftToFunctionField H.leadingCoeff`, `d = R.natDegree`,
`δ_{0,0} = 1` (else `0`), `Σλ` the size of the `Y`-Hasse-derivative, and the numerator `B_{i₁,λ} ∈ 𝒪`
(the *integral* subring).  The `W`-divisibility that lands `B` back in `𝒪` comes from the
`W^{i₁+δ}·ξ^{2i₁+Σλ−2}` prefactor of (A.1) — concretely (BCIKS20 App-A line ~2931) from the fact that
`W = H.leadingCoeff` divides the top `Y`-coefficient of `R(x₀,·,Z)` (`Hypotheses.dvd_evalX`).

We formalize the **`i₁ = 0` line case** in full, kernel-clean:

* `hasseDerivYNumerPoly x₀ R σ := Polynomial.hasseDeriv σ (Bivariate.evalX (C x₀) R)` — the order-`σ`
  (outer-`Y`) Hasse derivative of the `X`-specialization `R(x₀,·,Z)`, a `F[X][Y]` whose evaluation at
  `α₀ = T/W` is `∆^{0}_X ∆^{σ}_Y R(x₀, α₀, Z)`.
* `lineHasseCoeff x₀ R H σ := eval₂ liftToFunctionField (T/W) (hasseDerivYNumerPoly x₀ R σ) ∈ 𝕃` —
  the concrete `A_{0,σ}` (with the multinomial scalar `= 1` since `λ = (σ)` is a single block).
* **Main theorem** `lineHasseCoeff_hasWPowerNumerator`:
  `HasWPowerNumerator (lineHasseCoeff x₀ R H σ) (R.natDegree − σ − 1)`, i.e. the App-A exponent
  `d − δ − Σλ` with `δ = 1`, `Σλ = σ` for the `i₁ = 0` line.  Proven via the in-tree denominator-
  clearing machine `regularElms_set_mul_pow_eval₂_div_of_natDegree_le_succ_of_coeff_succ_dvd`, whose
  `W ∣ top-coeff` hypothesis is discharged from `Hypotheses` (the `leadingCoeff_dvd_evalX_*` "save").
* **Composition with L7** `lineHasseCoeff_mem_regularElms_set_of_dvd`: given the `𝒪`-side
  divisibility witness `W_𝒪^{d−σ−1} ∣ B` that L7's recursion supplies, L2's
  `hasWPowerNumerator.mem_regularElms_set_of_dvd` fires and `A_{0,σ} ∈ 𝒪`.  This is exactly the
  `hA` interface L7's `betaRec_mem` calls per recursion term.

For the **general `i₁ > 0`** case (the inner-`X` Hasse derivative, which requires building the
trivariate Hasse-derivative machinery that is not in tree) we isolate the residual not as a `sorry`
but as an explicit hypothesis-taking lemma `genHasseCoeff_hasWPowerNumerator_of_clearing`: it
*derives* `HasWPowerNumerator` from the two genuine App-A inputs (the natDegree bound on the cleared
numerator and the `W ∣ top-coeff` divisibility), so an `i₁ > 0` instantiation only has to supply
those two facts.

This file does **not** edit any existing file.  All names live in `namespace ArkLib`.

What is proven (all kernel-clean, no `sorry`/`admit`/`axiom`/`native_decide`):

* `hasseDerivYNumerPoly_natDegree_le`, `hasseDerivYNumerPoly_coeff`, the top-coeff `W`-divisibility
  `leadingCoeff_dvd_hasseDerivYNumerPoly_coeff`.
* `lineHasseCoeff_hasWPowerNumerator` — the concrete `HasWPowerNumerator (A_{0,σ}) (d−σ−1)`.
* `genHasseCoeff_hasWPowerNumerator_of_clearing` — the residual-isolating generic clearing lemma.
* `lineHasseCoeff_mem_regularElms_set_of_dvd` — the L7-facing `hA` composition.
-/

import ArkLib.ToMathlib.HasseDerivNumerators
import ArkLib.Data.Polynomial.RationalFunctions
import Mathlib

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2

namespace ArkLib

variable {F : Type} [Field F]

/-! ### The concrete `Y`-Hasse-derivative numerator polynomial

The order-`σ` Hasse derivative (in the outer `Y` variable) of the `X`-specialization
`R(x₀,·,Z) = Bivariate.evalX (C x₀) R : F[X][Y]`.  Evaluating this `F[X][Y]` at `α₀ = T/W` realizes
`∆^{0}_X ∆^{σ}_Y R(x₀, α₀, Z)` (the `i₁ = 0` line of recursion (A.1)). -/

/-- The concrete numerator polynomial: `∆^{σ}_Y R(x₀,·,Z)` as a `F[X][Y]`. -/
noncomputable def hasseDerivYNumerPoly (x₀ : F) (R : F[X][X][Y]) (σ : ℕ) : F[X][Y] :=
  Polynomial.hasseDeriv σ (Bivariate.evalX (Polynomial.C x₀) R)

/-- The `Y`-degree of the order-`σ` Hasse derivative drops by (at least) `σ`:
`natDegree (∆^σ_Y R(x₀,·,Z)) ≤ R.natDegree − σ`. -/
lemma hasseDerivYNumerPoly_natDegree_le (x₀ : F) (R : F[X][X][Y]) (σ : ℕ) :
    (hasseDerivYNumerPoly x₀ R σ).natDegree ≤ R.natDegree - σ := by
  unfold hasseDerivYNumerPoly
  calc (Polynomial.hasseDeriv σ (Bivariate.evalX (Polynomial.C x₀) R)).natDegree
      ≤ (Bivariate.evalX (Polynomial.C x₀) R).natDegree - σ :=
        Polynomial.natDegree_hasseDeriv_le _ σ
    _ ≤ R.natDegree - σ := by
        have : (Bivariate.evalX (Polynomial.C x₀) R).natDegree ≤ R.natDegree := by
          rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
          intro n hn
          have hcoeff : R.coeff n = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt hn
          simp [Bivariate.evalX_eq_map, Polynomial.coeff_map, hcoeff]
        omega

/-- The coefficients of the Hasse-derivative numerator, via `Polynomial.hasseDeriv_coeff`:
`(∆^σ_Y R(x₀,·,Z)).coeff n = (n+σ).choose σ · R(x₀,·,Z).coeff (n+σ)`. -/
lemma hasseDerivYNumerPoly_coeff (x₀ : F) (R : F[X][X][Y]) (σ n : ℕ) :
    (hasseDerivYNumerPoly x₀ R σ).coeff n =
      ((n + σ).choose σ : F[X]) * (Bivariate.evalX (Polynomial.C x₀) R).coeff (n + σ) := by
  unfold hasseDerivYNumerPoly
  rw [Polynomial.hasseDeriv_coeff]

/-- **The `W`-divisibility "save" (App-A line ~2931), specialized to the line case.**  The leading
coefficient `W = H.leadingCoeff` divides the top relevant coefficient of `∆^σ_Y R(x₀,·,Z)` — namely
the coefficient at index `R.natDegree − σ`, which equals (a multinomial multiple of) the top
`Y`-coefficient of `R(x₀,·,Z)`, which `W` divides by `Hypotheses.dvd_evalX`.  This is precisely the
`W`-divisibility supplied by the recursion's prefactor and is what makes the cleared numerator
integral. -/
lemma leadingCoeff_dvd_hasseDerivYNumerPoly_coeff {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]}
    (hHyp : Hypotheses x₀ R H) (σ : ℕ) (hσ : σ ≤ R.natDegree) :
    H.leadingCoeff ∣ (hasseDerivYNumerPoly x₀ R σ).coeff (R.natDegree - σ) := by
  rw [hasseDerivYNumerPoly_coeff]
  have hsum : R.natDegree - σ + σ = R.natDegree := Nat.sub_add_cancel hσ
  rw [hsum]
  rcases leadingCoeff_dvd_evalX_coeff_natDegree hHyp with ⟨q, hq⟩
  exact ⟨((R.natDegree).choose σ : F[X]) * q, by rw [hq]; ring⟩

/-! ### The concrete line coefficient `A_{0,σ}` in `𝕃` and its `W`-power-numerator form -/

/-- The concrete `i₁ = 0` line Hasse-derivative coefficient `A_{0,σ} = ∆^σ_Y R(x₀, α₀, Z) ∈ 𝕃`,
obtained by evaluating the numerator polynomial at the canonical root `α₀ = T/W`.  (The App-A
multinomial scalar for a single block `λ = (σ)` is `1`.) -/
noncomputable def lineHasseCoeff (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [H_irreducible : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]
    (σ : ℕ) : 𝕃 H :=
  Polynomial.eval₂ liftToFunctionField
    (functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff)
    (hasseDerivYNumerPoly x₀ R σ)

/-! ### Generic clearing lemma (isolates the `i₁ > 0` residual as explicit hypotheses, NOT a sorry)

The `W`-power-numerator form of *any* `eval₂(T/W) P` follows from the two genuine App-A inputs:
(i) a `natDegree` bound `P.natDegree ≤ (j+1)` matching the cleared exponent `j`, and
(ii) the `W`-divisibility of the cleared top coefficient `P.coeff (j+1)`.  An `i₁ > 0`
instantiation (once the trivariate inner-`X` Hasse derivative is named) need only supply these two
facts about its numerator polynomial; the `HasWPowerNumerator` conclusion is then automatic. -/
lemma genHasseCoeff_hasWPowerNumerator_of_clearing {H : F[X][Y]}
    [H_irreducible : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]
    {P : F[X][Y]} {j : ℕ} (hP : P.natDegree ≤ j + 1)
    (hdvd : H.leadingCoeff ∣ P.coeff (j + 1)) :
    HasWPowerNumerator
      (Polynomial.eval₂ liftToFunctionField
        (functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff) P) j := by
  -- The in-tree clearing machine gives `W^j · eval₂(T/W) P ∈ regularElms_set H`.
  have hreg :
      liftToFunctionField (H := H) H.leadingCoeff ^ j *
        Polynomial.eval₂ liftToFunctionField
          (functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff) P ∈
        regularElms_set H :=
    regularElms_set_mul_pow_eval₂_div_of_natDegree_le_succ_of_coeff_succ_dvd hP hdvd
  rcases hreg with ⟨B, hB⟩
  refine ⟨B, ?_⟩
  -- Rewrite `W^j` in the `W_𝕃` notation and commute the product to match `A · W^j = embedding B`.
  have hWeq : (W_𝕃 H : 𝕃 H) = liftToFunctionField (H := H) H.leadingCoeff := rfl
  rw [hWeq, ← hB, mul_comm]

/-- **Main theorem (concrete `i₁ = 0` line case).**  The concrete Hasse-derivative coefficient
`A_{0,σ}` has the `W`-power-numerator form at the App-A exponent `d − δ − Σλ = R.natDegree − 1 − σ`
(with `δ_{0,0} = 1`, `Σλ = σ`):

  `HasWPowerNumerator (lineHasseCoeff x₀ R H σ) (R.natDegree − σ − 1)`.

This is exactly the shape L7's recursion consumes, established for the genuine in-tree objects with
the `W`-divisibility coming from `Hypotheses` (no sorry/axiom).  Requires `σ + 1 ≤ R.natDegree`
(so that the cleared exponent `R.natDegree − σ − 1` and the matching `(R.natDegree − σ − 1) + 1`
index are the honest ones — the boundary `σ = R.natDegree` line is the leading term handled
separately). -/
lemma lineHasseCoeff_hasWPowerNumerator {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]}
    [H_irreducible : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) {σ : ℕ} (hσ : σ + 1 ≤ R.natDegree) :
    HasWPowerNumerator (lineHasseCoeff x₀ R H σ) (R.natDegree - σ - 1) := by
  unfold lineHasseCoeff
  set j := R.natDegree - σ - 1 with hj
  -- `j + 1 = R.natDegree - σ`, so the natDegree bound and the cleared-coeff index line up.
  have hj1 : j + 1 = R.natDegree - σ := by omega
  refine genHasseCoeff_hasWPowerNumerator_of_clearing (j := j) ?_ ?_
  · -- `natDegree (∆^σ_Y R(x₀,·,Z)) ≤ R.natDegree - σ = j + 1`.
    rw [hj1]; exact hasseDerivYNumerPoly_natDegree_le x₀ R σ
  · -- `W ∣ (∆^σ_Y R(x₀,·,Z)).coeff (j+1) = .coeff (R.natDegree - σ)`.
    rw [hj1]
    exact leadingCoeff_dvd_hasseDerivYNumerPoly_coeff hHyp σ (by omega)

/-! ### L7-facing composition (`hA` interface)

L7's `betaRec_mem` needs, per recursion term, that the coefficient lands in `𝒪`.  L2 supplies the
closure fact `hasWPowerNumerator.mem_regularElms_set_of_dvd`: a numerator form whose numerator is
`W^j`-divisible *inside `𝒪`* is integral.  The recursion supplies that `𝒪`-side divisibility witness
(its `W^{i₁+δ}·ξ^{2i₁+Σλ−2}` prefactor).  We thread the concrete `A_{0,σ}` numerator through it. -/

/-- **L7 composition.**  Given the `𝒪`-side divisibility witness `W_𝒪^{d−σ−1} ∣ B` that the
β-recursion supplies for the concrete line numerator `B` (the `𝒪`-element with
`A_{0,σ} · W^{d−σ−1} = embedding B`), the concrete coefficient `A_{0,σ}` is integral
(`∈ regularElms_set H`).  This is the exact `hA`-shaped fact L7's `betaRec_mem` calls per term. -/
lemma lineHasseCoeff_mem_regularElms_set_of_dvd {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]}
    [H_irreducible : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]
    {σ : ℕ} {B : 𝒪 H}
    (hB : lineHasseCoeff x₀ R H σ * W_𝕃 H ^ (R.natDegree - σ - 1) = embeddingOf𝒪Into𝕃 H B)
    (hdvd : W_𝒪 H ^ (R.natDegree - σ - 1) ∣ B) :
    lineHasseCoeff x₀ R H σ ∈ regularElms_set H :=
  hasWPowerNumerator.mem_regularElms_set_of_dvd hB hdvd

/-- The fully packaged L7 entry point: the concrete line coefficient *is* a `HasWPowerNumerator`
(from `lineHasseCoeff_hasWPowerNumerator`), and given the recursion's `𝒪`-side divisibility witness
on its numerator it lands in `𝒪`.  This bundles the existence of the numerator `B` (from the main
theorem) with the membership closure, matching L7's `hA` interface in one shot. -/
lemma lineHasseCoeff_mem_regularElms_set {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]}
    [H_irreducible : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) {σ : ℕ} (hσ : σ + 1 ≤ R.natDegree)
    (hdvd : ∀ B : 𝒪 H,
      lineHasseCoeff x₀ R H σ * W_𝕃 H ^ (R.natDegree - σ - 1) = embeddingOf𝒪Into𝕃 H B →
        W_𝒪 H ^ (R.natDegree - σ - 1) ∣ B) :
    lineHasseCoeff x₀ R H σ ∈ regularElms_set H := by
  obtain ⟨B, hB⟩ := lineHasseCoeff_hasWPowerNumerator hHyp hσ
  exact hasWPowerNumerator.mem_regularElms_set_of_dvd hB (hdvd B hB)

end ArkLib
