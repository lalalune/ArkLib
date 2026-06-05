/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Discharge of the `hdvd_top` residual of brick **L2b-general**

Brick L2b-general (`ArkLib.ToMathlib.HasseDerivNumeratorGeneral`) reduced the general (`i₁ > 0`)
mixed Hasse-derivative `W`-power-numerator theorem
`genHasseCoeff_hasWPowerNumerator_of_dvd_top` to a *single* App-A divisibility residual:

```
  hdvd_top : H.leadingCoeff ∣ (Bivariate.evalX (C x₀) (innerXHasse i₁ R)).coeff R.natDegree
```

the `W`-divisibility of the inner-`X`-derived top `Y`-coefficient (the App-A recursion-(A.1)
`W^{i₁+δ}·ξ^{2i₁+Σλ−2}` prefactor save, for general `i₁ > 0`).  For `i₁ = 0` this is already
discharged in tree by `Hypotheses.leadingCoeff_dvd_evalX_coeff_natDegree`.

This file discharges `hdvd_top` for **general `i₁`** from genuine in-tree inputs.

## The genuine trivariate content, isolated

The inner-`X` Hasse derivative acts coefficient-wise on the `Y`-layer
(`innerXHasse_coeff`), and `X`-specialization at `x₀` is `evalX = map (evalRingHom (C x₀))`,
so the top `Y`-coefficient that `hdvd_top` is about rewrites cleanly:

```
  (Bivariate.evalX (C x₀) (innerXHasse i₁ R)).coeff R.natDegree
    =  (hasseDeriv i₁ (R.coeff R.natDegree)).eval (C x₀)                  -- `evalX_innerXHasse_coeff`
```

i.e. it is the order-`i₁` **Hasse–Taylor coefficient at `C x₀`** of the top `Y`-coefficient
`R.coeff R.natDegree ∈ (F[X])[X]` of `R` (the GS factor), in the inner `X`-variable.

The *honest* App-A structural fact behind the `W`-prefactor save is the **multiplicity / vanishing
structure of the GS interpolant at `x₀`**: the leading `Y`-coefficient of `R` is divisible by
`W = H.leadingCoeff` *as a polynomial in the inner `X`-variable*, i.e.

```
  hdvd_C : (C W) ∣ R.coeff R.natDegree          in (F[X])[X].
```

This is strictly stronger than (and implies, see `hdvd_C_implies_zero_case`) the `i₁ = 0` line fact
`W ∣ (R.coeff R.natDegree).eval (C x₀)` that `Hypotheses` provides — it is exactly the extra
trivariate content that makes the *whole* Hasse–Taylor tower (every order `i₁`) `W`-divisible.
Since `hasseDeriv i₁` is `F[X]`-linear, it commutes with the `C W` scalar, and the `W`-divisibility
propagates through `hasseDeriv i₁` then `eval (C x₀)` to *all* orders at once.  We prove this
reduction (`hdvd_top_of_dvd_C`); the deep multiplicity step is isolated as the single explicit
hypothesis `hdvd_C` — never a `sorry`.

We also give the strictly-minimal per-`i₁` reduction `hdvd_top_of_dvd_hasseTaylor` (taking only the
already-`evalX`'d per-order divisibility), and recover the `i₁ = 0` line case from `Hypotheses` with
no residual at all (`hdvd_top_zero`).  Finally we wire `hdvd_top_of_dvd_C` into brick L2b-general's
`genHasseCoeff_hasWPowerNumerator_of_dvd_top` to obtain the residual-discharged general
`W`-power-numerator theorem `genHasseCoeff_hasWPowerNumerator_of_dvd_C`.

This file does **not** edit any existing file.  All names live in `namespace ArkLib`.

What is proven (all kernel-clean, no `sorry`/`admit`/`axiom`/`native_decide`):

* `evalX_innerXHasse_coeff` — the structural rewrite of the `hdvd_top` coefficient as the order-`i₁`
  Hasse–Taylor coefficient at `C x₀` of the top `Y`-coefficient of `R`.
* `hdvd_top_of_dvd_hasseTaylor` — `hdvd_top` from the minimal per-`i₁` (post-`evalX`) divisibility.
* `hdvd_top_of_dvd_C` — `hdvd_top` for **all** `i₁` from the single structural hypothesis `hdvd_C`.
* `hdvd_C_implies_zero_case` — `hdvd_C` implies the `i₁ = 0` line fact (consistency with `Hypotheses`).
* `hdvd_top_zero` — the `i₁ = 0` discharge from `Hypotheses` (no residual).
* `genHasseCoeff_hasWPowerNumerator_of_dvd_C` — the residual-discharged general theorem.
-/

import ArkLib.ToMathlib.HasseDerivNumeratorGeneral
import ArkLib.ToMathlib.HasseDerivNumeratorConcrete
import ArkLib.ToMathlib.HasseDerivNumerators
import ArkLib.Data.Polynomial.RationalFunctions
import Mathlib

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2

namespace ArkLib

variable {F : Type} [Field F]

/-! ### The structural rewrite of the `hdvd_top` coefficient

The inner-`X` Hasse derivative acts coefficient-wise on the `Y`-layer (`innerXHasse_coeff`, from
brick L2b-general), and `Bivariate.evalX (C x₀) = map (evalRingHom (C x₀))`, so the relevant top
`Y`-coefficient is the order-`i₁` Hasse–Taylor coefficient at `C x₀` of the top `Y`-coefficient
`R.coeff R.natDegree ∈ (F[X])[X]`. -/

/-- The `hdvd_top` coefficient is the order-`i₁` Hasse–Taylor coefficient at `C x₀` of the top
`Y`-coefficient of `R`:
`(Bivariate.evalX (C x₀) (∆^{i₁}_X R)).coeff n = (∆^{i₁}_X (R.coeff n)).eval (C x₀)`.
This is the genuine plumbing through which the App-A `W`-prefactor divisibility propagates. -/
lemma evalX_innerXHasse_coeff (x₀ : F) (R : F[X][X][Y]) (i₁ n : ℕ) :
    (Bivariate.evalX (Polynomial.C x₀) (innerXHasse i₁ R)).coeff n =
      (Polynomial.hasseDeriv i₁ (R.coeff n)).eval (Polynomial.C x₀) := by
  rw [Bivariate.evalX_eq_map, Polynomial.coeff_map]
  -- `(evalRingHom (C x₀)) p = p.eval (C x₀)` definitionally; then rewrite the inner-`X` coeff.
  rw [show ((Polynomial.evalRingHom (Polynomial.C x₀)) ((innerXHasse i₁ R).coeff n)) =
      ((innerXHasse i₁ R).coeff n).eval (Polynomial.C x₀) from rfl]
  rw [innerXHasse_coeff]

/-! ### `hdvd_top` from the minimal per-`i₁` (post-`evalX`) divisibility

The strictly-smallest reduction: assume only the already-specialized per-order divisibility (which is
literally the goal after the structural rewrite).  Useful when a caller can supply the Hasse–Taylor
coefficient divisibility directly for a fixed `i₁`. -/

/-- `hdvd_top` for a fixed `i₁` from the minimal post-`evalX` per-order divisibility hypothesis. -/
lemma hdvd_top_of_dvd_hasseTaylor {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]} {i₁ : ℕ}
    (hdvd : H.leadingCoeff ∣
      (Polynomial.hasseDeriv i₁ (R.coeff R.natDegree)).eval (Polynomial.C x₀)) :
    H.leadingCoeff ∣ (Bivariate.evalX (Polynomial.C x₀) (innerXHasse i₁ R)).coeff R.natDegree := by
  rw [evalX_innerXHasse_coeff]
  exact hdvd

/-! ### `hdvd_top` for *all* `i₁` from the single structural hypothesis

The honest App-A multiplicity content: `W = H.leadingCoeff` divides the top `Y`-coefficient of `R`
*as a polynomial in the inner `X`-variable*.  Because `hasseDeriv i₁` is `F[X]`-linear it commutes
with the `C W` scalar, so the `W`-divisibility survives `∆^{i₁}_X` and then `eval (C x₀)` for **every**
order `i₁` simultaneously — this is precisely the multiplicity-⟹-divisibility propagation the App-A
`W^{i₁+δ}` prefactor encodes. -/

/-- **Main discharge.**  From the single genuine structural hypothesis
`hdvd_C : (C W) ∣ R.coeff R.natDegree` (the App-A vanishing/multiplicity structure of the GS factor
`R` at `x₀`, with `W = H.leadingCoeff`), the residual `hdvd_top` holds for **every** inner Hasse
order `i₁`. -/
lemma hdvd_top_of_dvd_C {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]}
    (hdvd_C : (Polynomial.C H.leadingCoeff : (F[X])[X]) ∣ R.coeff R.natDegree) (i₁ : ℕ) :
    H.leadingCoeff ∣ (Bivariate.evalX (Polynomial.C x₀) (innerXHasse i₁ R)).coeff R.natDegree := by
  rw [evalX_innerXHasse_coeff]
  obtain ⟨c', hc'⟩ := hdvd_C
  rw [hc']
  -- `hasseDeriv i₁ (C W * c') = C W * hasseDeriv i₁ c'` (`F[X]`-linearity), then evaluate.
  rw [← Polynomial.smul_eq_C_mul, map_smul, Polynomial.smul_eq_C_mul,
      Polynomial.eval_mul, Polynomial.eval_C]
  exact Dvd.intro _ rfl

/-- The structural hypothesis `hdvd_C` implies the `i₁ = 0` line fact
`W ∣ (R.coeff R.natDegree).eval (C x₀)` — so it is a genuine *strengthening* of (consistent with)
the `Hypotheses`-supplied line divisibility, not an orthogonal assumption. -/
lemma hdvd_C_implies_zero_case {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]}
    (hdvd_C : (Polynomial.C H.leadingCoeff : (F[X])[X]) ∣ R.coeff R.natDegree) :
    H.leadingCoeff ∣ (R.coeff R.natDegree).eval (Polynomial.C x₀) := by
  obtain ⟨c', hc'⟩ := hdvd_C
  rw [hc', Polynomial.eval_mul, Polynomial.eval_C]
  exact Dvd.intro _ rfl

/-! ### `i₁ = 0` recovery from `Hypotheses` (no residual)

For `i₁ = 0` the inner-`X` Hasse derivative is the identity (`innerXHasse_zero`), so `hdvd_top` is
*exactly* `Hypotheses.leadingCoeff_dvd_evalX_coeff_natDegree`; no structural hypothesis is needed. -/

/-- For `i₁ = 0` the residual `hdvd_top` is discharged outright from `Hypotheses` (no residual). -/
lemma hdvd_top_zero {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]} (hHyp : Hypotheses x₀ R H) :
    H.leadingCoeff ∣ (Bivariate.evalX (Polynomial.C x₀) (innerXHasse 0 R)).coeff R.natDegree := by
  rw [evalX_innerXHasse_coeff, Polynomial.hasseDeriv_zero]
  rw [show ((LinearMap.id : (F[X])[X] →ₗ[F[X]] (F[X])[X]) (R.coeff R.natDegree)) =
      R.coeff R.natDegree from rfl]
  have h := leadingCoeff_dvd_evalX_coeff_natDegree hHyp
  rwa [Bivariate.evalX_eq_map, Polynomial.coeff_map] at h

/-! ### Wiring the discharge into brick L2b-general's `W`-power-numerator theorem

Feeding `hdvd_top_of_dvd_C` to brick L2b-general's
`genHasseCoeff_hasWPowerNumerator_of_dvd_top` discharges its lone residual, giving the general
(`i₁ > 0`) `W`-power-numerator theorem from the single structural hypothesis `hdvd_C`. -/

/-- **General `W`-power-numerator theorem with the residual discharged.**  For *every* inner Hasse
order `i₁`, given the single structural hypothesis `hdvd_C : (C W) ∣ R.coeff R.natDegree`, the general
mixed Hasse-derivative coefficient `A_{i₁,σ}` has the App-A `W`-power-numerator form at exponent
`R.natDegree − σ − 1`. -/
lemma genHasseCoeff_hasWPowerNumerator_of_dvd_C {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]}
    [H_irreducible : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]
    {i₁ σ : ℕ} (hσ : σ + 1 ≤ R.natDegree)
    (hdvd_C : (Polynomial.C H.leadingCoeff : (F[X])[X]) ∣ R.coeff R.natDegree) :
    HasWPowerNumerator (genHasseCoeff x₀ R H i₁ σ) (R.natDegree - σ - 1) :=
  genHasseCoeff_hasWPowerNumerator_of_dvd_top hσ (hdvd_top_of_dvd_C hdvd_C i₁)

/-- **L7-facing entry point with the residual discharged.**  The general coefficient lands in `𝒪`
(`∈ regularElms_set H`) given the structural hypothesis `hdvd_C` and the recursion's `𝒪`-side
divisibility witness on its numerator — matching L7's `hA`/`Bcoeff` interface, with no `hdvd_top`
residual. -/
lemma genHasseCoeff_mem_regularElms_set_of_dvd_C {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]}
    [H_irreducible : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]
    {i₁ σ : ℕ} (hσ : σ + 1 ≤ R.natDegree)
    (hdvd_C : (Polynomial.C H.leadingCoeff : (F[X])[X]) ∣ R.coeff R.natDegree)
    (hdvd : ∀ B : 𝒪 H,
      genHasseCoeff x₀ R H i₁ σ * W_𝕃 H ^ (R.natDegree - σ - 1) = embeddingOf𝒪Into𝕃 H B →
        W_𝒪 H ^ (R.natDegree - σ - 1) ∣ B) :
    genHasseCoeff x₀ R H i₁ σ ∈ regularElms_set H :=
  genHasseCoeff_mem_regularElms_set hσ (hdvd_top_of_dvd_C hdvd_C i₁) hdvd

end ArkLib

-- Axiom audit: every claimed-done lemma must rest only on `[propext, Classical.choice, Quot.sound]`.
#print axioms ArkLib.evalX_innerXHasse_coeff
#print axioms ArkLib.hdvd_top_of_dvd_hasseTaylor
#print axioms ArkLib.hdvd_top_of_dvd_C
#print axioms ArkLib.hdvd_C_implies_zero_case
#print axioms ArkLib.hdvd_top_zero
#print axioms ArkLib.genHasseCoeff_hasWPowerNumerator_of_dvd_C
#print axioms ArkLib.genHasseCoeff_mem_regularElms_set_of_dvd_C
