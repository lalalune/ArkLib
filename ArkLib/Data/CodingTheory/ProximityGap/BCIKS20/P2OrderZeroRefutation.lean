/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.RestrictedFaaDiBrunoExtract

/-!
# BCIKS20 Appendix A.4 — the order-zero P2 carved core is mis-normalized for non-monic `H`

The carved P2 residual `RestrictedFaaDiBrunoMatch` (the single named combinatorial core of the
(P2) lift identity, tracked by issue #139 ⟺ the #9 P2 half, and asserted by the
`restrictedFaaDiBrunoMatch_residual` axiom) is **not unconditionally true**.  This file isolates a
genuine *refutation* of its order-zero component for non-monic `H`.

## The defect

The in-tree reduction chain (all `hHyp.dvd_evalX`-free) proves, under only `2 ≤ R.natDegree`:

via `restrictedMatchAt_zero_iff_eval₂WDivTarget` then the target definition:
```
RestrictedFaaDiBrunoMatchAt H x₀ R hHyp 0
  ↔ RestrictedMatchAtZeroEval₂WDivTarget H x₀ R
  ↔ ( eval₂ lift (T/W) p  =  eval₂ lift T p / W ^ R.natDegree )
```
with `p = evalX (C x₀) (Δ_X¹ R)` the order-1 `X`-Taylor coefficient and
`W = liftToFunctionField H.leadingCoeff`.

The recursion-side normalization clears by the **full** `W ^ R.natDegree`, but the order-1 numerator
`p` has actual `Y`-degree `natDegreeY p`, which may be strictly smaller.  When `p` is a nonzero
`Y`-**constant** (`natDegreeY p = 0`) the target collapses to `lift c = lift c / W ^ R.natDegree`,
i.e. `W ^ R.natDegree = 1` — **false** for non-monic `H` (`W` is not a root of unity, so
`W ^ R.natDegree ≠ 1` for `R.natDegree ≥ 1`).

## Why this regime is reachable (non-vacuity)

`ClaimA2.Hypotheses x₀ R H` constrains only the **0th** `X`-Taylor coefficient
`g = evalX (C x₀) R` (`dvd_evalX : H ∣ g` and `separable_evalX : g.Separable`).  It places **no**
constraint on the order-1 coefficient `p = evalX (C x₀) (Δ_X¹ R)`.  Concretely, taking
`R = g(Y) + (X − x₀)·C c + (X − x₀)²·(…)` with `g = H·(Y − a)` separable gives `hHyp`, `p = C c`
constant, and `R.natDegree = natDegreeY g ≥ 2`.  Hence the refutation below is *non-vacuous*: there
exist `R` satisfying `ClaimA2.Hypotheses` on which the carved order-zero core fails.

## Consequence

`restrictedFaaDiBrunoMatch_residual` (the allowlisted axiom, issue #169) asserts a proposition that
is **false** for non-monic `H`, so it is unsound, not merely unproven.  The fix is to re-normalize
the recursion-side `B_coeff` clearing to the actual numerator `Y`-degree (`natDegreeY p`, via the
proven cleared representative `hasseCoeffRepr𝒪_cleared`) rather than the uniform `R.natDegree`.
-/

noncomputable section

open scoped BigOperators
open Polynomial Polynomial.Bivariate
open BCIKS20AppendixA
open ProximityPrize.BCIKS20.GammaGenuine

namespace BCIKS20.HenselNumerator

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- **Refutation of the order-zero P2 `eval₂`/W-divisor target for a `Y`-constant numerator.**
If the order-1 `X`-Taylor coefficient `evalX (C x₀) (Δ_X¹ R)` is a nonzero `Y`-constant `C c`, then
the order-zero target `eval₂(T/W) = eval₂(T) / W ^ R.natDegree` collapses (`eval₂_C`) to
`lift c = lift c / W ^ R.natDegree`, which holds iff `W ^ R.natDegree = 1`.  For non-monic `H`
(`W ^ R.natDegree ≠ 1`) it is therefore **false**.  This isolates the genuine cleared/un-cleared
normalization defect: the recursion clears by the full `R.natDegree` while the numerator's actual
`Y`-degree here is `0`. -/
theorem eval₂WDivTarget_false_of_constant_of_W_pow_ne_one
    (x₀ : F) (R : F[X][X][Y]) (c : F[X])
    (hp : Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 (hasseDerivY 0 R))
        = Polynomial.C c)
    (hc : liftToFunctionField (H := H) c ≠ 0)
    (hW : liftToFunctionField (H := H) H.leadingCoeff ^ R.natDegree ≠ 1) :
    ¬ RestrictedMatchAtZeroEval₂WDivTarget H x₀ R := by
  unfold RestrictedMatchAtZeroEval₂WDivTarget
  rw [hp, Polynomial.eval₂_C, Polynomial.eval₂_C]
  intro h
  have hWne : liftToFunctionField (H := H) H.leadingCoeff ≠ 0 :=
    liftToFunctionField_leadingCoeff_ne_zero (H := H)
  rw [eq_div_iff (pow_ne_zero R.natDegree hWne)] at h
  -- h : lift c * W ^ R.natDegree = lift c
  have hz : liftToFunctionField (H := H) c
      * (liftToFunctionField (H := H) H.leadingCoeff ^ R.natDegree - 1) = 0 := by
    rw [mul_sub, mul_one, h, sub_self]
  rcases mul_eq_zero.mp hz with h1 | h2
  · exact hc h1
  · exact hW (sub_eq_zero.mp h2)

/-- **The carved order-zero P2 core is FALSE for a `Y`-constant order-1 numerator over non-monic
`H`.**  Composing the refutation of the `eval₂`/W-divisor target with the proven equivalence
`restrictedMatchAt_zero_iff_eval₂WDivTarget` (which uses only `2 ≤ R.natDegree`, never
`hHyp.dvd_evalX`).  Hence `RestrictedFaaDiBrunoMatch` — the carved #139/#9-P2 core, and the content
asserted by the `restrictedFaaDiBrunoMatch_residual` axiom — does **not** hold as stated for
non-monic `H`: see the module docstring for the explicit non-vacuous witness family. -/
theorem restrictedMatchAt_zero_false_of_constant_of_W_pow_ne_one
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree) (c : F[X])
    (hp : Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 (hasseDerivY 0 R))
        = Polynomial.C c)
    (hc : liftToFunctionField (H := H) c ≠ 0)
    (hW : liftToFunctionField (H := H) H.leadingCoeff ^ R.natDegree ≠ 1) :
    ¬ RestrictedFaaDiBrunoMatchAt H x₀ R hHyp 0 := by
  rw [restrictedMatchAt_zero_iff_eval₂WDivTarget H x₀ R hHyp hd]
  exact eval₂WDivTarget_false_of_constant_of_W_pow_ne_one H x₀ R c hp hc hW

end BCIKS20.HenselNumerator

#print axioms BCIKS20.HenselNumerator.eval₂WDivTarget_false_of_constant_of_W_pow_ne_one
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.restrictedMatchAt_zero_false_of_constant_of_W_pow_ne_one
