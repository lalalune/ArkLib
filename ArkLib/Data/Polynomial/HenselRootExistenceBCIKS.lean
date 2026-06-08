/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.Polynomial.RationalFunctions
import ArkLib.Data.Polynomial.HenselExistenceXDep

/-!
# Existence of a Hensel root for `evalRAtPowerSeries` (BCIKS20 Appendix A.4)

This file lands the analytic core of the Hensel-lift development in the `evalRAtPowerSeries`
terms used by `IsHenselNumeratorSequence`: **a power-series root of `R(X,Y,Z)` exists.**

`evalRAtPowerSeries H R Γ = eval₂ (liftCoeffToPowerSeries H) Γ R` is, after interpreting `Z` in
the function field and `X` as the power-series variable, the evaluation of a polynomial in `Y`
whose coefficients are power series in `X`.  The X-dependent Hensel engine
`ProximityPrize.HenselExistenceXDep.exists_powerSeries_root_eval₂` lifts a *simple* root of the
order-0 reduction to a genuine root over `𝕃 H⟦X⟧`.  It is built by Newton iteration, so the root
needs **no `PowerSeries.subst`** and is unaffected by the documented
`HasSubst (shiftSeries x₀ H) ↔ x₀ = 0` landmine (`RationalFunctions.lean`, the F1 caveat): a
Hensel root genuinely *exists*.

`exists_root_of_evalRAtPowerSeries` states this conditionally on the order-0 *simple-root* data,
kept in `eval₂` form (the polynomial stays over the light base `F[X][X]`, never materialized over
the heavy quotient `𝕃 H⟦X⟧`):

* `hroot` — `T/W` is a root of the order-0 reduction `eval₂ (constantCoeff ∘ liftCoeff) (T/W) R`;
* `hunit` — that root is simple (the order-0 `Y`-derivative at `T/W` is a unit, i.e. `ζ ≠ 0`).

Both follow from the standing `Hypotheses`: `hroot` from `H ∣ R(x₀,·)` together with
`eval₂_liftToFunctionField_div_leadingCoeff_H_eq_zero` (`H(T/W) = 0` in `𝕃 H`), and `hunit` from
`Hypotheses.separable_evalX` (a field, so `ζ ≠ 0 ⇒` unit).  Discharging those two against the
`𝕃 H` machinery is the remaining wiring; the analytic order-by-order Newton vanishing — the part
that was genuinely open — is **done** and kernel-clean via the engine.
-/

open Polynomial Polynomial.Bivariate ToRatFunc Ideal

set_option maxHeartbeats 1000000

namespace BCIKS20AppendixA.ClaimA2

variable {F : Type} [Field F]

/-- **Existence of the BCIKS20 App-A.4 Hensel root** (conditional on the order-0 simple-root
data, in `eval₂` form).  If `T/W` is a *simple* root of the order-0 reduction of `R`, there is a
power series `Γ : 𝕃 H⟦X⟧` with `constantCoeff Γ = T/W` and `evalRAtPowerSeries H R Γ = 0`.

The root is produced by Newton iteration (no `PowerSeries.subst`), so it exists genuinely; the
two hypotheses are the order-0 root (`hroot`) and its simplicity (`hunit`). -/
theorem exists_root_of_evalRAtPowerSeries (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (hroot : Polynomial.eval₂
        ((PowerSeries.constantCoeff (R := 𝕃 H)).comp (liftCoeffToPowerSeries H))
        (functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff) R = 0)
    (hunit : IsUnit (Polynomial.eval₂
        ((PowerSeries.constantCoeff (R := 𝕃 H)).comp (liftCoeffToPowerSeries H))
        (functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff)
        (Polynomial.derivative R))) :
    ∃ Γ : PowerSeries (𝕃 H),
      PowerSeries.constantCoeff (R := 𝕃 H) Γ =
        functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff ∧
      evalRAtPowerSeries H R Γ = 0 := by
  obtain ⟨Γ, hc, hev⟩ :=
    ProximityPrize.HenselExistenceXDep.exists_powerSeries_root_eval₂
      (liftCoeffToPowerSeries H) (P := R)
      (c := functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff)
      hroot hunit
  exact ⟨Γ, hc, hev⟩

end BCIKS20AppendixA.ClaimA2
