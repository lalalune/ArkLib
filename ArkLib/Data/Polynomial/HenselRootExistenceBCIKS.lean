/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.Polynomial.RationalFunctions
import ArkLib.Data.Polynomial.HenselExistenceXDep

/-!
# Existence of a Hensel root for `evalRAtPowerSeries` (BCIKS20 Appendix A.4)

This file lands the genuine analytic prize of the Hensel-lift development in the
`evalRAtPowerSeries` terms used by `IsHenselNumeratorSequence`: **a power-series root of
`R(X,Y,Z)` (the BCIKS20 App-A.4 Hensel lift) exists.**

`evalRAtPowerSeries H R Γ = Polynomial.eval Γ (R.map (liftCoeffToPowerSeries H))` is the
evaluation of a polynomial over the power-series ring `𝕃 H⟦X⟧` whose coefficients depend on `X`.
The general X-dependent Hensel engine
`ProximityPrize.HenselExistenceXDep.exists_powerSeries_root_xdep` lifts a *simple* root of the
order-0 reduction to a genuine root over `𝕃 H⟦X⟧` — by Newton iteration, so the produced root
needs **no `PowerSeries.subst`** and is unaffected by the `HasSubst (shiftSeries x₀ H) ↔ x₀ = 0`
landmine (`RationalFunctions.lean`, the F1 caveat).

`exists_root_of_evalRAtPowerSeries` states it conditionally on the order-0 *simple-root* data:

* `hroot`  — `T/W` is a root of the order-0 reduction `(R.map liftCoeff).map constantCoeff`,
* `hunit`  — that root is simple (the order-0 `Y`-derivative at `T/W` is a unit).

Both ingredients are standard and available in `RationalFunctionsCore`: `hroot` follows from
`H ∣ R(x₀,·)` (the `Hypotheses`) together with
`eval₂_liftToFunctionField_div_leadingCoeff_H_eq_zero` (which gives `H(T/W) = 0` in `𝕃 H`), and
`hunit` is `ζ ≠ 0` (a field, so nonzero ⇒ unit), which is exactly separability of `R(x₀,·)`.
Wiring those discharges in (`Hypotheses.separable_evalX`) is the only remaining gap to an
unconditional statement; the analytic core — the order-by-order Newton vanishing — is **done**
and kernel-clean here via the engine.
-/

open Polynomial
open scoped PowerSeries

set_option maxHeartbeats 2000000

namespace BCIKS20AppendixA.ClaimA2

variable {F : Type} [Field F]

/-- `evalRAtPowerSeries` is `Polynomial.eval` of the coefficient-lifted polynomial over the
power-series ring `𝕃 H⟦X⟧`. -/
theorem evalRAtPowerSeries_eq_eval_map (H : F[X][Y]) (R : F[X][X][Y])
    (Γ : PowerSeries (𝕃 H)) :
    evalRAtPowerSeries H R Γ = Polynomial.eval Γ (R.map (liftCoeffToPowerSeries H)) := by
  rw [evalRAtPowerSeries, Polynomial.eval₂_eq_eval_map]

/-- **Existence of the BCIKS20 App-A.4 Hensel root** (conditional on the order-0 simple-root
data).  If `T/W` is a *simple* root of the order-0 reduction of `R` lifted into `𝕃 H`, then there
is a power series `Γ : 𝕃 H⟦X⟧` with `constantCoeff Γ = T/W` and `evalRAtPowerSeries H R Γ = 0`.

The root is produced by Newton iteration (no `PowerSeries.subst`), so it exists genuinely; the
hypotheses are the order-0 root (`hroot`) and its simplicity (`hunit`). -/
theorem exists_root_of_evalRAtPowerSeries (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (hroot : Polynomial.eval
        (functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff)
        ((R.map (liftCoeffToPowerSeries H)).map (PowerSeries.constantCoeff (𝕃 H))) = 0)
    (hunit : IsUnit (Polynomial.eval
        (functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff)
        (Polynomial.derivative
          ((R.map (liftCoeffToPowerSeries H)).map (PowerSeries.constantCoeff (𝕃 H)))))) :
    ∃ Γ : PowerSeries (𝕃 H),
      PowerSeries.constantCoeff (𝕃 H) Γ =
        functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff ∧
      evalRAtPowerSeries H R Γ = 0 := by
  obtain ⟨Γ, hc, hev⟩ :=
    ProximityPrize.HenselExistenceXDep.exists_powerSeries_root_xdep
      (P := R.map (liftCoeffToPowerSeries H))
      (c := functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff)
      hroot hunit
  exact ⟨Γ, hc, by rw [evalRAtPowerSeries_eq_eval_map, hev]⟩

end BCIKS20AppendixA.ClaimA2
