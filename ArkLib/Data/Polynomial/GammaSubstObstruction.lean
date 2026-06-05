/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.Nilpotent.Lemmas

/-!
# The γ-substitution obstruction (BCIKS20 App. A.4 — P2 frontier)

A kernel-checked obstruction explaining why the Hensel-lift power series `γ` of
`RationalFunctions.lean` (`def γ … := PowerSeries.subst (PowerSeries.mk subst) (mk α)`,
where `subst 0 = fieldTo𝕃 (-x₀)`, `subst 1 = 1`, `subst _ = 0` — i.e. the substituted
series is `C (-x₀) + X`) is **degenerate for `x₀ ≠ 0`**:

`PowerSeries.subst` only behaves as composition when the substituted series satisfies
`PowerSeries.HasSubst`, i.e. its constant coefficient is nilpotent
(`HasSubst a := IsNilpotent (constantCoeff a)`). The γ-substitution series `C (-x₀) + X`
has constant coefficient `-x₀`, which over a field is nilpotent **iff `x₀ = 0`**. Hence:

* for `x₀ ≠ 0`, `HasSubst` fails, so the `coeff_subst` composition-coefficient formula
  (the engine of the wave-3/4 Faà-di-Bruno P2 path) **does not apply to γ as defined** —
  `γ` is not the intended composition and the planned order-by-order vanishing argument
  is invalid until the definition is recentered;
* the faithful fix is to substitute the **local variable** `X' := X - x₀` (constant
  coefficient `0`, trivially nilpotent), i.e. treat `γ` as a power series in `X'`.

This is a second definitional gap on the P2 chain, parallel to the `β_regular = 0` stub:
both `β`/`α`/`γ` must be re-anchored to the genuine recursive Hensel data before
`R(X, γ, Z) = 0` (P2) is even meaningfully provable. See
`research/proximity-prize/dispositions/pc-w2-P2-scout.md` and the wave-3 scout.

The lemma below is the precise, reusable, field-generic root of the obstruction.
-/

namespace ProximityPrize

open PowerSeries

/-- **γ-substitution obstruction (generic form).** Over a field `K`, the degree-`≤1`
power series `C c + X` is `HasSubst`-substitutable iff its constant term `c` vanishes.

This is exactly the shape of the γ-substitution series of [BCIKS20] App. A.4 with
`c = -x₀`: it can be substituted (so `PowerSeries.subst` is genuine composition) only when
`x₀ = 0`. For `x₀ ≠ 0` the `coeff_subst` machinery does not apply and the defined `γ` is
not the intended Hensel-lift series. -/
theorem hasSubst_C_add_X_iff {K : Type*} [Field K] (c : K) :
    PowerSeries.HasSubst ((PowerSeries.C c : PowerSeries K) + PowerSeries.X) ↔ c = 0 := by
  simp only [PowerSeries.HasSubst, map_add, isNilpotent_iff_eq_zero]
  rw [show (MvPowerSeries.constantCoeff (PowerSeries.C c : PowerSeries K)) = c from
        PowerSeries.constantCoeff_C c,
      show (MvPowerSeries.constantCoeff (PowerSeries.X : PowerSeries K)) = 0 from
        PowerSeries.constantCoeff_X, add_zero]

/-- Specialisation to the literal γ-substitution constant `-x₀`: the substitution is valid
iff `x₀ = 0`. -/
theorem hasSubst_C_neg_add_X_iff {K : Type*} [Field K] (x₀ : K) :
    PowerSeries.HasSubst ((PowerSeries.C (-x₀) : PowerSeries K) + PowerSeries.X) ↔ x₀ = 0 := by
  rw [hasSubst_C_add_X_iff, neg_eq_zero]

end ProximityPrize
