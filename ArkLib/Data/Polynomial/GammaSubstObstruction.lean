/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.Nilpotent.Lemmas

/-!
# The gamma-substitution obstruction (BCIKS20 App. A.4 - P2 frontier)

A kernel-checked obstruction explaining why the Hensel-lift power series `gamma` of
`RationalFunctions.lean` (`def gamma ... := PowerSeries.subst (PowerSeries.mk subst) (mk alpha)`,
where `subst 0 = fieldToL (-x0)`, `subst 1 = 1`, `subst _ = 0`, i.e. the substituted
series is `C (-x0) + X`) is degenerate for `x0 != 0`:

`PowerSeries.subst` only behaves as composition when the substituted series satisfies
`PowerSeries.HasSubst`, i.e. its constant coefficient is nilpotent
(`HasSubst a := IsNilpotent (constantCoeff a)`). The gamma-substitution series
`C (-x0) + X` has constant coefficient `-x0`, which over a field is nilpotent iff
`x0 = 0`. Hence:

* for `x0 != 0`, `HasSubst` fails, so the `coeff_subst` composition-coefficient formula
  (the engine of the wave-3/4 Faa-di-Bruno P2 path) does not apply to gamma as defined;
  gamma is not the intended composition and the planned order-by-order vanishing argument
  is invalid until the definition is recentered;
* the faithful fix is to substitute the local variable `X' := X - x0` (constant
  coefficient `0`, trivially nilpotent), i.e. treat gamma as a power series in `X'`.

This is a second definitional gap on the P2 chain, parallel to the `beta_regular = 0` stub:
both `beta`/`alpha`/`gamma` must be re-anchored to the genuine recursive Hensel data before
`R(X, gamma, Z) = 0` (P2) is even meaningfully provable. See
`research/proximity-prize/dispositions/pc-w2-P2-scout.md` and the wave-3 scout.

The lemma below is the precise, reusable, field-generic root of the obstruction.
-/

namespace ProximityPrize

open PowerSeries

/-- Gamma-substitution obstruction, generic form. Over a field `K`, the degree-`<= 1`
power series `C c + X` is `HasSubst`-substitutable iff its constant term `c` vanishes.

This is exactly the shape of the gamma-substitution series of BCIKS20 App. A.4 with
`c = -x0`: it can be substituted, so `PowerSeries.subst` is genuine composition, only when
`x0 = 0`. For `x0 != 0` the `coeff_subst` machinery does not apply and the defined `gamma`
is not the intended Hensel-lift series. -/
theorem hasSubst_C_add_X_iff {K : Type*} [Field K] (c : K) :
    PowerSeries.HasSubst (PowerSeries.C K c + PowerSeries.X) <-> c = 0 := by
  unfold PowerSeries.HasSubst
  rw [map_add, PowerSeries.constantCoeff_C, PowerSeries.constantCoeff_X, add_zero]
  exact isNilpotent_iff_eq_zero

/-- Specialization to the literal gamma-substitution constant `-x0`: the substitution is
valid iff `x0 = 0`. -/
theorem hasSubst_C_neg_add_X_iff {K : Type*} [Field K] (x0 : K) :
    PowerSeries.HasSubst (PowerSeries.C K (-x0) + PowerSeries.X) <-> x0 = 0 := by
  rw [hasSubst_C_add_X_iff]
  constructor
  · exact neg_eq_zero.mp
  · intro h
    rw [h, neg_zero]

end ProximityPrize
