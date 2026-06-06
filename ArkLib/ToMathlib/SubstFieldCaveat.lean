/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib
import ArkLib.Data.Polynomial.RationalFunctions

/-!
# Substitution Caveats for Power Series over Fields

This module analyzes the algebraic conditions under which the power series substitution operator
`PowerSeries.subst` is well-defined. In particular, we formalize the condition that substitution
into a power series over a field requires the substituted series to have a constant coefficient
of zero (i.e., a positive order).

## Mathematical Formulation

Let $K$ be a field, and let $g(X) \in K[[X]]$ be a power series. Mathlib defines the substitution
operator $f(g(X))$ for $f \in K[[X]]$ to be well-defined if the constant coefficient of $g$ is nilpotent,
which is packaged as the `PowerSeries.HasSubst` predicate.

Over a field $K$, the only nilpotent element is zero. Therefore, we have the equivalence:
$$\text{HasSubst}(g) \iff \text{constantCoeff}(g) = 0$$

In the context of the BCIKS substitution $X \mapsto X - x_0$ used in Hensel lifting, the shift series is
$$g(X) = -x_0 + X$$
If the field is $K = \mathbb{L}_H$, which contains the base field $F$, the constant coefficient is
$0$ if and only if $x_0 = 0$. For any off-center point $x_0 \neq 0$, the substitution operator is not
well-defined under the standard Mathlib definition.

## Key Formalizations
* `hasSubst_iff_constantCoeff_eq_zero_of_field`: Pointwise equivalence of the substitution condition to a zero constant coefficient over a field.
* `constantCoeff_shiftSeries`: Computes the constant coefficient of the shift series.
* `hasSubst_shiftSeries_iff_eq_zero`: Shows that the BCIKS shift series is substitutable if and only if the expansion center is $0$.
-/

open Polynomial PowerSeries
open scoped Polynomial.Bivariate
open BCIKS20AppendixA BCIKS20AppendixA.ClaimA2

namespace ArkLib

namespace SubstFieldCaveat

/-! ### Substitution Conditions over Fields -/

/-- Characterizes the substitution condition in terms of the nilpotency of the constant coefficient. -/
theorem hasSubst_iff_isNilpotent_constantCoeff {S : Type*} [CommRing S] (g : PowerSeries S) :
    PowerSeries.HasSubst g ↔ IsNilpotent (PowerSeries.constantCoeff g) := by
  unfold PowerSeries.HasSubst
  rfl

/-- Over a field, a power series is substitutable if and only if its constant coefficient is zero. -/
theorem hasSubst_iff_constantCoeff_eq_zero_of_field {K : Type*} [Field K] (g : PowerSeries K) :
    PowerSeries.HasSubst g ↔ PowerSeries.constantCoeff g = 0 := by
  rw [hasSubst_iff_isNilpotent_constantCoeff]
  exact isNilpotent_iff_eq_zero

/-- Contrapositive form showing that a non-zero constant coefficient obstructs substitution. -/
theorem not_hasSubst_of_constantCoeff_ne_zero_of_field {K : Type*} [Field K] {g : PowerSeries K}
    (hg : PowerSeries.constantCoeff g ≠ 0) : ¬ PowerSeries.HasSubst g :=
  fun h => hg ((hasSubst_iff_constantCoeff_eq_zero_of_field g).mp h)

/-! ### The Shift Series and Constant Coefficient -/

variable {F : Type} [Field F]

/-- The shift series corresponding to the substitution $X \mapsto X - x_0$. -/
noncomputable def shiftSeries (x₀ : F) (H : F[X][Y]) : PowerSeries (𝕃 H) :=
  PowerSeries.mk fun t =>
    match t with
    | 0 => fieldTo𝕃 (-x₀)
    | 1 => 1
    | _ => 0

/-- Computes the constant coefficient of the shift series. -/
@[simp]
theorem constantCoeff_shiftSeries (x₀ : F) (H : F[X][Y]) :
    PowerSeries.constantCoeff (shiftSeries x₀ H) = fieldTo𝕃 (-x₀) := by
  unfold shiftSeries
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk]

/-- Injectivity of the canonical embedding into the function field. -/
theorem fieldTo𝕃_injective {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)] :
    Function.Injective (fieldTo𝕃 (H := H)) := by
  unfold fieldTo𝕃
  exact RingHom.injective _

/-- The specialized coordinate embedding vanishes if and only if the coordinate center is zero. -/
theorem fieldTo𝕃_neg_eq_zero_iff {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (x₀ : F) : fieldTo𝕃 (H := H) (-x₀) = 0 ↔ x₀ = 0 := by
  rw [map_neg, neg_eq_zero]
  exact ⟨fun h => fieldTo𝕃_injective (by rw [h, map_zero]),
         fun h => by rw [h, map_zero]⟩

/-! ### Substitution Validity of the Shift Series -/

variable {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- Proves that the shift series satisfies the substitution condition if and only if the expansion center is $0$. -/
theorem hasSubst_shiftSeries_iff_eq_zero (x₀ : F) :
    PowerSeries.HasSubst (shiftSeries x₀ H) ↔ x₀ = 0 := by
  rw [hasSubst_iff_constantCoeff_eq_zero_of_field, constantCoeff_shiftSeries,
    fieldTo𝕃_neg_eq_zero_iff]

/-- The centered case always satisfies the substitution condition. -/
theorem hasSubst_shiftSeries_zero :
    PowerSeries.HasSubst (shiftSeries (0 : F) H) :=
  (hasSubst_shiftSeries_iff_eq_zero 0).mpr rfl

/-- For any non-zero center, the shift series does not satisfy the substitution condition. -/
theorem not_hasSubst_shiftSeries_of_ne_zero {x₀ : F} (hx₀ : x₀ ≠ 0) :
    ¬ PowerSeries.HasSubst (shiftSeries x₀ H) :=
  fun h => hx₀ ((hasSubst_shiftSeries_iff_eq_zero x₀).mp h)

end SubstFieldCaveat

end ArkLib

#print axioms ArkLib.SubstFieldCaveat.hasSubst_iff_isNilpotent_constantCoeff
#print axioms ArkLib.SubstFieldCaveat.hasSubst_iff_constantCoeff_eq_zero_of_field
#print axioms ArkLib.SubstFieldCaveat.not_hasSubst_of_constantCoeff_ne_zero_of_field
#print axioms ArkLib.SubstFieldCaveat.constantCoeff_shiftSeries
#print axioms ArkLib.SubstFieldCaveat.fieldTo𝕃_injective
#print axioms ArkLib.SubstFieldCaveat.fieldTo𝕃_neg_eq_zero_iff
#print axioms ArkLib.SubstFieldCaveat.hasSubst_shiftSeries_iff_eq_zero
#print axioms ArkLib.SubstFieldCaveat.hasSubst_shiftSeries_zero
#print axioms ArkLib.SubstFieldCaveat.not_hasSubst_shiftSeries_of_ne_zero
