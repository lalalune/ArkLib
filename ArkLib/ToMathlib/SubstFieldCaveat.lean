/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import ArkLib.Data.Polynomial.RationalFunctions

/-!
# `PowerSeries.subst` over a field requires zero constant coefficient (brick L18 caveat)

This file isolates and proves the mathematical fact behind the **correctness caveat** for the
in-tree `γ` of BCIKS20 Appendix A.4 (`RationalFunctions.lean:2886`, Claim 5.9 / Claim A.2).

## The caveat

Mathlib defines `PowerSeries.HasSubst g := IsNilpotent (constantCoeff g)`
(`Mathlib/RingTheory/PowerSeries/Substitution.lean:38`).  `PowerSeries.subst g f` is only
*meaningful* (it agrees with the intended infinite sum, is a ring hom in `f`, has the expected
coefficients, etc.) under `HasSubst g`; when `HasSubst g` fails mathlib's `subst` falls back to a
junk default (it is defined through `MvPowerSeries.eval₂` with the non-`HasEval` branch giving `0`),
so the resulting object carries no mathematical content.

Over a **field** `K` the ring is reduced, so `IsNilpotent x ↔ x = 0`.  Hence
`HasSubst g ↔ constantCoeff g = 0` over a field: *a substituted series over a field must have zero
constant coefficient* — only "positive order" series may be substituted.

## Application to the in-tree `γ`

`γ` (`RationalFunctions.lean:2886`) is `PowerSeries.subst (mk shift) (mk α)` over the **field**
`𝕃 H`, where the shift series is the BCIKS substitution `X ↦ X − x₀`:
`shift 0 = fieldTo𝕃 (-x₀)`, `shift 1 = 1`, `shift t = 0` for `t ≥ 2`.  Its constant coefficient is
`fieldTo𝕃 (-x₀)`.  Since `fieldTo𝕃` is a ring hom *out of a field into the nontrivial field* `𝕃 H`
it is injective, so `fieldTo𝕃 (-x₀) = 0 ↔ x₀ = 0`.  Combining with the field characterization:

> `HasSubst (shiftSeries x₀ H) ↔ x₀ = 0`.

So for `x₀ ≠ 0` the substitution underlying `γ` does **not** satisfy `HasSubst`, and the in-tree
`γ` is mathlib's junk default — **ill-defined / not the intended series** — making Claim 5.9's
conclusion about it vacuous for the off-centre case.

This file proves exactly these facts (kernel-clean, no `sorry`).  See the verdict + recommended fix
below and in `research/proximity-prize/GRIND-LEDGER.md` (Findings section).

## Verdict and recommended fix

The in-tree `γ` is **genuinely incorrect for `x₀ ≠ 0`**: it `subst`s `X − x₀` (constant coeff
`-x₀ ≠ 0`) into the `X`-series over the field `𝕃 H`, which mathlib rejects via `HasSubst`, leaving
`γ = subst-default` (junk).  It is *only* well-defined in the centred case `x₀ = 0` (where the shift
series is literally `X` and `HasSubst X` holds).

The mathematically correct BCIKS object is the lift expressed as a power series in the **new**
variable `T = X − x₀` (a *recentering*), i.e. `γ = ∑ₜ αₜ · Tᵗ ∈ 𝕃 H⟦T⟧`, which is just
`PowerSeries.mk α` read in the recentered variable — **not** a `subst` of `X − x₀` into the
`X`-series.  Two honest formalizations:

* **(recommended)** redefine `γ := PowerSeries.mk (α x₀ R H hHyp)` (the coefficient sequence in the
  recentered variable `T`), and — if a relationship to the original `X` is needed — recenter via
  `Polynomial.taylor x₀` on any honest polynomial representative, *not* via `PowerSeries.subst`; or
* **(as done by `Claim59Conditional`)** keep the in-tree `subst` form but **carry**
  `hsubst : PowerSeries.HasSubst (shiftSeries x₀ H)` as an explicit hypothesis of every downstream
  lemma.  By `hasSubst_shiftSeries_iff_eq_zero` below this hypothesis is *equivalent to* `x₀ = 0`, so
  this route silently restricts the statement to the centred case and is sound only there.

Everything below is kernel-clean (no `sorry`/`admit`/`axiom`/`native_decide`); the `#print axioms`
at the end shows only `[propext, Classical.choice, Quot.sound]`.
-/

open Polynomial PowerSeries
open scoped Polynomial.Bivariate
open BCIKS20AppendixA BCIKS20AppendixA.ClaimA2

namespace ArkLib

namespace SubstFieldCaveat

/-! ## Step 1: the general fact — `HasSubst` over a field is "zero constant coefficient" -/

/-- `PowerSeries.HasSubst g` unfolds to `IsNilpotent (constantCoeff g)`; we record the convenient
`PowerSeries.constantCoeff` form (defeq via the `Unit`-indexed `MvPowerSeries`). -/
theorem hasSubst_iff_isNilpotent_constantCoeff {S : Type*} [CommRing S] (g : PowerSeries S) :
    PowerSeries.HasSubst g ↔ IsNilpotent (PowerSeries.constantCoeff g) := by
  unfold PowerSeries.HasSubst
  rfl

/-- **The field caveat.**  Over a field `K`, a power series may be substituted into iff its constant
coefficient vanishes: `HasSubst g ↔ constantCoeff g = 0`.  (A field is reduced, so nilpotent ⇔ zero.)
This is the precise sense in which `PowerSeries.subst` over a field needs a "positive order" series:
if `constantCoeff g ≠ 0`, `HasSubst g` is false and `subst g · ` is mathlib's junk default. -/
theorem hasSubst_iff_constantCoeff_eq_zero_of_field {K : Type*} [Field K] (g : PowerSeries K) :
    PowerSeries.HasSubst g ↔ PowerSeries.constantCoeff g = 0 := by
  rw [hasSubst_iff_isNilpotent_constantCoeff]
  exact isNilpotent_iff_eq_zero

/-- Contrapositive convenience form: a nonzero constant coefficient over a field obstructs
substitution. -/
theorem not_hasSubst_of_constantCoeff_ne_zero_of_field {K : Type*} [Field K] {g : PowerSeries K}
    (hg : PowerSeries.constantCoeff g ≠ 0) : ¬ PowerSeries.HasSubst g :=
  fun h => hg ((hasSubst_iff_constantCoeff_eq_zero_of_field g).mp h)

/-! ## Step 2: the BCIKS shift series `X ↦ X − x₀` and its constant coefficient

We reproduce the shift series literally as it appears inside the in-tree `γ`
(`RationalFunctions.lean:2886`). -/

variable {F : Type} [Field F]

/-- The BCIKS shift series `X ↦ X − x₀` underlying the in-tree `γ`:
`shift 0 = fieldTo𝕃 (-x₀)`, `shift 1 = 1`, `shift t = 0` for `t ≥ 2`.
This is the `PowerSeries.mk subst` appearing literally in `γ` (`RationalFunctions.lean:2886`); it
matches `Claim59Conditional.shiftSeries`. -/
noncomputable def shiftSeries (x₀ : F) (H : F[X][Y]) : PowerSeries (𝕃 H) :=
  PowerSeries.mk fun t =>
    match t with
    | 0 => fieldTo𝕃 (-x₀)
    | 1 => 1
    | _ => 0

/-- The constant coefficient of the BCIKS shift series is `fieldTo𝕃 (-x₀)`. -/
@[simp]
theorem constantCoeff_shiftSeries (x₀ : F) (H : F[X][Y]) :
    PowerSeries.constantCoeff (shiftSeries x₀ H) = fieldTo𝕃 (-x₀) := by
  unfold shiftSeries
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk]

/-- `fieldTo𝕃` is injective: it is a ring hom out of the field `F` into the nontrivial field
`𝕃 H` (nontrivial because `H` is irreducible of positive `Y`-degree). -/
theorem fieldTo𝕃_injective {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)] :
    Function.Injective (fieldTo𝕃 (H := H)) := by
  unfold fieldTo𝕃
  exact RingHom.injective _

/-- `fieldTo𝕃 (-x₀) = 0 ↔ x₀ = 0`, by injectivity of `fieldTo𝕃`. -/
theorem fieldTo𝕃_neg_eq_zero_iff {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (x₀ : F) : fieldTo𝕃 (H := H) (-x₀) = 0 ↔ x₀ = 0 := by
  rw [map_neg, neg_eq_zero]
  exact ⟨fun h => fieldTo𝕃_injective (by rw [h, map_zero]),
         fun h => by rw [h, map_zero]⟩

/-! ## Step 3: the corollary for the in-tree `γ` — `HasSubst` of the shift series ⟺ `x₀ = 0` -/

variable {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- **Corollary (the in-tree `γ` caveat).**  The BCIKS substitution `X ↦ X − x₀` underlying the
in-tree `γ` has zero constant coefficient — and hence satisfies mathlib's `HasSubst` over the field
`𝕃 H` — **iff `x₀ = 0`**.  For `x₀ ≠ 0` the substitution is invalid and the in-tree
`γ = subst (mk shift) (mk α)` is mathlib's junk default. -/
theorem hasSubst_shiftSeries_iff_eq_zero (x₀ : F) :
    PowerSeries.HasSubst (shiftSeries x₀ H) ↔ x₀ = 0 := by
  rw [hasSubst_iff_constantCoeff_eq_zero_of_field, constantCoeff_shiftSeries,
    fieldTo𝕃_neg_eq_zero_iff]

/-- The centred case: `HasSubst (shiftSeries 0 H)` always holds (the shift series is then `X`). -/
theorem hasSubst_shiftSeries_zero :
    PowerSeries.HasSubst (shiftSeries (0 : F) H) :=
  (hasSubst_shiftSeries_iff_eq_zero 0).mpr rfl

/-- The off-centre case: for `x₀ ≠ 0` the substitution underlying the in-tree `γ` is **invalid**. -/
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
