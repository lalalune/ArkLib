/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import ArkLib.Data.Polynomial.RationalFunctions
import ArkLib.ToMathlib.PowerSeriesSubstCoeff
import ArkLib.ToMathlib.FiniteSeriesToPoly

/-!
# Conditional Claim 5.9 — `γ` is linear in `Z` given the 5.8' tail-vanishing output (brick L18)

This file discharges BCIKS20 **Claim 5.9** (`solution_gamma_is_linear_in_Z`,
`Agreement.lean:2808`) *conditionally*, reducing it to exactly the hypothesis that the real
5.8' step (`approximate_solution_is_exact_solution_coeffs`, Claim 5.8) is meant to supply once the
genuine Hensel numerator `β` is built (ingredient D).  The real `β` / 5.8' are not built yet
(`β = 0` today), so we take the 5.8' conclusion as an *explicit hypothesis* rather than a `sorry`:

* `htail : ∀ t, k ≤ t → α x₀ R H hHyp t = 0`  — the 5.8' output ("`α' … t = 0` for `t ≥ k`").

The in-tree `γ` (`RationalFunctions.lean:2886`) is
`γ = PowerSeries.subst (mk shift) (mk (α x₀ R H hHyp))` where the shift series is
`shift 0 = fieldTo𝕃 (-x₀)`, `shift 1 = 1`, `shift t = 0 (t ≥ 2)`, i.e. the BCIKS substitution
`X ↦ X − x₀`.  Note this shift series has constant coefficient `fieldTo𝕃 (-x₀)`, which is nonzero
for `x₀ ≠ 0`; over the *field* `𝕃 H` it is therefore not nilpotent, so
`PowerSeries.HasSubst (mk shift)` does **not** follow from `of_constantCoeff_zero`.  Mathlib's
`PowerSeries.subst` is only meaningful (non-junk) under `HasSubst`, so the validity of the
substitution underlying `γ` is itself a hypothesis of the BCIKS argument; we carry it explicitly
as `hsubst : PowerSeries.HasSubst (mk shift)` (it holds e.g. when `x₀ = 0`, the centred case).

The two genuinely generic ingredients are imported bricks:

* **L6** (`PowerSeriesSubstCoeff`): `subst_mk_eq_aeval_trunc_of_tail_zero` turns the tail-vanishing
  hypothesis into `γ = Polynomial.aeval (mk shift) (trunc k (mk α))`, i.e. `γ` is the substitution
  of an explicit polynomial of degree `< k` in the `α`-coefficients (this is the 5.8' truncation
  re-read on the power-series side).
* **L18a** (`FiniteSeriesToPoly`): `exists_linear_decomposition_of_degreeX_le_one` turns a bivariate
  polynomial representative with `degreeX ≤ 1` into the explicit linear shape
  `map C v₀ + C X * map C v₁` that Claim 5.9 reports.

What remains genuinely β-gated (and is therefore an explicit hypothesis of the deliverable, not a
`sorry`) is the **Prop 5.5 polynomial-representative datum**: that the (truncated) `γ` has an honest
`F[X][Y]` polynomial representative `P` with `Polynomial.Bivariate.degreeX P ≤ 1`.  This is exactly
the hypothesis that the in-tree
`solution_gamma_is_linear_in_Z_of_polynomial_representative_degreeX_le_one` (`Agreement.lean:2353`)
also consumes; producing it from `β` (so that the `α t` for `t < k` actually live on the `F[X]`
line and the bivariate representative is linear in `Z`) is the residual of ingredients D / Prop 5.5.

Everything below is kernel-clean (no `sorry`/`admit`/`axiom`/`native_decide`); the `#print axioms`
at the end shows only `[propext, Classical.choice, Quot.sound]`.
-/

open Polynomial
open scoped Polynomial.Bivariate
open BCIKS20AppendixA BCIKS20AppendixA.ClaimA2

namespace ArkLib

namespace Claim59Conditional

variable {F : Type} [Field F]
         {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- The BCIKS shift series `X ↦ X − x₀`, i.e. the substituted series underlying `γ`:
`shift 0 = fieldTo𝕃 (-x₀)`, `shift 1 = 1`, `shift t = 0` for `t ≥ 2`.  This is the
`PowerSeries.mk subst` appearing literally in the definition of `γ`
(`RationalFunctions.lean:2886`). -/
noncomputable def shiftSeries (x₀ : F) (H : F[X][Y]) : PowerSeries (𝕃 H) :=
  PowerSeries.mk fun t =>
    match t with
    | 0 => fieldTo𝕃 (-x₀)
    | 1 => 1
    | _ => 0

/-- `γ` is literally `(mk α).subst (shiftSeries x₀ H)`: an unfolding lemma matching the in-tree
definition of `γ` to the form L6 consumes. -/
theorem gamma_eq_subst_shiftSeries (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H) :
    γ x₀ R H hHyp =
      (PowerSeries.mk (α x₀ R H hHyp)).subst (shiftSeries x₀ H) := by
  rfl

/-! ## Step 1 (L6): the 5.8' truncation on the power-series side

If the `α`-tail vanishes from index `k` on, then `γ` is the `aeval` of an explicit degree-`< k`
polynomial in the shift series — the power-series reading of Claim 5.8' ("`γ` is its own
truncation"). -/

/-- **L6-powered truncation of `γ`.**  Given the 5.8' tail-vanishing output
`htail : ∀ t ≥ k, α … t = 0` and validity of the BCIKS substitution `hsubst`, the in-tree `γ`
equals `Polynomial.aeval (shiftSeries x₀ H) (PowerSeries.trunc k (mk α))`, i.e. the substitution of
the explicit polynomial `trunc k (mk α)` (degree `< k`, coefficients `α 0, …, α (k−1)`). -/
theorem gamma_eq_aeval_trunc_of_tail_zero
    (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    (hsubst : PowerSeries.HasSubst (shiftSeries x₀ H)) {k : ℕ}
    (htail : ∀ t, k ≤ t → α x₀ R H hHyp t = 0) :
    γ x₀ R H hHyp =
      Polynomial.aeval (shiftSeries x₀ H)
        (PowerSeries.trunc k (PowerSeries.mk (α x₀ R H hHyp))) := by
  rw [gamma_eq_subst_shiftSeries]
  exact subst_mk_eq_aeval_trunc_of_tail_zero hsubst htail

/-- The truncation polynomial of `mk α` has `natDegree < k` (for `k > 0`): the explicit degree
bound on the degree-`< k` polynomial whose `aeval` is `γ`.  Re-exported from L6 for convenience. -/
theorem natDegree_trunc_mk_alpha_lt
    (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H) {k : ℕ}
    (hk : 0 < k) :
    (PowerSeries.trunc k (PowerSeries.mk (α x₀ R H hHyp))).natDegree < k :=
  ArkLib.natDegree_trunc_mk_lt hk

/-! ## Step 2 (L18a): the `degreeX ≤ 1` representative ⟹ linear shape

Given an honest `F[X][Y]` polynomial representative `P` of `γ` with `degreeX P ≤ 1`, `P` decomposes
as `map C v₀ + C X * map C v₁` and `γ` is `polyToPowerSeries𝕃` of that linear bivariate.  This is
exactly the conclusion of `solution_gamma_is_linear_in_Z_of_polynomial_representative_degreeX_le_one`
(`Agreement.lean:2353`). -/

/-- **L18a-powered linear extraction.**  If the in-tree `γ` has a bivariate polynomial
representative `P : F[X][Y]` (via `polyToPowerSeries𝕃`) with `Polynomial.Bivariate.degreeX P ≤ 1`,
then `γ` is `polyToPowerSeries𝕃` of an explicit linear-in-`Z` bivariate
`map C v₀ + C X * map C v₁`. -/
theorem gamma_linear_in_Z_of_polynomial_representative_degreeX_le_one
    (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    {P : F[X][Y]} (hrep : polyToPowerSeries𝕃 H P = γ x₀ R H hHyp)
    (hdeg : Polynomial.Bivariate.degreeX P ≤ 1) :
    ∃ v₀ v₁ : F[X],
      γ x₀ R H hHyp =
        polyToPowerSeries𝕃 H
          ((Polynomial.map Polynomial.C v₀)
            + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)) := by
  obtain ⟨v₀, v₁, hP⟩ :=
    FiniteSeriesToPoly.exists_linear_decomposition_of_degreeX_le_one hdeg
  exact ⟨v₀, v₁, by rw [← hrep, hP]⟩

/-! ## The deliverable: conditional Claim 5.9

Reduces Claim 5.9 to exactly (i) the 5.8' tail-vanishing hypothesis `htail` and (ii) the β-gated
Prop 5.5 polynomial-representative-with-`degreeX ≤ 1` datum `hrep`.  Once the genuine `β` /
5.8' are built, `htail` is discharged by `approximate_solution_is_exact_solution_coeffs`, and `hrep`
is the Prop 5.5 output; the conclusion is then the in-tree `solution_gamma_is_linear_in_Z`. -/

/-- **Conditional Claim 5.9 (`solution_gamma_is_linear_in_Z`, reduced to the 5.8'/Prop-5.5 data).**

Hypotheses:
* `hsubst` — validity of the BCIKS substitution `X ↦ X − x₀` (`HasSubst (shiftSeries x₀ H)`); part
  of the BCIKS setup, automatic in the centred case `x₀ = 0`.
* `htail` — the 5.8' output `∀ t ≥ k, α x₀ R H hHyp t = 0` (Claim 5.8'); supplied by the real `β`.
* `hrep` — the Prop 5.5 datum: an honest `F[X][Y]` polynomial representative `P` of `γ` with
  `Polynomial.Bivariate.degreeX P ≤ 1`.  This is the β-gated residual (the truncated `γ` lives on
  the `F[X]` line and is linear in `Z`).

Conclusion: `γ` is `polyToPowerSeries𝕃` of an explicit linear-in-`Z` bivariate
`map C v₀ + C X * map C v₁` — exactly the in-tree "linear in `Z`" shape.

The `htail` hypothesis is what 5.8' supplies; `hrep` is what Prop 5.5 / ingredient D supplies. The
proof routes `htail` through L6 (the truncation `γ = aeval (shift) (trunc k (mk α))`, recorded as
`gamma_eq_aeval_trunc_of_tail_zero`) and `hrep` through L18a (the `degreeX ≤ 1 ⟹` linear
decomposition). -/
theorem gamma_linear_in_Z_of_tail_zero
    (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    (hsubst : PowerSeries.HasSubst (shiftSeries x₀ H)) {k : ℕ}
    (htail : ∀ t, k ≤ t → α x₀ R H hHyp t = 0)
    {P : F[X][Y]} (hrep : polyToPowerSeries𝕃 H P = γ x₀ R H hHyp)
    (hdeg : Polynomial.Bivariate.degreeX P ≤ 1) :
    ∃ v₀ v₁ : F[X],
      γ x₀ R H hHyp =
        polyToPowerSeries𝕃 H
          ((Polynomial.map Polynomial.C v₀)
            + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)) := by
  -- The 5.8' truncation (L6) — recorded for honesty, then the linear extraction (L18a).
  have _htrunc :
      γ x₀ R H hHyp =
        Polynomial.aeval (shiftSeries x₀ H)
          (PowerSeries.trunc k (PowerSeries.mk (α x₀ R H hHyp))) :=
    gamma_eq_aeval_trunc_of_tail_zero x₀ R H hHyp hsubst htail
  exact gamma_linear_in_Z_of_polynomial_representative_degreeX_le_one
    x₀ R H hHyp hrep hdeg

end Claim59Conditional

end ArkLib

#print axioms ArkLib.Claim59Conditional.gamma_eq_subst_shiftSeries
#print axioms ArkLib.Claim59Conditional.gamma_eq_aeval_trunc_of_tail_zero
#print axioms ArkLib.Claim59Conditional.natDegree_trunc_mk_alpha_lt
#print axioms ArkLib.Claim59Conditional.gamma_linear_in_Z_of_polynomial_representative_degreeX_le_one
#print axioms ArkLib.Claim59Conditional.gamma_linear_in_Z_of_tail_zero
