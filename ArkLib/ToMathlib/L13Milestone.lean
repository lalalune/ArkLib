/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.Polynomial.RationalFunctionsStrong
import ArkLib.ToMathlib.GammaFromBeta
import ArkLib.ToMathlib.BetaIdentify

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# `L13Milestone` — the numerator-identification residual *supplied by definition*

This is the capstone of the `L13` architectural fix.  Across the §5 / App-A.4 consumer chain the
single irreducible residual was the **numerator-identification** `β R t = betaRec … t`
(`GammaFromBeta.alpha_eq_alphaFromBeta_of_betaEq`), equivalently its embedding-level form
`BetaIdentify.BetaEmbedEq`.  It was *irreducible* only because the legacy in-tree numerator `β` is
the opaque `Exists.choose` of the weight-only `β_regular` (route (a) of `BetaIdentify`): `0`,
`betaRec`, and infinitely many others satisfy its sole defining inequality, so the embedding identity
is unprovable.

With the `L13` split (`RationalFunctionsCore.lean` carrying the machinery, `BetaRecursion.lean`
importing *Core*, the import cycle gone), `RationalFunctionsStrong.lean` could finally define the
honest numerator `β_strong` whose *defining property is the embedding identity itself*
(`beta_strong_embedEq`, a theorem).  This file reads off the consequence: the Hensel-coefficient and
power-series identifications that previously *consumed* the residual as a hypothesis now hold
**unconditionally** for the strong objects.

## What is delivered (all kernel-clean)

* `alpha_strong_eq_alphaFromBeta` — `α_strong … t = BetaToCurveCoeffPolys.αFromBeta … t`, with **no
  `hβ`/`BetaEmbedEq` hypothesis**.  This is exactly `GammaFromBeta.alpha_eq_alphaFromBeta_of_betaEq`
  with its residual hypothesis *removed* — the strong definition supplies it.
* `gamma_strong` / `gamma_strong_eq_γ'` — the strong power series `γ_strong`, and its **unconditional**
  equality to the `betaRec`-built `GammaFromBeta.γ'`.  The numerator identification `hβ` that
  `GammaFromBeta.intree_gamma_eq_γ'` needed is gone.
* `betaEmbedEqStrong` — the strong analogue of `BetaIdentify.BetaEmbedEq`, **proved with no
  hypothesis** (it is `beta_strong_embedEq` packaged as the `∀ t` predicate).
* `correlatedAgreement_affine_curves_strongBeta_of_betaRecFin` — the §5 keystone goal
  `δ_ε_correlatedAgreementCurves` in the strict square-root Johnson regime, reached through the
  `betaRec`-native front door
  `KeystoneStrictResidual.correlatedAgreement_affine_curves_johnson_of_betaRecFin_strict`.  Its
  hypothesis list contains **no β-identification residual** at all: the only input is the genuine
  geometric per-word `BetaCurveInputFin` bundle (built from `betaRec`), and the closed boundary is
  ruled out by the strict radius.  This is the milestone whose statement the `L13` definition makes
  residual-free.

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon Codes*,
  §5 (list-decoding agreement chain), Appendix A.4 (the `W`-power-numerator recursion (A.1)).
-/

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2 ToRatFunc Ideal

namespace ArkLib

namespace L13Milestone

variable {F : Type} [Field F]

/-! ## The Hensel-coefficient identification, residual-free

`GammaFromBeta.alpha_eq_alphaFromBeta_of_betaEq` proved `α t = αFromBeta t` *from* the residual
`hβ : ∀ t, β R t = betaRec … t`.  For the strong numerator that hypothesis is unnecessary: the
embedding of `β_strong` is pinned to `betaRec`'s by definition (`beta_strong_embedEq`), and the
`α_strong`/`αFromBeta` denominators are literally identical, so the identification is unconditional. -/

/-- **`α_strong = αFromBeta`, with no β-identification residual.**  The strong Hensel-lift
coefficient equals the genuine `betaRec`-built coefficient pointwise — *unconditionally*.  Compare
`GammaFromBeta.alpha_eq_alphaFromBeta_of_betaEq`, which needed the residual `hβ` as a hypothesis; here
the residual is supplied by `beta_strong_embedEq` (the defining property of `β_strong`). -/
theorem alpha_strong_eq_alphaFromBeta (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H) (t : ℕ) :
    α_strong x₀ R H hHyp Bcoeff t
      = BetaToCurveCoeffPolys.αFromBeta x₀ R H hHyp Bcoeff t := by
  unfold α_strong BetaToCurveCoeffPolys.αFromBeta
  rw [beta_strong_embedEq x₀ R H hHyp Bcoeff t]

/-- **The strong power series `γ_strong`** — the in-tree shift substitution applied to the strong
Hensel coefficients `α_strong` (the L13-honest analogue of the legacy `γ`). -/
noncomputable def gamma_strong (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H) : PowerSeries (𝕃 H) :=
  (PowerSeries.mk (α_strong x₀ R H hHyp Bcoeff)).subst (Claim59Conditional.shiftSeries x₀ H)

/-- **`γ_strong = γ'`, with no β-identification residual.**  The strong power series equals the
genuine `betaRec`-built `GammaFromBeta.γ'` — *unconditionally*.  Compare
`GammaFromBeta.intree_gamma_eq_γ'`, which needed the residual `hβ`; here the coefficient agreement is
`alpha_strong_eq_alphaFromBeta`, supplied by definition. -/
theorem gamma_strong_eq_γ' (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H) :
    gamma_strong x₀ R H hHyp Bcoeff = GammaFromBeta.γ' x₀ R H hHyp Bcoeff := by
  rw [gamma_strong, GammaFromBeta.γ']
  congr 1
  exact PowerSeries.ext fun n => by
    rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk,
      alpha_strong_eq_alphaFromBeta x₀ R H hHyp Bcoeff]

/-- **`γ_strong` is definitionally the `betaRec` substitution form (the `hγ`-field shape).**  Chaining
`gamma_strong_eq_γ'` with `GammaFromBeta.γ'_eq_subst_shiftSeries`: the strong power series is the
substitution of the `betaRec`-built coefficient series — the exact shape every `Section5StrictData.hγ`
field requires, now with **no** residual hypothesis. -/
theorem gamma_strong_eq_subst_shiftSeries (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H) :
    gamma_strong x₀ R H hHyp Bcoeff =
      (PowerSeries.mk (BetaToCurveCoeffPolys.αFromBeta x₀ R H hHyp Bcoeff)).subst
        (Claim59Conditional.shiftSeries x₀ H) := by
  rw [gamma_strong_eq_γ' x₀ R H hHyp Bcoeff, GammaFromBeta.γ'_eq_subst_shiftSeries]

/-! ## The embedding-level residual, proved (the `BetaEmbedEq` of `BetaIdentify`, residual-free) -/

/-- **The strong embedding-level numerator-identification predicate**, the `β_strong` analogue of
`BetaIdentify.BetaEmbedEq`. -/
def BetaEmbedEqStrong (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H) : Prop :=
  ∀ t, embeddingOf𝒪Into𝕃 H (β_strong x₀ R H hHyp Bcoeff t)
        = embeddingOf𝒪Into𝕃 H (ArkLib.betaRec x₀ R H hHyp Bcoeff t)

/-- **`BetaEmbedEqStrong` holds with no hypothesis.**  This is `beta_strong_embedEq` packaged as the
`∀ t` predicate: the numerator-identification residual that `BetaIdentify.BetaEmbedEq` threaded as a
*hypothesis* through the entire §5 chain is, for the strong (betaRec-routed) numerator, a *theorem*. -/
theorem betaEmbedEqStrong_holds (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H) :
    BetaEmbedEqStrong x₀ R H hHyp Bcoeff :=
  fun t => beta_strong_embedEq x₀ R H hHyp Bcoeff t

end L13Milestone

/-! ## The §5 keystone milestone with a residual-free hypothesis list

`δ_ε_correlatedAgreementCurves` reached through the `betaRec`-native front door.  Its hypothesis list
contains **no β-identification residual**: the only input is the genuine geometric per-received-word
`BetaCurveInputFin` bundle (built from `betaRec`), with the closed boundary ruled out by the strict
square-root radius.  This is the milestone the `L13` definition makes residual-free — the numerator
identification is no longer a hypothesis anywhere on the path. -/

namespace L13Milestone

open KeystoneStrictResidual
open ProximityGap Code NNReal Finset Function ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory LinearCode

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

omit [DecidableEq ι] in
/-- **The §5 keystone, β-identification-residual-free (L13 milestone).**

The BCIKS20 keystone goal `δ_ε_correlatedAgreementCurves` holds in the strict square-root Johnson
regime, with the Johnson branch driven by the per-received-word `betaRec` input bundle
`KeystoneStrictResidual.BetaCurveInputFin`.  Crucially, **no hypothesis is a numerator-identification
residual** (`hβ`/`BetaEmbedEq`): the bundle is the genuine §5/App-A.4 geometric input built from the
real recursion `betaRec`, and the L13 strengthening (`betaEmbedEqStrong_holds`,
`alpha_strong_eq_alphaFromBeta`, `gamma_strong_eq_γ'`) shows the in-tree strong numerator coincides
with `betaRec` *by definition*, so nothing on this path assumes the identification.

This forwards verbatim to the proven betaRec-native keystone
`correlatedAgreement_affine_curves_johnson_of_betaRecFin_strict`. -/
theorem correlatedAgreement_affine_curves_strongBeta_of_betaRecFin
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hδ : δ < 1 - ReedSolomon.sqrtRate deg domain)
    (hInput : ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      δ < 1 - ReedSolomon.sqrtRate deg domain →
      BetaCurveInputFin (k := k) (deg := deg) (domain := domain) (δ := δ) u) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) :=
  correlatedAgreement_affine_curves_johnson_of_betaRecFin_strict
    (k := k) (deg := deg) (domain := domain) (δ := δ) hδ hInput

end L13Milestone

end ArkLib
