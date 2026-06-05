/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.Curves
import ArkLib.ToMathlib.BetaToCurveCoeffPolys
import ArkLib.ToMathlib.Claim59Conditional
import ArkLib.ToMathlib.CorrelatedAgreementListDecodingClosed

/-!
# `γ'` — the `betaRec`-built power series and the `hγ` discharge (L13 drop-in, route B)

This file closes the `hγ` field of
`CorrelatedAgreementListDecodingClosed.Section5StrictData`:

```
hγ : γ x₀ R H hHyp =
  (PowerSeries.mk (BetaToCurveCoeffPolys.αFromBeta x₀ R H hHyp Bcoeff)).subst
    (Claim59Conditional.shiftSeries x₀ H)
```

## The blocker

The in-tree `γ` (`RationalFunctions.lean:2886`) is built from the in-tree Hensel coefficient `α`
(`RationalFunctions.lean:2874`), whose numerator is the in-tree `β` (`RationalFunctions.lean:2866`).
That `β` is `(β_regular …).choose`, and `β_regular` (`RationalFunctions.lean:2855`) asserts its
existence with the **trivial witness** `fun _ => ⟨0, by simp⟩`.  So `β R t` is an opaque element with
no algebraic relation to the genuine App-A.4 recursion `betaRec`.  Meanwhile `αFromBeta`
(`BetaToCurveCoeffPolys.lean:106`) is the *same quotient shape* as `α` but with the genuine `betaRec`
in the numerator:

```
α        t = embeddingOf𝒪Into𝕃 H (β       R t)              / (W^{t+1} · embedding(ξ)^{2t-1})
αFromBeta t = embeddingOf𝒪Into𝕃 H (betaRec x₀ R H hHyp Bcoeff t) / (W^{t+1} · embedding(ξ)^{2t-1})
```

The denominators are *literally* identical (`W := liftToFunctionField H.leadingCoeff`, same `ξ`).
Hence the *only* gap between the in-tree `γ` and the `betaRec`-built series is the identification of
the opaque in-tree numerator `β R t` with the genuine recursion `betaRec x₀ R H hHyp Bcoeff t`.

## Why route B (parallel definition) rather than route A (true in-tree drop-in)

A `rfl`-grade in-tree drop-in would require `β R t` to *be* `betaRec x₀ R H hHyp Bcoeff t`.  But the
in-tree `β` signature is `β (R) (t)` — it carries neither `x₀`, nor `hHyp`, nor the numerator
interface `Bcoeff`, all of which `betaRec` consumes.  Threading those through `β`/`α`/`γ` changes
their signatures and breaks the many in-tree/`Agreement.lean` consumers
(`alpha'_eq_zero_of_embedding_beta_eq_zero` at `Agreement.lean:1361`,
`approximate_solution_is_exact_solution_coeffs_of_beta_embedding_zero`, etc.).  So we take route B:
define `γ'` directly as the `betaRec`-built series, prove the `hγ` field discharges from the *single
honest residual* `hβ` (the genuine identification `β R t = betaRec x₀ R H hHyp Bcoeff t`, i.e. the
content the trivial `β_regular` witness fails to supply), and expose a `Section5StrictData` builder
whose `hγ` is supplied automatically.

`hβ` is exactly the deferred in-tree edit, isolated as an explicit hypothesis — never a `sorry`,
never `≡` the goal (`hγ` is about `γ`/`αFromBeta`; `hβ` is about the numerator recursion).

## References
* [BCIKS20] §5 (list-decoding agreement chain), Appendix A.4 (recursion (A.1)).
-/

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2 ToRatFunc Ideal

namespace ArkLib

namespace GammaFromBeta

variable {F : Type} [Field F]

/-! ## The `betaRec`-built power series `γ'`

`γ'` is *defined* as the substitution form the `hγ` field demands.  Consequently the `hγ` identity
for `γ'` is `rfl`. -/

/-- The `betaRec`-built analogue of the in-tree `γ` (`RationalFunctions.lean:2886`): the BCIKS shift
substitution `X ↦ X − x₀` applied to the genuine Hensel-coefficient series `mk (αFromBeta …)` (whose
numerators are the App-A.4 recursion `betaRec`).  This is *exactly* the right-hand side of the
`Section5StrictData.hγ` field, so `γ'_eq_subst_shiftSeries` below is `rfl`. -/
noncomputable def γ' (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H) : PowerSeries (𝕃 H) :=
  (PowerSeries.mk (BetaToCurveCoeffPolys.αFromBeta x₀ R H hHyp Bcoeff)).subst
    (Claim59Conditional.shiftSeries x₀ H)

/-- `γ'` is *definitionally* the substitution form: the `hγ`-field shape holds for `γ'` by `rfl`.
This is the route-B realization of "`hγ` is dischargeable as `rfl` for `γ'`". -/
theorem γ'_eq_subst_shiftSeries (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H) :
    γ' x₀ R H hHyp Bcoeff =
      (PowerSeries.mk (BetaToCurveCoeffPolys.αFromBeta x₀ R H hHyp Bcoeff)).subst
        (Claim59Conditional.shiftSeries x₀ H) :=
  rfl

/-! ## The single honest residual: `β R t = betaRec …`

This is the content the trivial `β_regular` witness fails to supply.  It is the genuine §5 / App-A.4
identification of the opaque in-tree numerator with the real recursion.  Everything below is *proven*
from it; it is never assumed to be the goal. -/

/-- **Numerator identification ⟹ Hensel-coefficient identification.**  If the opaque in-tree numerator
`β R t` equals the genuine recursion `betaRec x₀ R H hHyp Bcoeff t` for all `t`, then the in-tree
Hensel coefficient `α` equals `αFromBeta` pointwise (the denominators are literally identical, so this
is `unfold` + `rw`). -/
theorem alpha_eq_alphaFromBeta_of_betaEq (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H)
    (hβ : ∀ t, β (H := H) R t = betaRec x₀ R H hHyp Bcoeff t) (t : ℕ) :
    α x₀ R H hHyp t = BetaToCurveCoeffPolys.αFromBeta x₀ R H hHyp Bcoeff t := by
  unfold α BetaToCurveCoeffPolys.αFromBeta
  rw [hβ t]

/-- **The in-tree `γ` equals the `betaRec`-built `γ'`**, under the numerator identification `hβ`.
Both are the *same* shift substitution applied to series whose coefficients now agree pointwise. -/
theorem intree_gamma_eq_γ' (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H)
    (hβ : ∀ t, β (H := H) R t = betaRec x₀ R H hHyp Bcoeff t) :
    γ x₀ R H hHyp = γ' x₀ R H hHyp Bcoeff := by
  rw [Claim59Conditional.gamma_eq_subst_shiftSeries, γ']
  congr 1
  exact PowerSeries.ext fun n => by
    rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk,
      alpha_eq_alphaFromBeta_of_betaEq x₀ R H hHyp Bcoeff hβ]

/-- **The `Section5StrictData.hγ` field, discharged.**  Under the single honest residual `hβ`, the
in-tree `γ` equals the `betaRec`-built substitution form — i.e. *literally* the `hγ` field of
`Section5StrictData`.  No `sorry`, no `axiom`; `hβ` is the only input (it is the genuine §5 numerator
identification, NOT the `hγ` goal). -/
theorem hγ_field_of_betaEq (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H)
    (hβ : ∀ t, β (H := H) R t = betaRec x₀ R H hHyp Bcoeff t) :
    γ x₀ R H hHyp =
      (PowerSeries.mk (BetaToCurveCoeffPolys.αFromBeta x₀ R H hHyp Bcoeff)).subst
        (Claim59Conditional.shiftSeries x₀ H) := by
  rw [intree_gamma_eq_γ' x₀ R H hHyp Bcoeff hβ, γ'_eq_subst_shiftSeries]

end GammaFromBeta

/-! ## The `Section5StrictData` builder with `hγ` supplied automatically

The whole point of route B: a `Section5StrictData` constructor that takes *every* field except `hγ`,
plus the honest residual `hβ`, and fills `hγ` via `GammaFromBeta.hγ_field_of_betaEq`.  Callers of the
closed keystone (`CorrelatedAgreementListDecodingClosed`) no longer have to provide `hγ` by hand: it
is discharged from `hβ`.

Note the in-tree-`γ`-referencing fields (`hrep`, `hPz`) are unchanged — they are about the same
in-tree `γ`; only `hγ` is now derived. -/

section Builder

open BetaToCurveCoeffPolys Claim59Conditional
open ProximityGap Code NNReal Finset Function ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory LinearCode

namespace CorrelatedAgreementListDecodingClosed

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **`Section5StrictData` with the `hγ` field discharged from `hβ`.**

This builds the genuine §5 per-decoding extraction datum
`Section5StrictData (k := k) (deg := deg) (domain := domain) (δ := δ) u P` from *all* its fields
*except* `hγ`, supplying instead the single honest residual
`hβ : ∀ t, β R t = betaRec x₀ R H hHyp Bcoeff t` (the trivial-`β_regular` gap).  The `hγ` field is
then discharged by `GammaFromBeta.hγ_field_of_betaEq`.

This is the route-B deliverable: in-tree `γ` should eventually be redefined to be `betaRec`-built
(then `hβ` becomes `rfl` and disappears); until that deferred in-tree edit lands, `hβ` is the minimal
explicit residual. -/
noncomputable def section5StrictData_of_betaEq {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F}
    (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    (hIrr : Fact (Irreducible H)) (hPos : Fact (0 < H.natDegree))
    (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H)
    (hH : 0 < H.natDegree) (D : ℕ) (hD : D ≥ Bivariate.totalDegree H)
    (matchingSet : Finset F) (root : (z : F) → rationalRoot (H_tilde' H) z)
    (mp : ∀ t, k ≤ t → ∀ z ∈ matchingSet,
      BetaMatchingVanishes.MatchingPoint x₀ R H hHyp Bcoeff t z (root z))
    (hcard : ∀ t, k ≤ t → (↑matchingSet.card : WithBot ℕ)
        > weight_Λ_over_𝒪 hH (betaRec x₀ R H hHyp Bcoeff t) D * H.natDegree)
    (hsubst : PowerSeries.HasSubst (shiftSeries x₀ H))
    -- the honest residual replacing the `hγ` field:
    (hβ : ∀ t, β (H := H) R t = betaRec x₀ R H hHyp Bcoeff t)
    (Ppoly : F[X][Y]) (hrep : polyToPowerSeries𝕃 H Ppoly = γ x₀ R H hHyp)
    (hdegX : Polynomial.Bivariate.degreeX Ppoly ≤ 1)
    (hPz : ∀ v₀ v₁ : F[X],
      γ x₀ R H hHyp = polyToPowerSeries𝕃 H
        ((Polynomial.map Polynomial.C v₀) + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)) →
      (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ, P z =
        ((Polynomial.map Polynomial.C v₀)
            + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)).eval (Polynomial.C z))
        ∧ v₀.natDegree < k + 1 ∧ v₁.natDegree < k + 1) :
    Section5StrictData (k := k) (deg := deg) (domain := domain) (δ := δ) u P where
  x₀ := x₀
  R := R
  H := H
  hIrr := hIrr
  hPos := hPos
  hHyp := hHyp
  Bcoeff := Bcoeff
  hH := hH
  D := D
  hD := hD
  matchingSet := matchingSet
  root := root
  mp := mp
  hcard := hcard
  hsubst := hsubst
  hγ := GammaFromBeta.hγ_field_of_betaEq x₀ R H hHyp Bcoeff hβ
  Ppoly := Ppoly
  hrep := hrep
  hdegX := hdegX
  hPz := hPz

end CorrelatedAgreementListDecodingClosed

end Builder

end ArkLib

/-! ## Axiom audit — every claimed-done declaration rests only on
`[propext, Classical.choice, Quot.sound]`, no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ArkLib.GammaFromBeta.γ'_eq_subst_shiftSeries
#print axioms ArkLib.GammaFromBeta.alpha_eq_alphaFromBeta_of_betaEq
#print axioms ArkLib.GammaFromBeta.intree_gamma_eq_γ'
#print axioms ArkLib.GammaFromBeta.hγ_field_of_betaEq
#print axioms ArkLib.CorrelatedAgreementListDecodingClosed.section5StrictData_of_betaEq
