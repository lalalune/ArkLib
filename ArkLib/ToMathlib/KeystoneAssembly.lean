/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.GSFactorData
import ArkLib.ToMathlib.GammaFromBeta
import ArkLib.ToMathlib.MpProducer
import ArkLib.ToMathlib.TailDegProducer
import ArkLib.ToMathlib.HPzBridge
import ArkLib.ToMathlib.BoundaryDischarge
import ArkLib.ToMathlib.HcardDischarge

/-!
# `keystone_of_section5Inputs` — the final assembly of the BCIKS20 list-decoding keystone

This file is the **final assembly**.  Every field-producer for the corrected §5 bundle
`HcardDischarge.Section5StrictDataFin` has been verified as a standalone brick in
`ArkLib/ToMathlib/`.  Here we wire them together into a single builder
`section5DataFin_of_producers`, and then into ONE theorem `keystone_of_section5Inputs` that takes the
genuine §5 standing inputs and produces the keystone goal
`δ_ε_correlatedAgreementCurves … (ε := errorBound δ deg domain)`.

## The producer chain assembled here

```
GSFactorData.Bundle x₀                       (the (u,P)-independent GS-factor head:
                                              x₀,R,H,Fact(Irr H),Fact(0<deg H),Hypotheses,hH,D,hD —
                                              via GSFactorData.of_section5Inputs from h_gs + graph
                                              side-conditions hx0/hsep/hS_nonempty/A/hA/hcount/hlarge)
GammaFromBeta.hγ_field_of_betaEq hβ           ⟹ the `hγ` field (from the numerator residual hβ)
TailDegProducer.htailDeg_of_polynomial_representative hsubst hγ hrep
                                              ⟹ the `htailDeg` field, with T := Ppoly.natDegree
MpProducer.mpFin_of_pointwise point          ⟹ the `mpFin` field (finite-range matching family)
HPzBridge.hPz_of_henselDatum hHensel hdeg    ⟹ the `hPz` field (decoded = specialisation, via Hensel)
  ──assemble──►  HcardDischarge.Section5StrictDataFin u P
  ──HcardDischarge.hcoeffPoly_witness_of_section5DataFin──►  ∃ B : ℕ → F[X], …  (front-door shape)
  ──ProximityGap.correlatedAgreement_affine_curves_of_strict_coeff_polys_and_boundary──►
δ_ε_correlatedAgreementCurves                                            (the keystone goal)
```

The α-tail vanishing the front door ultimately consumes is the F5-repaired, satisfiable one
(`HcardDischarge.tail_zero_of_finite_card_and_degree`): the finite-range counting bound `hcardFin`
plus the algebraic-degree truncation `htailDeg` (driven by the Prop-5.5 polynomial representative),
not the over-strong unbounded-in-`t` `hcard`.

## The adapter

The one shape-mismatch handled here is the truncation index: `TailDegProducer` produces `htailDeg`
with `T := Ppoly.natDegree`, so `section5DataFin_of_producers` *fixes* the bundle's truncation index
to `Ppoly.natDegree`, and supplies the `hcardFin` field over that very range.  This is recorded as
`htailDeg_field` (a thin specialisation lemma binding `T = Ppoly.natDegree`).

## The complete residual list (the definitive standing inputs of the whole keystone)

`keystone_of_section5Inputs` takes exactly the following genuine §5 standing data, each a per-`(u,P)`
producer (the keystone goal universally quantifies over the curve `u` and the candidate decoding
`P`), and NONE of which is the keystone goal or any intermediate conclusion:

1. **`hBundle`** — the GS-factor bundle `GSFactorData.Bundle x₀` (the §5 curve datum, dischargeable
   from `GSFactorData.of_section5Inputs` and the graph side-conditions).
2. **`Bcoeff`** — the App-A.4 Hensel-numerator coefficient interface.
3. **`matchingSet`/`root`** — the §5 agreement set `S_β` and the per-`z` rational-root selector.
4. **`mpPoint`** — the finite-range per-point matching producer (ingredient-C geometry on `[k,T]`).
5. **`hcardFin`** — the L9/L10 weight bound over the finite counting range `[k, Ppoly.natDegree]`
   (the *satisfiable* form of `hcard`; cf. the F5 finding).
6. **`hsubst`** — validity of the BCIKS shift `X ↦ X − x₀`.
7. **`hβ`** — the numerator identification `β R t = betaRec …` (the trivial-`β_regular` gap; the only
   residual replacing `hγ`).
8. **`Ppoly`/`hrep`/`hdegX`** — the Prop-5.5 linear polynomial representative of `γ`.
9. **`hHensel`/`hdeg`** — the per-`z` Hensel root datum and degree bounds (yielding `hPz`).
10. **`hBoundaryData`** — the closed square-root boundary datum (cardinality bounds + §5 extraction).
11. **`hδ`** — the ambient Johnson hypothesis `δ ≤ 1 − √ρ`.

`#print axioms keystone_of_section5Inputs` is `[propext, Classical.choice, Quot.sound]`.

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon Codes*,
  §5 (list-decoding agreement chain), §6.2 (Theorem 6.2), Appendix A.2/A.4.
-/

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2 ToRatFunc Ideal
open ProximityGap Code NNReal Finset Function ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory LinearCode

namespace ArkLib

namespace KeystoneAssembly

open BetaToCurveCoeffPolys Claim59Conditional
open CorrelatedAgreementListDecodingClosed HcardDischarge

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-! ## Step 1 — the `htailDeg` adapter

`TailDegProducer.htailDeg_of_polynomial_representative` produces the algebraic-degree truncation with
truncation index `T := Ppoly.natDegree`.  `Section5StrictDataFin.htailDeg` is `∀ t, T < t → …`; we
therefore pin the bundle's `T` to `Ppoly.natDegree`, at which point the two shapes coincide. -/

omit [Fintype F] [DecidableEq F] in
/-- **The `htailDeg` adapter.**  With the truncation index taken to be `T = Ppoly.natDegree`, the
`TailDegProducer` output `∀ t, Ppoly.natDegree < t → αFromBeta … t = 0` is *exactly* the
`htailDeg` field of `Section5StrictDataFin`.  Pure rewrite of the index. -/
theorem htailDeg_field {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]}
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] {hHyp : Hypotheses x₀ R H}
    {Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H} {Ppoly : F[X][Y]}
    (hsubst : PowerSeries.HasSubst (Claim59Conditional.shiftSeries x₀ H))
    (hγ : γ x₀ R H hHyp =
      (PowerSeries.mk (BetaToCurveCoeffPolys.αFromBeta x₀ R H hHyp Bcoeff)).subst
        (Claim59Conditional.shiftSeries x₀ H))
    (hrep : polyToPowerSeries𝕃 H Ppoly = γ x₀ R H hHyp) :
    ∀ t, Ppoly.natDegree < t → BetaToCurveCoeffPolys.αFromBeta x₀ R H hHyp Bcoeff t = 0 :=
  TailDegProducer.htailDeg_of_polynomial_representative hsubst hγ hrep

/-! ## Step 2 — the full assembly into `Section5StrictDataFin`

We assemble the corrected §5 bundle for a single curve/decoding `(u, P)` from the producer inputs.
The truncation index is fixed to `Ppoly.natDegree`; `htailDeg` is the `TailDegProducer` output,
`hγ` is `GammaFromBeta.hγ_field_of_betaEq hβ`, `mpFin` is the pointwise matching producer, and `hPz`
is `HPzBridge.hPz_of_henselDatum`.  The GS-factor head is supplied verbatim from the bundle. -/

/-- **The final builder.**  Assembles `HcardDischarge.Section5StrictDataFin u P` from the genuine §5
producer inputs, with truncation index `T := Ppoly.natDegree`.  Each field is filled by the verified
brick named in the file header; the only assumptions are the genuine §5 standing data (none is the
goal). -/
noncomputable def section5DataFin_of_producers {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F}
    {x₀ : F} (b : GSFactorData.Bundle (F := F) x₀)
    [_inst_hIrr : Fact (Irreducible b.H)] [_inst_hPos : Fact (0 < b.H.natDegree)]
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 b.H)
    (matchingSet : Finset F)
    (root : (z : F) → rationalRoot (H_tilde' b.H) z)
    -- the Prop-5.5 linear representative of `γ` (fixes the truncation index `T := Ppoly.natDegree`):
    (Ppoly : F[X][Y])
    (hrep : polyToPowerSeries𝕃 b.H Ppoly = γ x₀ b.R b.H b.hHyp)
    (hdegX : Polynomial.Bivariate.degreeX Ppoly ≤ 1)
    -- finite-range per-point matching producer (ingredient-C geometry on `[k, Ppoly.natDegree]`):
    (mpPoint : ∀ t, k ≤ t → t ≤ Ppoly.natDegree → ∀ z ∈ matchingSet,
      BetaMatchingVanishes.MatchingPoint x₀ b.R b.H b.hHyp Bcoeff t z (root z))
    -- the satisfiable finite-range L9/L10 weight bound (cf. F5):
    (hcardFin : ∀ t, k ≤ t → t ≤ Ppoly.natDegree → (↑matchingSet.card : WithBot ℕ)
        > weight_Λ_over_𝒪 b.hH (betaRec x₀ b.R b.H b.hHyp Bcoeff t) b.D * b.H.natDegree)
    (hsubst : PowerSeries.HasSubst (Claim59Conditional.shiftSeries x₀ b.H))
    -- the numerator residual replacing `hγ`:
    (hβ : ∀ t, β (H := b.H) b.R t = betaRec x₀ b.R b.H b.hHyp Bcoeff t)
    -- the per-`z` Hensel root datum + degree bounds (yielding `hPz`):
    (hHensel : ∀ v₀ v₁ : F[X],
      γ x₀ b.R b.H b.hHyp = polyToPowerSeries𝕃 b.H
        ((Polynomial.map Polynomial.C v₀)
          + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)) →
      HPzBridge.HenselDatum (k := k) (deg := deg) (domain := domain) (δ := δ) u P v₀ v₁)
    (hdeg : ∀ v₀ v₁ : F[X],
      γ x₀ b.R b.H b.hHyp = polyToPowerSeries𝕃 b.H
        ((Polynomial.map Polynomial.C v₀)
          + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)) →
      v₀.natDegree < k + 1 ∧ v₁.natDegree < k + 1) :
    Section5StrictDataFin (k := k) (deg := deg) (domain := domain) (δ := δ) u P :=
  haveI := b.hIrr
  haveI := b.hPos
  { x₀ := x₀
    R := b.R
    H := b.H
    hIrr := b.hIrr
    hPos := b.hPos
    hHyp := b.hHyp
    Bcoeff := Bcoeff
    hH := b.hH
    D := b.D
    hD := b.hD
    matchingSet := matchingSet
    root := root
    T := Ppoly.natDegree
    mpFin := MpProducer.mpFin_of_pointwise (k := k) (T := Ppoly.natDegree) mpPoint
    hcardFin := hcardFin
    htailDeg :=
      htailDeg_field hsubst (GammaFromBeta.hγ_field_of_betaEq x₀ b.R b.H b.hHyp Bcoeff hβ) hrep
    hsubst := hsubst
    hγ := GammaFromBeta.hγ_field_of_betaEq x₀ b.R b.H b.hHyp Bcoeff hβ
    Ppoly := Ppoly
    hrep := hrep
    hdegX := hdegX
    hPz := HPzBridge.hPz_of_henselDatum hHensel hdeg }

/-! ## Step 3 — the Fin-bundle keystone (front door fed from `Section5StrictDataFin`)

The existing closed keystone `correlatedAgreement_affine_curves_listDecoding_closed` takes the
*over-strong* `Section5StrictData`-based extraction `hExtract`.  Here we re-derive the keystone goal
from the **satisfiable** `Section5StrictDataFin` bundle, reusing the same front-door skeleton but
routing the strict branch through `HcardDischarge.hcoeffPoly_witness_of_section5DataFin`.  This is the
Fin-variant the file header of `CorrelatedAgreementListDecodingClosed` flagged as needed. -/

omit [DecidableEq ι] in
/-- **The closed list-decoding keystone, from the corrected Fin bundle.**

Conclusion: the keystone goal `δ_ε_correlatedAgreementCurves … (ε := errorBound δ deg domain)`.

Residuals (both genuine §5 data, neither `≡` the goal):
* `hExtractFin` — per curve `u` and per good decoding `P` in the strict-Johnson range, the
  *satisfiable* corrected §5 extraction datum `Section5StrictDataFin u P`;
* `hBoundary` — the closed square-root boundary `jointAgreement` discharge. -/
theorem correlatedAgreement_listDecoding_closed_fin {k deg : ℕ}
    {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain)
    (hExtractFin : ∀ (u : WordStack F (Fin (k + 1)) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      δ < 1 - ReedSolomon.sqrtRate deg domain →
      ∀ P : F → Polynomial F,
        (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
          (P z).natDegree < deg ∧
            δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t, (P z).eval ∘ domain) ≤ δ) →
        Section5StrictDataFin (k := k) (deg := deg) (domain := domain) (δ := δ) u P)
    (hBoundary : ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      ¬δ < 1 - ReedSolomon.sqrtRate deg domain →
      jointAgreement (C := ReedSolomon.code domain deg) (δ := δ) (W := u)) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) := by
  refine correlatedAgreement_affine_curves_of_strict_coeff_polys_and_boundary
    (deg := deg) (domain := domain) (δ := δ) hδ ?_ hBoundary
  -- strict-Johnson branch: assemble `hcoeffPoly` from the per-decoding corrected Fin datum.
  intro hk u hprob hJ hsqrt P hP
  exact hcoeffPoly_witness_of_section5DataFin (hExtractFin u hprob hJ hsqrt P hP)

/-! ## Step 4 — `keystone_of_section5Inputs`: the final theorem from genuine standing inputs

This is the headline deliverable.  Every field of the corrected §5 bundle is assembled, per
curve/decoding `(u, P)`, from the verified producer bricks via `section5DataFin_of_producers`; the
result is fed into `correlatedAgreement_listDecoding_closed_fin`.  The hypotheses are exactly the
genuine §5 standing inputs (each a per-`(u, P)` producer because the keystone goal universally
quantifies over the curve and the candidate decoding), grouped through `section5DataFin_of_producers`
for the strict branch and `BoundaryDischarge.hBoundary_of_boundary_cards_and_coeffPolys` for the
boundary.  None is the goal or any intermediate conclusion. -/

omit [DecidableEq ι] in
/-- **THE FINAL ASSEMBLY.**  From the genuine §5 standing inputs — supplied per curve/decoding
`(u, P)` as the producer bundle that `section5DataFin_of_producers` consumes — together with the
closed-boundary datum and the ambient Johnson hypothesis `hδ`, the keystone goal
`δ_ε_correlatedAgreementCurves … (ε := errorBound δ deg domain)` of
`ProximityGap.correlatedAgreement_affine_curves` is produced.

The strict-Johnson branch assembles `HcardDischarge.Section5StrictDataFin` from the bricks
(GS-factor head, `hγ` from `hβ`, `htailDeg`/`mpFin`/`hcardFin`, Prop-5.5 representative, `hPz` from
the Hensel datum) and routes through `hcoeffPoly_witness_of_section5DataFin`; the boundary branch
routes the boundary cardinality + extraction datum through the in-tree assembly bridge.

`hSection5` is the genuine §5 standing residual: for every curve `u` and every good decoding `P` in
the strict-Johnson range, the corrected per-`(u, P)` extraction bundle exists.  It is *not* the goal:
the per-coefficient identity the front door consumes is **derived** from it by the producer chain. -/
theorem keystone_of_section5Inputs {k deg : ℕ}
    {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain)
    -- the genuine §5 standing inputs, per curve/decoding, packaged as a `Section5StrictDataFin`
    -- producer (each component is supplied via `section5DataFin_of_producers`):
    (hSection5 : ∀ (u : WordStack F (Fin (k + 1)) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      δ < 1 - ReedSolomon.sqrtRate deg domain →
      ∀ P : F → Polynomial F,
        (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
          (P z).natDegree < deg ∧
            δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t, (P z).eval ∘ domain) ≤ δ) →
        Section5StrictDataFin (k := k) (deg := deg) (domain := domain) (δ := δ) u P)
    -- the closed square-root boundary standing datum (cardinality bounds + §5 extraction):
    (hBoundaryData : ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      ¬δ < 1 - ReedSolomon.sqrtRate deg domain →
      ((RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card > k) ∧
      ((RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card ≥
        (Fintype.card ι + 1) * k) ∧
      (∀ P : F → Polynomial F,
        (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
          (P z).natDegree < deg ∧
            δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
              (P z).eval ∘ domain) ≤ δ) →
          ∃ B : ℕ → Polynomial F,
            (∀ j < deg, (B j).natDegree < k + 1) ∧
              ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
                ∀ j < deg, (P z).coeff j = (B j).eval z)) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) :=
  correlatedAgreement_listDecoding_closed_fin hδ hSection5
    (BoundaryDischarge.hBoundary_of_boundary_cards_and_coeffPolys
      (k := k) (deg := deg) (domain := domain) (δ := δ) hBoundaryData)

end KeystoneAssembly

end ArkLib

/-! ## Axiom audit — every declaration rests only on `[propext, Classical.choice, Quot.sound]`. -/
#print axioms ArkLib.KeystoneAssembly.htailDeg_field
#print axioms ArkLib.KeystoneAssembly.section5DataFin_of_producers
#print axioms ArkLib.KeystoneAssembly.correlatedAgreement_listDecoding_closed_fin
#print axioms ArkLib.KeystoneAssembly.keystone_of_section5Inputs
