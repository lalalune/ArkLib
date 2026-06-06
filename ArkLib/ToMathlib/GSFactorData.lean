/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.CorrelatedAgreementListDecodingClosed
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.ListDecoding.Agreement

/-!
# Discharging the GS-factor fields of `Section5StrictData`

`Section5StrictData` (in `CorrelatedAgreementListDecodingClosed.lean`) bundles the genuine §5
per-decoding list-decoding extraction.  Its first group of fields — the **GS-factor data**

```
x₀ : F, R : F[X][X][Y], H : F[X][Y], Fact (Irreducible H), Fact (0 < H.natDegree),
Hypotheses x₀ R H, hH : 0 < H.natDegree, D : ℕ, hD : D ≥ Bivariate.totalDegree H
```

is exactly the Appendix-A.2 curve datum extracted from the Guruswami interpolant `Q`.  This file
**proves** that those fields are produced, kernel-clean and with no `sorry`, from the in-tree §5
machinery — *without re-proving anything*.  We wire the already-proven graph-condition family

* `ProximityGap.R_graph` / `ProximityGap.H_graph`            (Agreement.lean ~984-1037)
* `ProximityGap.irreducible_H_graph`                          (Agreement.lean ~1072)
* `ProximityGap.natDegree_H_graph_pos`                        (Agreement.lean ~1102)
* `ProximityGap.claimA2_hypotheses_graph`                     (Agreement.lean ~1255)

which themselves sit on top of the GS interpolant existence
(`ProximityGap.modified_guruswami_has_a_solution`, Guruswami.lean ~1123) and its irreducible
factorisation (`ProximityGap.irreducible_factorization_of_gs_solution` / `ProximityGap.pg_Rset`,
Extraction.lean ~325/709).

## What discharges each field

| field                | discharged by                                                |
| -------------------- | ------------------------------------------------------------ |
| `x₀ : F`             | the standing centre `x₀` (an input)                          |
| `R : F[X][X][Y]`     | `R_graph …` (note `F[Z][X][Y]` is *defeq* `F[X][X][Y]`)      |
| `H : F[X][Y]`        | `H_graph …` (note `F[Z][X]` is *defeq* `F[X][Y]`)            |
| `Fact (Irreducible H)` | `⟨irreducible_H_graph …⟩`                                  |
| `Fact (0 < H.natDegree)` | `⟨natDegree_H_graph_pos …⟩`                              |
| `Hypotheses x₀ R H`  | `claimA2_hypotheses_graph …`                                 |
| `hH : 0 < H.natDegree` | `natDegree_H_graph_pos …`                                  |
| `D : ℕ`              | `Bivariate.totalDegree H_graph …`                            |
| `hD : D ≥ Bivariate.totalDegree H` | `le_refl _`                                    |

## Residuals (NOT discharged here — genuine §5 gaps, isolated as hypotheses)

The GS-factor fields are *independent* of the per-decoding witness `(u, P)`.  The remaining
`Section5StrictData` fields — `Bcoeff`, `matchingSet`, `root`, `mp`, `hcard`, `hsubst`, `hγ`,
`Ppoly`, `hrep`, `hdegX`, `hPz` — are the ingredient-C matching data, the Prop-5.5 representative and
the specialisation bridge; they are *per-`(u, P)`* and are NOT addressed here.  The
`section5StrictData_of_gsFactorData_and_residuals` assembler below takes them as explicit residual
hypotheses (each `≠` the goal) and shows the GS-factor bundle slots into the full structure.

The graph side-conditions `hx0 / hsep / hS_nonempty / A / hA / hcount / hlarge` are the documented
§5 standing inputs of the graph-condition extraction (`exists_pg_factors_with_large_common_root_set_of_graph_conditions`);
they are taken as inputs, not assumed away.

`#print axioms` for the constructor is `[propext, Classical.choice, Quot.sound]`.

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon Codes*,
  §5 (list-decoding agreement chain), Appendix A.2 (Claim A.2 hypotheses).
-/

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2 ToRatFunc Ideal
open ProximityGap Code NNReal Finset Function ProbabilityTheory Trivariate
open scoped BigOperators ENNReal ProbabilityTheory LinearCode

namespace ArkLib

namespace GSFactorData

variable {F : Type} [Field F] [DecidableEq F] [Finite F]

/-! ## The GS-factor bundle

`GSFactorData x₀` packages *exactly* the GS-factor fields of `Section5StrictData` (the curve datum:
centre, curve polynomials, irreducibility/degree Facts, the Claim-A.2 `Hypotheses`, and the
total-degree bound `D`).  It is the `(u, P)`-independent head of `Section5StrictData`. -/
structure Bundle (x₀ : F) : Type where
  R : F[X][X][Y]
  H : F[X][Y]
  hIrr : Fact (Irreducible H)
  hPos : Fact (0 < H.natDegree)
  hHyp : Hypotheses x₀ R H
  hH : 0 < H.natDegree
  D : ℕ
  hD : D ≥ Bivariate.totalDegree H

/-! ## The constructor

From the §5 standing inputs — the GS interpolant assumption `ModifiedGuruswami` (which by
`modified_guruswami_has_a_solution` is satisfiable in regime) and the documented graph
side-conditions — we produce the GS-factor bundle by wiring the proven graph family.  Nothing is
re-proved: `R`/`H` are `R_graph`/`H_graph`, the Facts are the proven irreducibility/degree lemmas,
and `Hypotheses` is `claimA2_hypotheses_graph`. -/
noncomputable def of_section5Inputs
    [DecidableEq (RatFunc F)] [DecidableEq (Polynomial F)]
    {n m : ℕ} (k : ℕ) {δ : ℚ} (x₀ : F)
    {u₀ u₁ : Fin n → F} {Q : F[Z][X][Y]} {ωs : Fin n ↪ F}
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hx0 : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        Bivariate.evalX (Polynomial.C x₀) R ≠ 0)
    (hsep : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        (Bivariate.evalX (Polynomial.C x₀) R).Separable)
    (hS_nonempty : (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁).Nonempty)
    (A : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ → Finset (Fin n))
    (hA : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      ∀ i ∈ A z, (u₀ + z.1 • u₁) i =
        (Pz (n := n) (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2).eval (ωs i))
    (hcount : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      Bivariate.natWeightedDegree (Trivariate.eval_on_Z Q z.1) 1 k < m * (A z).card)
    (hlarge :
      #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q) >
        2 * D_Y Q ^ 2 * (D_X ((k + 1 : ℚ) / n) n m) * D_YZ Q) :
    Bundle (F := F) x₀ where
  R := R_graph (F := F) (m := m) (n := n) k δ x₀ h_gs hx0 hsep hS_nonempty A hA hcount hlarge
  H := H_graph (F := F) (m := m) (n := n) k δ x₀ h_gs hx0 hsep hS_nonempty A hA hcount hlarge
  hIrr := ⟨irreducible_H_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
            hx0 hsep hS_nonempty A hA hcount hlarge⟩
  hPos := ⟨natDegree_H_graph_pos (F := F) (m := m) (n := n) k δ x₀ h_gs
            hx0 hsep hS_nonempty A hA hcount hlarge⟩
  hHyp := claimA2_hypotheses_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
            hx0 hsep hS_nonempty A hA hcount hlarge
  hH := natDegree_H_graph_pos (F := F) (m := m) (n := n) k δ x₀ h_gs
            hx0 hsep hS_nonempty A hA hcount hlarge
  D := Bivariate.totalDegree
        (H_graph (F := F) (m := m) (n := n) k δ x₀ h_gs hx0 hsep hS_nonempty A hA hcount hlarge)
  hD := le_refl _

/-! ## Slotting the bundle into the full `Section5StrictData`

The GS-factor bundle is the `(u, P)`-independent head of `Section5StrictData`.  Given the per-`(u, P)`
residual fields (ingredient-C matching, Prop-5.5 representative, specialisation bridge), the full
structure is assembled with the bundle's GS-factor fields supplied verbatim.  This is the explicit
record that the bundle discharges *exactly* the GS-factor fields and nothing else. -/
variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι] [Fintype F]

/-- Assemble a `Section5StrictData` from a GS-factor `Bundle` plus the residual (per-`(u, P)`) §5
fields.  The GS-factor fields (`x₀`, `R`, `H`, the two `Fact`s, `Hypotheses`, `hH`, `D`, `hD`) come
straight from the bundle `b`; everything else is an explicit residual argument. -/
def toSection5StrictData
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F}
    {x₀ : F} (b : Bundle (F := F) x₀)
    [_inst_hIrr : Fact (Irreducible b.H)] [_inst_hPos : Fact (0 < b.H.natDegree)]
    (Bcoeff : (i₁ : ℕ) → {mm : ℕ} → Nat.Partition mm → 𝒪 b.H)
    (matchingSet : Finset F)
    (root : (z : F) → rationalRoot (H_tilde' b.H) z)
    (mp : ∀ t, k ≤ t → ∀ z ∈ matchingSet,
      BetaMatchingVanishes.MatchingPoint x₀ b.R b.H b.hHyp Bcoeff t z (root z))
    (hcard : ∀ t, k ≤ t → (↑matchingSet.card : WithBot ℕ)
        > weight_Λ_over_𝒪 b.hH (betaRec x₀ b.R b.H b.hHyp Bcoeff t) b.D * b.H.natDegree)
    (hsubst : PowerSeries.HasSubst (Claim59Conditional.shiftSeries x₀ b.H))
    (hγ : γ x₀ b.R b.H b.hHyp =
      (PowerSeries.mk (BetaToCurveCoeffPolys.αFromBeta x₀ b.R b.H b.hHyp Bcoeff)).subst
        (Claim59Conditional.shiftSeries x₀ b.H))
    (Ppoly : F[X][Y])
    (hrep : polyToPowerSeries𝕃 b.H Ppoly = γ x₀ b.R b.H b.hHyp)
    (hdegX : Polynomial.Bivariate.degreeX Ppoly ≤ 1)
    (hPz : ∀ v₀ v₁ : F[X],
      γ x₀ b.R b.H b.hHyp = polyToPowerSeries𝕃 b.H
        ((Polynomial.map Polynomial.C v₀)
          + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)) →
      (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ, P z =
        ((Polynomial.map Polynomial.C v₀)
            + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)).eval (Polynomial.C z))
        ∧ v₀.natDegree < k + 1 ∧ v₁.natDegree < k + 1) :
    CorrelatedAgreementListDecodingClosed.Section5StrictData
      (k := k) (deg := deg) (domain := domain) (δ := δ) u P where
  x₀ := x₀
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
  mp := mp
  hcard := hcard
  hsubst := hsubst
  hγ := hγ
  Ppoly := Ppoly
  hrep := hrep
  hdegX := hdegX
  hPz := hPz

end GSFactorData

end ArkLib
