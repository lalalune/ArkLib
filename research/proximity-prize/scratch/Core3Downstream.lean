/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GSMultiplicityChainCompose
import ArkLib.ToMathlib.GSFactorData
import ArkLib.ToMathlib.KeystoneAssembly

/-!
# Core 3 Downstream — the final composition: `StrictCoeffPolysResidual` from the radius + §5 machinery

This file performs the **forward composition** of the deepest open core of the proximity prize:
it drives the §5 graph-vanishing chain (the landed `Q_vanishes_on_close_codeword_graph_of_Qdeg`,
whose remaining hypotheses are `{Q_multiplicity + Q_deg + the Johnson radius}`) into the
`betaRec`-setup inputs that `BetaToCurveCoeffPolys.curveCoeffPolys_of_betaRec` consumes, and thence
into the keystone's §5 residual `ProximityGap.StrictCoeffPolysResidual`.

## The two precise links established here

### Link 1 — graph-vanishing count ⟹ the GS-factor `hcount` field (the *only* gap closed by radius)

`GSFactorData.of_section5Inputs` (proven, `ArkLib/ToMathlib/GSFactorData.lean`) produces the
`(u, P)`-independent GS-factor head of `Section5StrictData` from `h_gs : ModifiedGuruswami` plus the
documented graph side-conditions `hx0 / hsep / hS_nonempty / A / hA / hcount / hlarge`.  Of these,
the **count** field

```
hcount : ∀ z : coeffs_of_close_proximity F k ωs δ u₀ u₁,
  natWeightedDegree (eval_on_Z Q z.1) 1 k < m * (A z).card
```

is exactly the side condition my landed graph-vanishing chain discharges from the radius:
`Core3GSMultiplicity.keystone_count_of_radius` (proven) reduces it to the radius +
`hwdeg : natWeightedDegree (eval_on_Z Q z.1) 1 k ≤ proximity_gap_degree_bound k n m`, and the
landed `Core3Compose.Qdeg_eval_on_Z_le_proximity_gap_degree_bound` (proven) discharges `hwdeg` from
the solution's own `Q_deg` field.  So `hcount` is **derived from the radius**, never assumed.
`hcount_of_radius` below packages this per-`z`.

This is the single place where the radius enters the betaRec-setup: the radius supplies the GS-factor
`hcount`, hence (via `of_section5Inputs`) the curve datum `(x₀, R, H, …)` that `betaRec` is built on.

### Link 2 — `Section5StrictData`/`Fin` ⟹ `StrictCoeffPolysResidual` (the betaRec call)

`StrictCoeffPolysResidual` (`Curves.lean:2505`) asks: for every good decoding `P`, produce coefficient
polynomials `B_j` with `(P z).coeff j = (B j).eval z` on `RS_goodCoeffsCurve … u δ`.  Its hypotheses
*include* the list-decoding radius premises (the probability lower bound, the Johnson `(1-ρ)/2 < δ`,
and `δ < 1 - sqrtRate`).  Per the §5 chain:

* `CorrelatedAgreementListDecodingClosed.hcoeffPoly_witness_of_section5Data` (proven) turns a
  per-`P` `Section5StrictData u P` into exactly the `∃ B, …` conclusion of `StrictCoeffPolysResidual`
  — **via `curveCoeffPolys_of_betaRec`** (so `betaRec` is genuinely consumed);
* `HcardDischarge.hcoeffPoly_witness_of_section5DataFin` (proven) does the same from the *satisfiable*
  finite-range bundle `Section5StrictDataFin u P`.

So `StrictCoeffPolysResidual` reduces to: *a per-`P` §5 extraction datum producer*.  This file makes
that reduction explicit (`strictCoeffPolysResidual_of_section5Data` /
`strictCoeffPolysResidual_of_section5DataFin`).

## The honest residual after this composition

Everything mechanically downstream of the §5 extraction datum is **discharged** (the betaRec call,
the α-tail vanishing, the linear-representative reconstruction, the per-coefficient identity).  The
radius discharges the GS-factor `hcount`.  The single remaining genuinely-§5 datum is the **per-`P`
§5 extraction bundle** `Section5StrictDataFin u P` — concretely its `betaRec`-construction fields
(`Bcoeff`, the per-point ingredient-C matching `mpFin`, the Prop-5.5 representative `Ppoly/hrep/hdegX`,
the substitution `hsubst`, the numerator identity `hβ`, the Hensel/specialisation bridge `hPz`) — and
the §5 graph side-conditions of `of_section5Inputs` *other than* `hcount` (`hx0/hsep/hS_nonempty/
hlarge`, plus the per-`z` agreement geometry `A/hA` carried by `RadiusData`).  These are isolated as
the explicit hypotheses of `hExtract` / `RadiusData` below; none is a `sorry`/`axiom`, and none is
`≡` the goal.

`sorry`/`admit`/`axiom`/`native_decide`-free.

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon Codes*,
  §5 (list-decoding agreement chain), §6.2, Appendix A.2/A.4.
-/

set_option linter.style.longLine false

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2 ToRatFunc Ideal
open ProximityGap Code NNReal Finset Function ProbabilityTheory Trivariate RatFunc
open scoped BigOperators ENNReal ProbabilityTheory LinearCode

namespace ArkLib

namespace Core3Downstream

/-! ## Link 1 — the GS-factor `hcount` field from the Johnson radius

`GSFactorData.of_section5Inputs` consumes a per-`z` count side condition.  We produce it from the
radius datum, transporting the landed `Q_vanishes_on_close_codeword_graph_of_Qdeg` machinery
(`keystone_count_of_radius` + `Qdeg_eval_on_Z_le_proximity_gap_degree_bound`).  The radius/cardinality
bookkeeping is supplied **per matching point `z`** by a `RadiusData` family. -/

section CountFromRadius

variable {F : Type} [Field F] [DecidableEq F] [DecidableEq (RatFunc F)] [Finite F]
  [DecidableEq (Polynomial F)]
variable {n m : ℕ}

/-- **The per-`z` Johnson-radius / agreement-cardinality datum** the GS-factor `hcount` needs.

For a matching coordinate `z` in `coeffs_of_close_proximity`, this bundles the agreement set `A z`,
its decode-distance `dist z`, the geometric matching `hA z` (every `i ∈ A z` agrees with the
decoded `Pz`), the cardinality identity `(A z).card = n - dist z`, the distance bound `dist z ≤ n`,
and the genuine list-decoding premise `dist z / n < proximity_gap_johnson k n m`.  These are exactly
the inputs of the landed `Q_vanishes_on_close_codeword_graph_of_Qdeg`, minus the `(1,k)`-degree
budget which is derived from `h_gs.Q_deg`.

This is the radius datum, isolated as the smallest explicit per-`z` hypothesis — the genuine §5/
list-decoding premise, never the count itself (the count is *derived* below). -/
structure RadiusData {k : ℕ} {δ : ℚ} {u₀ u₁ : Fin n → F} {Q : F[Z][X][Y]} {ωs : Fin n ↪ F}
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁) where
  /-- the agreement set at `z`. -/
  A : Finset (Fin n)
  /-- the decode distance at `z`. -/
  dist : ℕ
  /-- the geometric matching: every `i ∈ A` agrees with the decoded `Pz`. -/
  hA : ∀ i ∈ A, (u₀ + z.1 • u₁) i = (Pz (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2).eval (ωs i)
  /-- the agreement cardinality identity. -/
  hcard : A.card = n - dist
  /-- the distance bound. -/
  hdist : dist ≤ n
  /-- the genuine Johnson-radius premise. -/
  hradius : (dist : ℝ) / n < proximity_gap_johnson k n m

/-- **Link 1 (the count field, derived from the radius).**

From the per-`z` radius data (and `k+1 ≤ n`, `1 ≤ m`), the GS-factor `hcount` side condition of
`GSFactorData.of_section5Inputs` holds: for every matching coordinate `z`,
`natWeightedDegree (eval_on_Z Q z.1) 1 k < m * (A z).card`.

The proof per `z` is `Core3GSMultiplicity.keystone_count_of_radius` fed the radius datum and the
`(1,k)`-degree budget `Qdeg_eval_on_Z_le_proximity_gap_degree_bound h_gs` (the landed transport of
`h_gs.Q_deg`).  The count is therefore a **consequence of the radius**, exactly as the landed
graph-vanishing chain establishes; it is not an independent assumption. -/
theorem hcount_of_radius {k : ℕ} {δ : ℚ} {u₀ u₁ : Fin n → F} {Q : F[Z][X][Y]} {ωs : Fin n ↪ F}
    {h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁}
    (hk : k + 1 ≤ n) (hm : 1 ≤ m)
    (rd : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁, RadiusData (F := F) h_gs z) :
    ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      Bivariate.natWeightedDegree (Trivariate.eval_on_Z Q z.1) 1 k < m * (rd z).A.card :=
  fun z =>
    Core3GSMultiplicity.keystone_count_of_radius
      (Qz := Trivariate.eval_on_Z Q z.1) (m := m) (k := k)
      (A := (rd z).A) (dist := (rd z).dist)
      hk hm (rd z).hdist (rd z).hradius
      (Core3Compose.Qdeg_eval_on_Z_le_proximity_gap_degree_bound (z := z.1) h_gs)
      (rd z).hcard

/-- **Link 1 packaged: the GS-factor `Bundle` from `h_gs`, the radius data, and the remaining graph
side-conditions.**

This is the curve datum `(x₀, R, H, Hypotheses, …)` on which `betaRec` is built, produced with the
`hcount` field discharged from the radius (via `hcount_of_radius`).  The remaining inputs
`hx0/hsep/hS_nonempty/hlarge` are the documented §5 graph side-conditions of `of_section5Inputs`
*other than* the count — they are taken as explicit hypotheses (not the count, which is now derived). -/
noncomputable def gsBundle_of_radius {k : ℕ} {δ : ℚ} (x₀ : F)
    {u₀ u₁ : Fin n → F} {Q : F[Z][X][Y]} {ωs : Fin n ↪ F}
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hk : k + 1 ≤ n) (hm : 1 ≤ m)
    (rd : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁, RadiusData (F := F) h_gs z)
    (hx0 : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        Bivariate.evalX (Polynomial.C x₀) R ≠ 0)
    (hsep : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        (Bivariate.evalX (Polynomial.C x₀) R).Separable)
    (hS_nonempty : (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁).Nonempty)
    (hlarge :
      #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q) >
        2 * D_Y Q ^ 2 * (D_X ((k + 1 : ℚ) / n) n m) * D_YZ Q) :
    GSFactorData.Bundle (F := F) x₀ :=
  GSFactorData.of_section5Inputs (F := F) (m := m) (n := n) k x₀ h_gs
    hx0 hsep hS_nonempty (fun z => (rd z).A) (fun z => (rd z).hA)
    (hcount_of_radius (F := F) (h_gs := h_gs) hk hm rd) hlarge

end CountFromRadius

/-! ## Link 2 — `StrictCoeffPolysResidual` from a per-`P` §5 extraction datum producer

The keystone's §5 residual `ProximityGap.StrictCoeffPolysResidual` is discharged by a *per-`P`* producer of
`Section5StrictData u P` (or the satisfiable `Section5StrictDataFin u P`), routed through
`hcoeffPoly_witness_of_section5Data{,Fin}` (which calls `curveCoeffPolys_of_betaRec` — so `betaRec`
is consumed).  The producer may use the radius hypotheses of `StrictCoeffPolysResidual` itself. -/

section ResidualFromData

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

open CorrelatedAgreementListDecodingClosed HcardDischarge

omit [DecidableEq ι] in
/-- **Link 2 (the betaRec call into the keystone residual), over-strong bundle.**

`StrictCoeffPolysResidual` follows from a per-`P` producer of `Section5StrictData u P`.  The producer
may consume the radius/Johnson hypotheses of `StrictCoeffPolysResidual` (`hprob`, `hJ`, `hsqrt`).
Each `∃ B, …` obligation is discharged by `hcoeffPoly_witness_of_section5Data`, i.e. by
`curveCoeffPolys_of_betaRec` — so the proof term genuinely contains `betaRec`.  Nothing here is
assumed about the per-coefficient identity; it is *derived*. -/
theorem strictCoeffPolysResidual_of_section5Data {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (hExtract : ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
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
        Section5StrictData (k := k) (deg := deg) (domain := domain) (δ := δ) u P) :
    ProximityGap.StrictCoeffPolysResidual (k := k) (deg := deg) (domain := domain) (δ := δ) := by
  intro hk u hprob hJ hsqrt P hP
  exact hcoeffPoly_witness_of_section5Data (hExtract hk u hprob hJ hsqrt P hP)

omit [DecidableEq ι] in
/-- **Link 2 (the betaRec call into the keystone residual), satisfiable finite-range bundle.**

Identical to `strictCoeffPolysResidual_of_section5Data` but from the *satisfiable* corrected bundle
`Section5StrictDataFin u P` (the F5-repaired interface: finite-range counting `mpFin/hcardFin` plus
the algebraic-degree datum `htailDeg`, instead of the over-strong infinite-range `hcard`).  The
discharge is `hcoeffPoly_witness_of_section5DataFin`, which routes the α-tail vanishing through
`tail_zero_of_finite_card_and_degree` and then re-runs the §5 `betaRec` algebra. -/
theorem strictCoeffPolysResidual_of_section5DataFin {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (hExtract : ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
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
        Section5StrictDataFin (k := k) (deg := deg) (domain := domain) (δ := δ) u P) :
    ProximityGap.StrictCoeffPolysResidual (k := k) (deg := deg) (domain := domain) (δ := δ) := by
  intro hk u hprob hJ hsqrt P hP
  exact hcoeffPoly_witness_of_section5DataFin (hExtract hk u hprob hJ hsqrt P hP)

end ResidualFromData

end Core3Downstream

end ArkLib

/-! ## Axiom audit — every declaration here must rest only on
`[propext, Classical.choice, Quot.sound]`, no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ArkLib.Core3Downstream.hcount_of_radius
#print axioms ArkLib.Core3Downstream.gsBundle_of_radius
#print axioms ArkLib.Core3Downstream.strictCoeffPolysResidual_of_section5Data
#print axioms ArkLib.Core3Downstream.strictCoeffPolysResidual_of_section5DataFin
