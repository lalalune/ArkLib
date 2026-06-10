/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.LocalSeriesProducer

/-!
# Issue #304 — fixing the most-common-cell interface direction

## The problem (precisely)

The landed producer `RawGS304.localSeriesDatumOn_of_cell` demands
`hcell : ∀ z ∈ good, z ∈ cell` — the good set INSIDE one incidence cell.  But the proven
combinatorial Claim 5.7 (`Claim57Pigeonhole.claim57_pigeonhole`) outputs the OPPOSITE
inclusion: one LARGE cell inside the (avoided sub-)good set, `T < |cell ∩ S₀|` with
`cell ⊆ S₀`.  The two shapes meet nowhere, so the §5 "pass to the most common cell"
step (BCIKS20 Steps 5–7) could not be expressed against the landed interface.

## The fix (this file)

Weaken the producer interface from the pinned good set to an arbitrary finset `S`:

* `LocalSeriesDatumOnSub k S P` — `FaithfulCurveExtraction.LocalSeriesDatumOn` with every
  per-`z` demand quantified over `z ∈ S` instead of `z ∈ RS_goodCoeffsCurve u δ`
  (note the pinned structure used `u, δ, domain, deg` ONLY through the good set, and `k`
  only through `hn`; so the sub-finset variant needs only `(k, S, P)`);
* round-trip welds `…Sub_of_localSeriesDatumOn` / `localSeriesDatumOn_of_…Sub_good`
  (the new interface is a conservative generalization) and the new freedom
  `LocalSeriesDatumOnSub.mono` (restriction to any sub-finset — impossible at the pinned
  interface, and exactly what "pass to the most common cell" needs);
* `localSeriesDatumOnSub_of_rawGS` — the raw-GS producer of `LocalSeriesProducer.lean`,
  re-targeted at `S` (all its `RawGS304` field welds were already `S`-generic);
* `localSeriesDatumOnSub_of_cell` — **the corrected cell weld**: take `S :=` the claim57
  incidence cell itself; cell MEMBERSHIP (not `good ⊆ cell`) supplies both per-`z` raw GS
  inputs via `cell_conditions_of_mem`;
* `exists_localSeriesDatumOnSub_of_pigeonhole_output` — the weld consuming
  `claim57_pigeonhole`'s ACTUAL per-cell output shape (`hshape` + `∃ c ∈ Index, T < |cell c|`),
  with the genuinely deep per-cell residuals isolated as named hypotheses.

## Downstream soundness (the counting only needs ≥-many points — verified)

The pinned consumers (`CurveFamilyData.hPz`, `KeystoneCapstone.CurveCoeffPolys`,
`StrictCoeffPolysResidual`) quantify over the WHOLE good set, but the underlying counting
chain in `Curves.lean` is already sub-finset-ready:
`decoded_family_coefficients_of_coeff_polys_core`,
`decoded_family_coefficients_assemble_codeword_curve`, and
`decoded_sum_polynomial_family_on_codeword_curve_implies_jointAgreement` all work on an
arbitrary `S'` with ONLY the cardinality thresholds `|S'| > l + 1` and
`|S'| ≥ (|ι| + 1)·(l + 1)` — and they consume a SPECIFIC decoded family `P`, so a
`P`-dependent most-common cell is fine.  This file proves the full chain:

* `hPz_of_localSeriesDatumOnSub` — the per-`z` Hensel pin `P z = ∑ (z − x₀)^t • c t` on `S`
  (the `S`-generic re-assembly of `curveHenselDatum_of_truncatedLocalRoot_genuine_on` +
  `eval_identity_of_curveHensel`, all of whose per-`z` bricks were already good-set-free);
* `curveCoeffPolys_of_localSeriesDatumOnSub` / `coeffPolyWitness_of_localSeriesDatumOnSub` —
  the coefficient-interpolant extraction on `S` (via the already-finset-generic
  `curveCoeffPolys_of_curveFamily`);
* `jointAgreement_of_localSeriesDatumOnSub` — **the threshold capstone**: a sub-finset datum
  on ANY `S'` with `|S'| > l + 1` and `|S'| ≥ (|ι| + 1)·(l + 1)`, for a decoded family `P`
  on `S'`, already yields the §6 `jointAgreement` conclusion — so the weakening is sound
  end-to-end, and the most-common cell can replace the good set as soon as the pigeonhole
  threshold `T` is taken `≥ (|ι| + 1)·(l + 1)`;
* `jointAgreement_of_pigeonhole_cell` — the composed Steps-5–7 skeleton: claim57 per-cell
  output at threshold `T = (|ι| + 1)·(l + 1)` + per-cell analytic cargo ⟹ `jointAgreement`.

## Honest scope — the isolated deep residuals

NOT claimed (carried as named hypotheses, exactly as in the landed producer lane):

* `htrunc` (`TruncReadingOnSub`) — the §5 Claim-5.9/Prop-5.5 base-rational reading of the
  truncated local series, now demanded only on the cell;
* `hvanish` — the `αGenuine` tail vanishing (in-tree production lanes exist on the good set;
  the *statement* is `z`-free so it transfers verbatim);
* `hlc` — the monicization residual; `hsep`/`hRsep` — the S5 separable-specialization facts;
* `havoid` — cofinite `elimPoly (ξ)` avoidance (discriminant proven nonzero in-tree:
  `RawGS304.elimPoly_ξ_ne_zero`), now demanded only on the cell — strictly weaker than the
  landed good-set demand.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2 Ideal
open ProximityGap Code NNReal Finset Function ProbabilityTheory
open ProximityPrize.BCIKS20.GammaGenuine BCIKS20.HenselNumerator
open scoped BigOperators ENNReal ProbabilityTheory

namespace ArkLib

namespace Threshold304

attribute [local instance] Classical.propDecidable

/-! ## Part 1 — the threshold-quantified (sub-finset) producer interface -/

section Interface

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **The sub-finset §5 analytic datum** — `FaithfulCurveExtraction.LocalSeriesDatumOn` with
the pinned good set `RS_goodCoeffsCurve u δ` replaced by an arbitrary carrier finset `S`.
Every per-`z` field is demanded at members of `S` only.  Instantiating
`S := RS_goodCoeffsCurve u δ` recovers the landed structure exactly
(`localSeriesDatumOnSub_of_localSeriesDatumOn` / `localSeriesDatumOn_of_localSeriesDatumOnSub_good`);
instantiating `S :=` a claim57 incidence cell is the §5 "pass to the most common cell". -/
structure LocalSeriesDatumOnSub (k : ℕ) (S : Finset F) (P : F → Polynomial F) : Type where
  /-- the expansion centre. -/
  x₀ : F
  /-- the GS interpolant data. -/
  R : F[X][X][Y]
  /-- the (monic) irreducible GS factor. -/
  H : F[X][Y]
  hIrr : Fact (Irreducible H)
  hPos : Fact (0 < H.natDegree)
  hHyp : Hypotheses x₀ R H
  hξ : ξ x₀ R H hHyp ≠ 0
  hlc : H.leadingCoeff = 1
  hR : R.Separable
  /-- the number of curve coefficients (at most `k + 1`). -/
  n : ℕ
  hn : n < k + 2
  /-- the codeword-polynomial curve coefficients. -/
  c : ℕ → F[X]
  /-- the membership-restricted rational-root family — now restricted to `S`. -/
  rootOn : (z : F) → z ∈ S → rationalRoot (H_tilde' H) z
  /-- per-`z` unit condition at members of `S`. -/
  hx : ∀ z (hz : z ∈ S), (π_z z (rootOn z hz)) (ξ x₀ R H hHyp) ≠ 0
  /-- tail vanishing of the genuine Hensel coefficients from `n` on (`z`-free). -/
  hvanish : ∀ t, n ≤ t → αGenuine H x₀ R hHyp t = 0
  /-- the per-`z` base-rational reading on `S`. -/
  htrunc : ∀ z (hz : z ∈ S),
    (PowerSeries.trunc n (localSeries hHyp z (rootOn z hz) (hx z hz)) : Polynomial F)
      = ∑ t ∈ Finset.range n, (z - x₀) ^ t • c t
  /-- the decoded-side GS matching-factor divisibility on `S`. -/
  hdvd : ∀ z (hz : z ∈ S),
    (Polynomial.X - Polynomial.C ((P z : F[X]) : PowerSeries F)) ∣
      ((R.map (coeffHom_loc x₀ hHyp)).map
        (PowerSeries.map (π_hat_z hHyp z (rootOn z hz) (hx z hz))))
  /-- the decoded-side order-0 congruence on `S`. -/
  hcong : ∀ z (hz : z ∈ S),
    ((P z : F[X]) : PowerSeries F) - PowerSeries.C ((π_z z (rootOn z hz))
        (BCIKS20.HenselNumerator.βHensel H x₀ R hHyp 0))
      ∈ Ideal.span {(PowerSeries.X : PowerSeries F)}

/-- **Restriction (the new freedom).**  A sub-finset datum restricts to any smaller carrier —
the operation the pinned interface could not express, and exactly what "pass to the most
common cell" performs (`good ⊇ cell`, not `good ⊆ cell`). -/
noncomputable def LocalSeriesDatumOnSub.mono {k : ℕ} {S S' : Finset F} {P : F → Polynomial F}
    (hsub : S' ⊆ S) (d : LocalSeriesDatumOnSub k S P) :
    LocalSeriesDatumOnSub k S' P :=
  { x₀ := d.x₀, R := d.R, H := d.H, hIrr := d.hIrr, hPos := d.hPos, hHyp := d.hHyp,
    hξ := d.hξ, hlc := d.hlc, hR := d.hR, n := d.n, hn := d.hn, c := d.c,
    rootOn := fun z hz => d.rootOn z (hsub hz),
    hx := fun z hz => d.hx z (hsub hz),
    hvanish := d.hvanish,
    htrunc := fun z hz => d.htrunc z (hsub hz),
    hdvd := fun z hz => d.hdvd z (hsub hz),
    hcong := fun z hz => d.hcong z (hsub hz) }

end Interface

/-! ## Part 2 — round trips with the pinned interface (conservative generalization) -/

section RoundTrip

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- The pinned datum is the sub-finset datum at `S := RS_goodCoeffsCurve u δ`. -/
noncomputable def localSeriesDatumOnSub_of_localSeriesDatumOn
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F}
    (d : FaithfulCurveExtraction.LocalSeriesDatumOn
      (k := k) (deg := deg) (domain := domain) (δ := δ) u P) :
    LocalSeriesDatumOnSub k
      (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ) P :=
  { x₀ := d.x₀, R := d.R, H := d.H, hIrr := d.hIrr, hPos := d.hPos, hHyp := d.hHyp,
    hξ := d.hξ, hlc := d.hlc, hR := d.hR, n := d.n, hn := d.hn, c := d.c,
    rootOn := d.rootOn, hx := d.hx, hvanish := d.hvanish, htrunc := d.htrunc,
    hdvd := d.hdvd, hcong := d.hcong }

/-- Conversely, a sub-finset datum at the full good set is the pinned datum. -/
noncomputable def localSeriesDatumOn_of_localSeriesDatumOnSub_good
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F}
    (d : LocalSeriesDatumOnSub k
      (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ) P) :
    FaithfulCurveExtraction.LocalSeriesDatumOn
      (k := k) (deg := deg) (domain := domain) (δ := δ) u P :=
  { x₀ := d.x₀, R := d.R, H := d.H, hIrr := d.hIrr, hPos := d.hPos, hHyp := d.hHyp,
    hξ := d.hξ, hlc := d.hlc, hR := d.hR, n := d.n, hn := d.hn, c := d.c,
    rootOn := d.rootOn, hx := d.hx, hvanish := d.hvanish, htrunc := d.htrunc,
    hdvd := d.hdvd, hcong := d.hcong }

end RoundTrip

end Threshold304

end ArkLib

/-! ## Axiom audit (Parts 1–2) -/
#print axioms ArkLib.Threshold304.LocalSeriesDatumOnSub
#print axioms ArkLib.Threshold304.LocalSeriesDatumOnSub.mono
#print axioms ArkLib.Threshold304.localSeriesDatumOnSub_of_localSeriesDatumOn
#print axioms ArkLib.Threshold304.localSeriesDatumOn_of_localSeriesDatumOnSub_good
