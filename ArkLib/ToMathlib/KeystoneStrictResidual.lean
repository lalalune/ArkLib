/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.Curves
import ArkLib.ToMathlib.BetaToCurveCoeffPolys
import ArkLib.ToMathlib.HcardDischarge

-- This file is documentation-heavy (extended BCIKS §5 prose in the docstrings); the long-line
-- style linter is disabled locally, matching the sibling `BetaToCurveCoeffPolys.lean`.
set_option linter.style.longLine false
-- The keystone wrapper carries `[DecidableEq ι]` because `correlatedAgreement_affine_curves`'s
-- *proof* (not its type) needs it; the unused-binder linter only inspects the type, so disable it.
set_option linter.unusedDecidableInType false

/-!
# Keystone front-door wiring — `StrictCoeffPolysResidual` from the genuine `betaRec` capsule

This file performs **items C/D/E** of the BCIKS20 §5 proximity-gap completion plan
(`research/proximity-prize/GRIND-LEDGER.md`): it wires the *verified* `betaRec` construction
(`ArkLib.betaRec`, the App-A.4 Hensel-lift recursion) into the **keystone front door**
`ProximityGap.correlatedAgreement_affine_curves` (`Curves.lean:2520`), so that the Johnson list-
decoding branch consumes a **real `β`** via the end-to-end capsule
`ArkLib.BetaToCurveCoeffPolys.curveCoeffPolys_of_betaRec` instead of the vacuous hypothesis plumbing
of `KeystoneCapstone.Section55Output` (which the ledger's Finding F4 flagged as `≡` the goal).

## Why this is NOT the F4 wrapper

`KeystoneCapstone.Section55Output u` is *definitionally* the front-door `hcoeffPoly` goal
(`∀ P, good P → CurveCoeffPolys u P`), and the proof of `hcoeffPoly_of_johnson_regime` never invokes
`betaRec`.  That is a re-bundling, not a reduction.

Here, by contrast, the per-coefficient datum `BetaToCurveCoeffPolys.CurveCoeffPolys k deg good P` is
**derived** by `curveCoeffPolys_of_betaRec`, whose proof term genuinely uses `betaRec`
(`tail_zero_of_betaRec_embedding_zero` → `betaRec_embedding_eq_zero_of_matchingSet_large` →
`alphaFromBeta`; the F4-avoidance proven there by a transitive proof-term dependency walk).  The
hypotheses fed to that capsule are the genuine in-tree §5 *input* data (ingredient-C per-point
matching `MatchingPoint`, the L9/L10 weight bound `hcard`, the BCIKS substitution validity `hsubst`,
the Prop-5.5 polynomial representative `hrep`/`hdegX`, the §5 specialisation bridge `hPz`, the
degree bounds `hdeg₀`/`hdeg₁`) — **none of which is `≡ CurveCoeffPolys`/`hcoeffPoly`**.

## The two genuine Lean steps proved here

1. `hcoeffPoly_witness_of_betaRecCurveCoeffPolys` — the **bundling reshuffle**
   `(∀ j, ∃ Bj, …)  ⟹  (∃ B, ∀ j, …)`: turns the capsule's per-index curve-polynomial datum into the
   single `B : ℕ → Polynomial F` shape the Curves front door consumes (`Curves.lean:2502-2505`).
   Pure Lean content (choice over the bounded index), no `sorry`.
2. `hcoeffPoly_of_betaRec` — the **front-door supply for one received curve `u` and one decoded
   family `P`**: composes the bundling with `curveCoeffPolys_of_betaRec` (β load-bearing), producing
   exactly the `∃ B …` body of `StrictCoeffPolysResidual`/`hcoeffPoly` from the §5 input bundle.

Then `strictCoeffPolysResidual_of_betaRec` packages a per-`u` supplier of that bundle into the
`StrictCoeffPolysResidual` predicate, and `correlatedAgreement_affine_curves_johnson_of_betaRec`
feeds it to the keystone `correlatedAgreement_affine_curves` (with `BoundaryCardResidual` for the
square-root boundary as the only other input).

## What stays an explicit residual (the named gap)

The Johnson branch is reduced to the **`BetaCurveInput` bundle**: a per-received-word, per-decoded-
family supply of the capsule's hypotheses.  This is the genuine BCIKS §5 / App-A.4 geometric input
(GS multiplicity datum behind `mp`/`hcard`, Prop-5.5 representative, the specialisation bridge),
isolated as one structure — never a `sorry`, and never `≡` the conclusion.  Physically reaching the
in-tree `correlatedAgreement_affine_curves` from the bundle still owes the cross-file `L13` drop-in
(replace the trivial in-tree `β_regular` with `betaRec` inside `RationalFunctions.lean`) and the
`F1` γ-recentering fix; both touch live-session-owned files and are deferred by design.

Everything proven here is kernel-clean: `#print axioms` at the bottom shows only
`[propext, Classical.choice, Quot.sound]`, no `sorry`/`admit`/`axiom`/`native_decide`.

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon Codes*,
  §5 (list-decoding agreement), Appendix A.4 (the `W`-power-numerator recursion (A.1)).
-/

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2 ToRatFunc Ideal

namespace ArkLib

namespace KeystoneStrictResidual

open ProximityGap Polynomial Code NNReal Finset Function ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory LinearCode

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-! ## Step 1 — the bundling reshuffle `(∀ j, ∃ Bj) ⟹ (∃ B, ∀ j)`

The capsule `BetaToCurveCoeffPolys.curveCoeffPolys_of_betaRec` concludes
`BetaToCurveCoeffPolys.CurveCoeffPolys k deg good P`, namely
`∀ j < deg, ∃ Bj, Bj.natDegree < k+1 ∧ ∀ z ∈ good, (P z).coeff j = Bj.eval z`
(one interpolant per coefficient index).  The Curves front door
(`StrictCoeffPolysResidual`, `Curves.lean:2502-2505`) wants a *single*
`B : ℕ → Polynomial F` with the joint degree-and-eval body.  We bundle the per-index existentials
into one function via choice — genuine (non-`sorry`) Lean content. -/

omit [Nonempty ι] [DecidableEq ι] [Fintype ι] [Fintype F] [DecidableEq F] in
/-- **Bundling reshuffle (proven, kernel-clean).**  The capsule's per-index curve-polynomial datum
`BetaToCurveCoeffPolys.CurveCoeffPolys k deg good P` yields the bundled `hcoeffPoly` existential the
Curves front door consumes: a single `B : ℕ → Polynomial F` with `(B j).natDegree < k+1` for all
`j < deg` and `(P z).coeff j = (B j).eval z` on the `good` set. -/
theorem hcoeffPoly_witness_of_betaRecCurveCoeffPolys
    {k deg : ℕ} {good : Finset F} {P : F → Polynomial F}
    (hCurve : BetaToCurveCoeffPolys.CurveCoeffPolys (F := F) k deg good P) :
    ∃ B : ℕ → Polynomial F,
      (∀ j < deg, (B j).natDegree < k + 1) ∧
        ∀ z ∈ good, ∀ j < deg, (P z).coeff j = (B j).eval z := by
  classical
  -- For each index choose an interpolant if `j < deg`, otherwise `0`.
  refine ⟨fun j => if h : j < deg then (hCurve j h).choose else 0, ?_, ?_⟩
  · intro j hj
    simp only [hj, dif_pos]
    exact (hCurve j hj).choose_spec.1
  · intro z hz j hj
    simp only [hj, dif_pos]
    exact (hCurve j hj).choose_spec.2 z hz

/-! ## Step 2 — the §5 input bundle and the per-`(u, P)` front-door supply

`BetaCurveInput` packages, for a fixed received curve `u`, the genuine §5 / App-A.4 *input* data
that the verified capsule `BetaToCurveCoeffPolys.curveCoeffPolys_of_betaRec` consumes.  It is
parameterised by the abstract setup `(x₀, R, H, hHyp, Bcoeff, D)` and, for each decoded family `P`
good on the good set, supplies the per-point matching data, the weight bound, the substitution
validity, the Prop-5.5 representative, the specialisation bridge and the curve-parameter degree
bounds.  Crucially the conclusion field is the *hypotheses* of the capsule, not its conclusion. -/

/-- The genuine BCIKS §5 / App-A.4 **input bundle** for one received curve `u`, in the shape the
verified capsule `BetaToCurveCoeffPolys.curveCoeffPolys_of_betaRec` consumes.

Each field is a genuine §5 datum (function-field setup, ingredient-C per-point matching, L9/L10
weight bound, BCIKS substitution validity, Prop-5.5 representative, specialisation bridge,
curve-parameter degree bounds).  **No field is `≡ CurveCoeffPolys`/`hcoeffPoly`** — the
per-coefficient conclusion is *derived* by the capsule, not assumed.

## ⚠ F5 finding — this structure is statement-unsatisfiable as written; prefer `BetaCurveInputFin`

The `mp`/`hcard` fields are quantified `∀ t, k ≤ t → …`, i.e. over the **infinite** tail of indices,
and the `hcard` weight budget `weight_Λ_over_𝒪 (betaRec … t) D · d_H` (collapsing to the concrete
`(2t+1)·d_R·D·d_H`, `BetaWeightCollapse.betaRec_weight_le_concrete`) **grows linearly and
unboundedly in `t`**.  The matching set `matchingSet : Finset F` is *fixed* (the §5 agreement set
`S_β`, independent of `t`).  A fixed finite cardinality cannot dominate an unbounded sequence, so
there is **no** `matchingSet` for which `hcard` holds for *all* `t ≥ k`: the `hcard` field is
unsatisfiable in principle, hence the whole structure is vacuous as stated (the same trap as the
earlier F3 `htele` and the `HcardDischarge` F5 verdict).

The honest repair is `BetaCurveInputFin` below: it replaces the infinite-range `mp`/`hcard` by the
**finite-range** `T`/`mpFin`/`hcardFin` (the counting bound is genuinely dischargeable from a fixed
large `matchingSet` only on `k ≤ t ≤ T`) plus the explicit algebraic-degree datum `htailDeg` (for
`t > T`, the Hensel coefficients vanish for the bounded-`Z`-degree reason, Prop 5.5).  See
`HcardDischarge.Section5StrictDataFin` and `BetaInputSupply.hcardFin_of_concrete` for the
satisfiable counting path.  This structure is retained only for back-compatibility and to document
the finding; the rewired front door uses the fin variant
(`hcoeffPoly_of_betaRecFin` → `strictCoeffPolysResidual_of_betaRecFin` →
`correlatedAgreement_affine_curves_johnson_of_betaRecFin`). -/
structure BetaCurveInput {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (u : WordStack F (Fin (k + 1)) ι) : Type 1 where
  /-- The base point of the BCIKS Hensel lift. -/
  x₀ : F
  /-- The trivariate polynomial `R` carrying the §5 list-decoding geometry. -/
  R : F[X][X][Y]
  /-- The irreducible defining polynomial `H` of the function field. -/
  H : F[X][Y]
  /-- `H` is irreducible (the `Fact` the function-field machinery requires). -/
  [hHirr : Fact (Irreducible H)]
  /-- `H` has positive `X`-degree (the `Fact` the machinery requires). -/
  [hHpos : Fact (0 < H.natDegree)]
  /-- The §5 hypotheses bundle (separability, base point, …) for `(x₀, R, H)`. -/
  hHyp : Hypotheses x₀ R H
  /-- The App-A.4 Hasse-derivative numerator family feeding `betaRec`. -/
  Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H
  /-- Positivity of `H.natDegree` (the weight-bound side condition). -/
  hH : 0 < H.natDegree
  /-- The total-degree bound `D`. -/
  D : ℕ
  /-- `D` dominates the total degree of `H`. -/
  hD : D ≥ Bivariate.totalDegree H
  /-- The matching set (the geometric §5 large set, after pole removal). -/
  matchingSet : Finset F
  /-- The rational-root section over the matching set. -/
  root : (z : F) → rationalRoot (H_tilde' H) z
  /-- The BCIKS substitution `X ↦ X − x₀` is valid (§5 setup; automatic for `x₀ = 0`). -/
  hsubst : PowerSeries.HasSubst (Claim59Conditional.shiftSeries x₀ H)
  /-- The in-tree `γ` is built from the genuine Hensel coefficients `αFromBeta` (the L13 bridge). -/
  hγ : γ x₀ R H hHyp =
    (PowerSeries.mk (BetaToCurveCoeffPolys.αFromBeta x₀ R H hHyp Bcoeff)).subst
      (Claim59Conditional.shiftSeries x₀ H)
  /-- The Prop-5.5 polynomial representative `Ppoly` of `γ`. -/
  Ppoly : F[X][Y]
  /-- `Ppoly` represents `γ` as a power series. -/
  hrep : polyToPowerSeries𝕃 H Ppoly = γ x₀ R H hHyp
  /-- The representative has `X`-degree `≤ 1` (Claim 5.9 linearity in `Z`). -/
  hdegX : Polynomial.Bivariate.degreeX Ppoly ≤ 1
  /-- The per-decoded-family ingredient-C per-point matching data, for every index `t ≥ k`. -/
  mp : ∀ t, k ≤ t → ∀ z ∈ matchingSet,
    BetaMatchingVanishes.MatchingPoint x₀ R H hHyp Bcoeff t z (root z)
  /-- The per-decoded-family L9/L10 weight bound `#matchingSet > Λ(betaRec t)·d`, for `t ≥ k`. -/
  hcard : ∀ t, k ≤ t → (↑matchingSet.card : WithBot ℕ)
    > weight_Λ_over_𝒪 hH (betaRec x₀ R H hHyp Bcoeff t) D * H.natDegree
  /-- The §5 specialisation bridge: the decoded family `P` equals the linear representative on the
  good set, with the curve-parameter degree bounds.  Depends on the candidate `P`. -/
  hPz : ∀ (P : F → Polynomial F) (v₀ v₁ : F[X]),
    γ x₀ R H hHyp = polyToPowerSeries𝕃 H
      ((Polynomial.map Polynomial.C v₀)
        + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)) →
    (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ, P z =
      ((Polynomial.map Polynomial.C v₀)
        + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)).eval (Polynomial.C z))
      ∧ v₀.natDegree < k + 1 ∧ v₁.natDegree < k + 1

attribute [instance] BetaCurveInput.hHirr BetaCurveInput.hHpos

omit [Nonempty ι] [DecidableEq ι] in
/-- **Step 2 — front-door supply for one received curve `u` and one decoded family `P`
(genuine, `betaRec` load-bearing).**

From the §5 input bundle `BetaCurveInput u` and a decoded family `P` good on the good set, produce
the single `B : ℕ → Polynomial F` with `(B j).natDegree < k+1` and `(P z).coeff j = (B j).eval z` on
the good set — exactly the `∃ B …` body of `StrictCoeffPolysResidual`/`hcoeffPoly`.

The proof composes the verified end-to-end capsule
`BetaToCurveCoeffPolys.curveCoeffPolys_of_betaRec` (whose proof term genuinely uses `betaRec`) with
the Step-1 bundling reshuffle.  `betaRec` is therefore load-bearing in this theorem. -/
theorem hcoeffPoly_of_betaRec
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι}
    (inp : BetaCurveInput (k := k) (deg := deg) (domain := domain) (δ := δ) u)
    (P : F → Polynomial F) :
    ∃ B : ℕ → Polynomial F,
      (∀ j < deg, (B j).natDegree < k + 1) ∧
        ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
          ∀ j < deg, (P z).coeff j = (B j).eval z := by
  -- Derive the per-index curve-polynomial datum via the capsule (β load-bearing).
  have hCurve :
      BetaToCurveCoeffPolys.CurveCoeffPolys (F := F) k deg
        (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ) P :=
    BetaToCurveCoeffPolys.curveCoeffPolys_of_betaRec
      inp.x₀ inp.R inp.H inp.hHyp inp.Bcoeff inp.hH inp.D inp.hD
      (matchingSet := inp.matchingSet) (root := inp.root)
      (inp.mp) (inp.hcard) inp.hsubst inp.hγ
      (Ppoly := inp.Ppoly) inp.hrep inp.hdegX
      (inp.hPz P)
  -- Bundle the per-index existentials into one `B` (Step 1).
  exact hcoeffPoly_witness_of_betaRecCurveCoeffPolys hCurve

/-! ## Step 2′ — the F5-corrected, satisfiable input bundle `BetaCurveInputFin`

`BetaCurveInputFin` is the honest replacement for `BetaCurveInput`: it carries the same §5 /
App-A.4 setup, but its weight-budget obligation is **finite-range** (`k ≤ t ≤ T`) plus an explicit
algebraic-degree datum for `t > T`, exactly the `HcardDischarge.Section5StrictDataFin` split.  This
makes the bundle satisfiable in principle — see the satisfiability analysis below
(`betaCurveInputFin_card_satisfiable_comment`).

The downstream capsule `BetaToCurveCoeffPolys.curveCoeffPolys_of_betaRec` only needs the **full**
α-tail vanishing `∀ t ≥ k, αFromBeta … t = 0` (a power series equals its degree-`< k` truncation
only if *all* higher coefficients vanish).  We recover that full tail from the finite-range counting
data + degree datum via `HcardDischarge.tail_zero_of_finite_card_and_degree`, then re-run the same
§5 algebra.  Concretely we route each decoded family `P` through the already-verified
`HcardDischarge.hcoeffPoly_witness_of_section5DataFin` by assembling a `Section5StrictDataFin` from
this bundle and `P`. -/

/-- The **F5-corrected** §5 / App-A.4 input bundle for one received curve `u`: identical to
`BetaCurveInput` except that the unsatisfiable infinite-range `mp`/`hcard` are replaced by

* a truncation index `T` (the largest tail index for which the fixed `matchingSet` dominates the
  weight, `T ≈ #matchingSet / (2·d_R·D·d_H)`);
* the **finite-range** ingredient-C matching `mpFin` and weight bound `hcardFin` (`k ≤ t ≤ T`), the
  genuinely dischargeable counting bound; and
* the explicit **algebraic-degree datum** `htailDeg` (for `t > T`, the Hensel coefficients vanish
  because `γ` is linear in `Z`, Prop 5.5, so its power-series numerator has finite degree).

Every other field is carried over verbatim from `BetaCurveInput`.  Because the weight budget is now
required only on the bounded range `[k, T]`, the cardinality obligation is satisfiable for a fixed
large `matchingSet` (no remaining `∀-t` blowup); see the satisfiability comment below. -/
structure BetaCurveInputFin {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (u : WordStack F (Fin (k + 1)) ι) : Type 1 where
  /-- The base point of the BCIKS Hensel lift. -/
  x₀ : F
  /-- The trivariate polynomial `R` carrying the §5 list-decoding geometry. -/
  R : F[X][X][Y]
  /-- The irreducible defining polynomial `H` of the function field. -/
  H : F[X][Y]
  /-- `H` is irreducible (the `Fact` the function-field machinery requires). -/
  [hHirr : Fact (Irreducible H)]
  /-- `H` has positive `X`-degree (the `Fact` the machinery requires). -/
  [hHpos : Fact (0 < H.natDegree)]
  /-- The §5 hypotheses bundle (separability, base point, …) for `(x₀, R, H)`. -/
  hHyp : Hypotheses x₀ R H
  /-- The App-A.4 Hasse-derivative numerator family feeding `betaRec`. -/
  Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H
  /-- Positivity of `H.natDegree` (the weight-bound side condition). -/
  hH : 0 < H.natDegree
  /-- The total-degree bound `D`. -/
  D : ℕ
  /-- `D` dominates the total degree of `H`. -/
  hD : D ≥ Bivariate.totalDegree H
  /-- The matching set (the geometric §5 large set, after pole removal). -/
  matchingSet : Finset F
  /-- The rational-root section over the matching set. -/
  root : (z : F) → rationalRoot (H_tilde' H) z
  /-- The Lemma-A.1 truncation index `T`: the largest tail index for which the fixed `matchingSet`
  dominates `weight(betaRec t)·d_H`.  Replaces the (false) uniform-in-`t` largeness of `hcard`. -/
  T : ℕ
  /-- The BCIKS substitution `X ↦ X − x₀` is valid (§5 setup; automatic for `x₀ = 0`). -/
  hsubst : PowerSeries.HasSubst (Claim59Conditional.shiftSeries x₀ H)
  /-- The in-tree `γ` is built from the genuine Hensel coefficients `αFromBeta` (the L13 bridge). -/
  hγ : γ x₀ R H hHyp =
    (PowerSeries.mk (BetaToCurveCoeffPolys.αFromBeta x₀ R H hHyp Bcoeff)).subst
      (Claim59Conditional.shiftSeries x₀ H)
  /-- The Prop-5.5 polynomial representative `Ppoly` of `γ`. -/
  Ppoly : F[X][Y]
  /-- `Ppoly` represents `γ` as a power series. -/
  hrep : polyToPowerSeries𝕃 H Ppoly = γ x₀ R H hHyp
  /-- The representative has `X`-degree `≤ 1` (Claim 5.9 linearity in `Z`). -/
  hdegX : Polynomial.Bivariate.degreeX Ppoly ≤ 1
  /-- The per-decoded-family ingredient-C per-point matching data over the **finite** counting range
  `k ≤ t ≤ T` (the satisfiable replacement for `BetaCurveInput.mp`). -/
  mpFin : ∀ t, k ≤ t → t ≤ T → ∀ z ∈ matchingSet,
    BetaMatchingVanishes.MatchingPoint x₀ R H hHyp Bcoeff t z (root z)
  /-- The per-decoded-family L9/L10 weight bound over the **finite** counting range `k ≤ t ≤ T` (the
  satisfiable replacement for `BetaCurveInput.hcard`: a fixed large `matchingSet` *can* dominate the
  weight for `t ≤ T`). -/
  hcardFin : ∀ t, k ≤ t → t ≤ T → (↑matchingSet.card : WithBot ℕ)
    > weight_Λ_over_𝒪 hH (betaRec x₀ R H hHyp Bcoeff t) D * H.natDegree
  /-- The **algebraic-degree datum**: beyond the truncation index `T`, the Hensel-lift coefficients
  vanish for the bounded-`Z`-degree reason (Prop 5.5: `γ` is linear in `Z`, hence its power-series
  numerator has finite degree).  This is the genuine §5 content that *replaces* the unsatisfiable
  unbounded-in-`t` counting obligation — isolated explicitly, never equal to the goal. -/
  htailDeg : ∀ t, T < t → BetaToCurveCoeffPolys.αFromBeta x₀ R H hHyp Bcoeff t = 0
  /-- The §5 specialisation bridge: the decoded family `P` equals the linear representative on the
  good set, with the curve-parameter degree bounds.  Depends on the candidate `P`. -/
  hPz : ∀ (P : F → Polynomial F) (v₀ v₁ : F[X]),
    γ x₀ R H hHyp = polyToPowerSeries𝕃 H
      ((Polynomial.map Polynomial.C v₀)
        + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)) →
    (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ, P z =
      ((Polynomial.map Polynomial.C v₀)
        + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)).eval (Polynomial.C z))
      ∧ v₀.natDegree < k + 1 ∧ v₁.natDegree < k + 1

attribute [instance] BetaCurveInputFin.hHirr BetaCurveInputFin.hHpos

/-! ### Satisfiability of `BetaCurveInputFin` (the audit that killed `BetaCurveInput` passes here)

The audit that ruled out `BetaCurveInput` was: its `hcard` field
`#matchingSet > weight_Λ_over_𝒪 (betaRec t) D · d_H` is required for **all** `t ≥ k`, but the
right-hand side collapses to the concrete `(2t+1)·d_R·D·d_H`
(`BetaWeightCollapse.betaRec_weight_le_concrete`), which is **strictly increasing without bound** in
`t`, while `#matchingSet` is a fixed finite number — so for `t` large enough the inequality fails and
no `matchingSet` can satisfy the field for every `t`.

For `BetaCurveInputFin` the same audit **passes**:

* `hcardFin` is required only on the **bounded** range `k ≤ t ≤ T`.  The concrete budget on that
  range attains its maximum at `t = T`, namely `(2T+1)·d_R·D·d_H`, a *finite* number.  Any
  `matchingSet` with `#matchingSet > (2T+1)·d_R·D·d_H` therefore satisfies `hcardFin` for every
  `t ∈ [k, T]` simultaneously — and such a `matchingSet` exists whenever the §5 agreement set is
  large enough (which is the genuine §5 largeness hypothesis `hlarge`).  Equivalently, given a fixed
  large `matchingSet`, one chooses `T := ⌊(#matchingSet − 1) / (2·d_R·D·d_H)⌋ − 1`, the largest
  index for which the budget still fits — there is **no remaining `∀-t` blowup**.
* `htailDeg` carries the `t > T` obligation algebraically (bounded-`Z`-degree truncation of `γ`),
  not combinatorially, so it imposes no further cardinality demand.

A lemma-level witness of the cardinality direction is `betaCurveInputFin_hcardFin_satisfiable`
below: for a `matchingSet` strictly larger than the max-over-`[k,T]` concrete budget, the finite
weight field is dischargeable index-by-index via `BetaInputSupply.hcardFin_of_concrete`'s building
block `hcard_of_concrete`. -/

omit [Nonempty ι] [DecidableEq ι] [Fintype ι] [Field F] [Fintype F] [DecidableEq F] in
/-- **Satisfiability witness for the `hcardFin` field (the audit that killed `BetaCurveInput`
passes the fin variant).**

If `#matchingSet` strictly exceeds the *maximum* concrete weight budget over the finite range
`[k, T]` — which, since `(2t+1)·d_R·D·d_H` is monotone in `t`, is just its value at `t = T`,
`(2T+1)·d_R·D·d_H` — then the finite-range weight inequality
`#matchingSet > (2t+1)·d_R·D·d_H` holds for *every* `t ∈ [k, T]` simultaneously.  This is the
finite, satisfiable counterpart of the impossible uniform-in-`t` bound `BetaCurveInput.hcard`
demanded: a single fixed finite cardinality dominates a *bounded* (hence maximal-at-`T`) family. -/
theorem betaCurveInputFin_hcardFin_satisfiable
    {dR D dH k T : ℕ} {matchingSet : Finset F}
    (hmax : ((2 * T + 1) * dR * D * dH : ℕ) < matchingSet.card) :
    ∀ t, k ≤ t → t ≤ T →
      (((2 * t + 1) * dR * D * dH : ℕ) : WithBot ℕ) < (↑matchingSet.card : WithBot ℕ) := by
  intro t _hkt htT
  -- the concrete budget is monotone in `t`; its max over `[k,T]` is at `t = T`.
  have hmono : (2 * t + 1) * dR * D * dH ≤ (2 * T + 1) * dR * D * dH := by
    have : 2 * t + 1 ≤ 2 * T + 1 := by omega
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ this))
  have hlt : (2 * t + 1) * dR * D * dH < matchingSet.card := lt_of_le_of_lt hmono hmax
  exact_mod_cast hlt

omit [Nonempty ι] [DecidableEq ι] in
/-- **Step 2′ — front-door supply from the F5-corrected bundle (genuine, `betaRec` load-bearing).**

From the satisfiable input bundle `BetaCurveInputFin u` and a decoded family `P`, produce the single
`B : ℕ → Polynomial F` with `(B j).natDegree < k+1` and `(P z).coeff j = (B j).eval z` on the good
set — exactly the `∃ B …` body of `StrictCoeffPolysResidual`/`hcoeffPoly`.

The α-tail vanishing is recovered from the *finite-range* counting data plus the algebraic-degree
datum via `HcardDischarge.tail_zero_of_finite_card_and_degree`, and the remaining §5 algebra is the
already-verified `HcardDischarge.hcoeffPoly_witness_of_section5DataFin` (which genuinely consumes
`betaRec`).  We assemble the `Section5StrictDataFin` from this bundle and `P`. -/
theorem hcoeffPoly_of_betaRecFin
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι}
    (inp : BetaCurveInputFin (k := k) (deg := deg) (domain := domain) (δ := δ) u)
    (P : F → Polynomial F) :
    ∃ B : ℕ → Polynomial F,
      (∀ j < deg, (B j).natDegree < k + 1) ∧
        ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
          ∀ j < deg, (P z).coeff j = (B j).eval z := by
  haveI := inp.hHirr
  haveI := inp.hHpos
  -- Assemble the corrected, satisfiable §5 bundle for this `P` and route it through the
  -- already-verified finite-range witness (which recovers the full α-tail internally).
  exact HcardDischarge.hcoeffPoly_witness_of_section5DataFin
    (k := k) (deg := deg) (domain := domain) (δ := δ) (u := u) (P := P)
    { x₀ := inp.x₀, R := inp.R, H := inp.H, hIrr := inp.hHirr, hPos := inp.hHpos,
      hHyp := inp.hHyp, Bcoeff := inp.Bcoeff, hH := inp.hH, D := inp.D, hD := inp.hD,
      matchingSet := inp.matchingSet, root := inp.root, T := inp.T,
      mpFin := inp.mpFin, hcardFin := inp.hcardFin, htailDeg := inp.htailDeg,
      hsubst := inp.hsubst, hγ := inp.hγ, Ppoly := inp.Ppoly, hrep := inp.hrep,
      hdegX := inp.hdegX, hPz := inp.hPz P }

/-! ## Step 3 — `StrictCoeffPolysResidual` from a per-`u` supplier of the input bundle

`StrictCoeffPolysResidual` (`Curves.lean:2489`) is the explicit Johnson-branch residual the keystone
`correlatedAgreement_affine_curves` takes.  We discharge it from a per-received-word supplier of the
§5 input bundle `BetaCurveInput`.  The probability-threshold / Johnson-radius hypotheses of
`StrictCoeffPolysResidual` are *consumed* to produce the bundle (they witness the Johnson regime
under which the §5 geometry holds), so the supplier may depend on them. -/

omit [Nonempty ι] [DecidableEq ι] in
/-- **Step 3 — `StrictCoeffPolysResidual` from the `betaRec` input bundle.**

Given, for every received curve `u` in the Johnson regime (probability threshold + radius bounds),
the §5 input bundle `BetaCurveInput u`, the Johnson-branch residual `StrictCoeffPolysResidual` holds.

This is the genuine front-door supply: the residual's `∃ B …` body is produced by `hcoeffPoly_of_
betaRec`, i.e. by the `betaRec`-driven capsule, **not** by re-assuming the conclusion. -/
theorem strictCoeffPolysResidual_of_betaRec
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (hInput : ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      δ < 1 - ReedSolomon.sqrtRate deg domain →
      BetaCurveInput (k := k) (deg := deg) (domain := domain) (δ := δ) u) :
    StrictCoeffPolysResidual (k := k) (deg := deg) (domain := domain) (δ := δ) := by
  intro hk u hprob hJ hsqrt P hP
  exact hcoeffPoly_of_betaRec (hInput hk u hprob hJ hsqrt) P

omit [Nonempty ι] [DecidableEq ι] in
/-- **Step 3′ — `StrictCoeffPolysResidual` from the F5-corrected input bundle `BetaCurveInputFin`.**

The satisfiable counterpart of `strictCoeffPolysResidual_of_betaRec`: from a per-received-word
supplier of the *finite-range* bundle `BetaCurveInputFin u`, the Johnson-branch residual
`StrictCoeffPolysResidual` holds.  The residual's `∃ B …` body is produced by `hcoeffPoly_of_
betaRecFin`, i.e. by the `betaRec`-driven capsule (with the satisfiable counting interface), **not**
by re-assuming the conclusion. -/
theorem strictCoeffPolysResidual_of_betaRecFin
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (hInput : ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      δ < 1 - ReedSolomon.sqrtRate deg domain →
      BetaCurveInputFin (k := k) (deg := deg) (domain := domain) (δ := δ) u) :
    StrictCoeffPolysResidual (k := k) (deg := deg) (domain := domain) (δ := δ) := by
  intro hk u hprob hJ hsqrt P hP
  exact hcoeffPoly_of_betaRecFin (hInput hk u hprob hJ hsqrt) P

/-! ## Step 4 — the keystone, Johnson branch driven by the real `betaRec`

Feeding `strictCoeffPolysResidual_of_betaRec` into `correlatedAgreement_affine_curves`
(`Curves.lean:2520`) yields the literal keystone goal `δ_ε_correlatedAgreementCurves`, with the
Johnson list-decoding branch supplied by the **genuine `betaRec` capsule**.  The only remaining
inputs are the closed square-root `BoundaryCardResidual` (§6.2, orthogonal to the β-construction) and
the boundary inequality `hδ`. -/

/-- **Step 4 — the keystone with the Johnson branch driven by the real `betaRec`.**

`δ_ε_correlatedAgreementCurves` (the literal `correlatedAgreement_affine_curves` goal,
`Curves.lean:2520`) follows from:

* `hInput` — the per-received-word §5 input bundle `BetaCurveInput` (drives the Johnson branch via
  the `betaRec` capsule; this is the genuine, named §5 residual, **not** the conclusion);
* `hBoundaryCard` — the closed square-root boundary residual `BoundaryCardResidual` (§6.2,
  orthogonal to the β-construction);
* `hδ` — the boundary inequality `δ ≤ 1 − √rate`.

The Johnson branch's `hcoeffPoly` is produced by `strictCoeffPolysResidual_of_betaRec`, i.e. by the
`betaRec`-driven capsule — so the keystone's list-decoding branch consumes a **real `β`**. -/
theorem correlatedAgreement_affine_curves_johnson_of_betaRec
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain)
    (hInput : ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      δ < 1 - ReedSolomon.sqrtRate deg domain →
      BetaCurveInput (k := k) (deg := deg) (domain := domain) (δ := δ) u)
    (hBoundaryCard : BoundaryCardResidual (k := k) (deg := deg) (domain := domain) (δ := δ)) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) :=
  correlatedAgreement_affine_curves (k := k) (deg := deg) (domain := domain) (δ := δ)
    (strictCoeffPolysResidual_of_betaRec hInput) hBoundaryCard hδ

omit [DecidableEq ι] in
/-- **Strict-radius keystone with the Johnson branch driven by the real `betaRec`.**

In the strict square-root range, the closed-boundary branch of the BCIKS20 keystone is impossible,
so the β-driven Johnson branch is the only residual input needed. -/
theorem correlatedAgreement_affine_curves_johnson_of_betaRec_strict
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hδ : δ < 1 - ReedSolomon.sqrtRate deg domain)
    (hInput : ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      δ < 1 - ReedSolomon.sqrtRate deg domain →
      BetaCurveInput (k := k) (deg := deg) (domain := domain) (δ := δ) u) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) :=
  correlatedAgreement_affine_curves_of_strict_coeff_polys
    (k := k) (deg := deg) (domain := domain) (δ := δ) hδ
    (fun hk u hprob hJ P hP =>
      strictCoeffPolysResidual_of_betaRec hInput hk u hprob hJ hδ P hP)

/-- **Step 4′ — the keystone with the Johnson branch driven by the F5-corrected `betaRec` bundle.**

The satisfiable counterpart of `correlatedAgreement_affine_curves_johnson_of_betaRec`:
`δ_ε_correlatedAgreementCurves` follows from the per-received-word *finite-range* §5 input bundle
`BetaCurveInputFin` (driving the Johnson branch via the `betaRec` capsule with the satisfiable
counting interface), the closed square-root `BoundaryCardResidual`, and the boundary inequality. -/
theorem correlatedAgreement_affine_curves_johnson_of_betaRecFin
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain)
    (hInput : ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      δ < 1 - ReedSolomon.sqrtRate deg domain →
      BetaCurveInputFin (k := k) (deg := deg) (domain := domain) (δ := δ) u)
    (hBoundaryCard : BoundaryCardResidual (k := k) (deg := deg) (domain := domain) (δ := δ)) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) :=
  correlatedAgreement_affine_curves (k := k) (deg := deg) (domain := domain) (δ := δ)
    (strictCoeffPolysResidual_of_betaRecFin hInput) hBoundaryCard hδ

omit [DecidableEq ι] in
/-- **Strict-radius keystone with the Johnson branch driven by the F5-corrected `betaRec` bundle.**

In the strict square-root range the closed-boundary branch is impossible, so the β-driven Johnson
branch (supplied here by the satisfiable `BetaCurveInputFin`) is the only residual input needed. -/
theorem correlatedAgreement_affine_curves_johnson_of_betaRecFin_strict
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
  correlatedAgreement_affine_curves_of_strict_coeff_polys
    (k := k) (deg := deg) (domain := domain) (δ := δ) hδ
    (fun hk u hprob hJ P hP =>
      strictCoeffPolysResidual_of_betaRecFin hInput hk u hprob hJ hδ P hP)

omit [DecidableEq ι] in
/-- **Strict-radius keystone from the corrected finite-range §5 bundle.**

This is the satisfiable replacement for the older `BetaCurveInput` front door: callers supply
`Section5StrictDataFin` for each decoded family `P`, and the existing `HcardDischarge` path derives
the coefficient-polynomial witness consumed by the BCIKS20 strict Johnson branch. -/
theorem correlatedAgreement_affine_curves_johnson_of_section5DataFin_strict
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hδ : δ < 1 - ReedSolomon.sqrtRate deg domain)
    (hInput : ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      δ < 1 - ReedSolomon.sqrtRate deg domain →
      ∀ P : F → Polynomial F,
        (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
          (P z).natDegree < deg ∧
            δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
              (P z).eval ∘ domain) ≤ δ) →
        HcardDischarge.Section5StrictDataFin
          (k := k) (deg := deg) (domain := domain) (δ := δ) u P) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) :=
  correlatedAgreement_affine_curves_of_strict_coeff_polys
    (k := k) (deg := deg) (domain := domain) (δ := δ) hδ
    (fun hk u hprob hJ P hP =>
      HcardDischarge.hcoeffPoly_witness_of_section5DataFin
        (hInput hk u hprob hJ hδ P hP))

end KeystoneStrictResidual

end ArkLib

/-! ## Axiom audit — every claimed-done declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ArkLib.KeystoneStrictResidual.hcoeffPoly_witness_of_betaRecCurveCoeffPolys
#print axioms ArkLib.KeystoneStrictResidual.hcoeffPoly_of_betaRec
#print axioms ArkLib.KeystoneStrictResidual.strictCoeffPolysResidual_of_betaRec
#print axioms ArkLib.KeystoneStrictResidual.correlatedAgreement_affine_curves_johnson_of_betaRec
#print axioms ArkLib.KeystoneStrictResidual.correlatedAgreement_affine_curves_johnson_of_betaRec_strict
#print axioms ArkLib.KeystoneStrictResidual.correlatedAgreement_affine_curves_johnson_of_section5DataFin_strict
-- The F5-corrected, satisfiable fin-variant front door:
#print axioms ArkLib.KeystoneStrictResidual.betaCurveInputFin_hcardFin_satisfiable
#print axioms ArkLib.KeystoneStrictResidual.hcoeffPoly_of_betaRecFin
#print axioms ArkLib.KeystoneStrictResidual.strictCoeffPolysResidual_of_betaRecFin
#print axioms ArkLib.KeystoneStrictResidual.correlatedAgreement_affine_curves_johnson_of_betaRecFin
#print axioms ArkLib.KeystoneStrictResidual.correlatedAgreement_affine_curves_johnson_of_betaRecFin_strict
