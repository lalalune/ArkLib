/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2MatchMonic
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2Match
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.RestrictedFaaDiBrunoExtract

/-!
# BCIKS20 Appendix A.4 — monic Faà-di-Bruno match, TOP-DOWN / root assembly (issue #139)

This file is the **top-down companion** to `P2MatchMonic.lean`. The bottom-up file proves the
carved P2 core `RestrictedFaaDiBrunoMatch` for monic `H` term-by-term, via the per-`(i₁,λ)`
partition identity `lhs_inner_eq_rhs_term` (the genuine BCIKS20 A.4 Faà-di-Bruno bijection,
discharged by `taylorCollapse` and the `W = 1` collapse). That match is `restrictedFaaDiBrunoMatch_of_monic`.

Here we read that proven match through the *root* side of the theory — the EQUIVALENT
`FaaDiBrunoFullSumVanishes` statement (the FULL, unrestricted `countPerms` Faà-di-Bruno sum
vanishes at every positive order, i.e. the assembled `(A.1)` numerator series is a root of `Q`).
This is the "Faà-di-Bruno-of-a-root" framing requested for the alternative strategy: the proven
monic match says exactly that `coeff n (eval (βHenselAssembled) Q) = 0` for every `n ≥ 1`, which
together with the already-proven order-zero vanishing `coeff_zero_eval_βHenselAssembled` makes
`βHenselAssembled` a genuine root of `Q` — hence, by `gammaGenuine`-uniqueness, the genuine Hensel
lift, and the repaired BCIKS20 lift identity holds at every order.

NOTHING here re-proves the genuine combinatorial content: every theorem composes the already-PROVEN
monic match `restrictedFaaDiBrunoMatch_of_monic` with the already-PROVEN, hypothesis-taking P2
reductions (`restrictedMatch_iff_fullVanishes`, `assembledSeries_isRoot_of_match`,
`βHensel_lift_identity_of_match`, `P2_closed`). The point is to land the monic *root* endpoints as
named, axiom-clean theorems and to expose the per-order top-down route.

## Main results (all axiom-clean, all unconditional under `H.leadingCoeff = 1`)

* `faaDiBrunoFullSum_succ_eq_zero_of_monic` — the FULL order-`(t+1)` Faà-di-Bruno `countPerms` sum
  vanishes for monic `H` (per-order; the order-induction-friendly form).
* `faaDiBrunoFullSumVanishes_of_monic` — the all-orders full-sum vanishing for monic `H`
  (the genuine A.4 root statement, `FaaDiBrunoFullSumVanishes`).
* `coeff_succ_eval_βHenselAssembled_eq_zero_of_monic` — every positive-order coefficient of
  `eval (βHenselAssembled) Q` vanishes for monic `H` (the root coefficients, top-down).
* `assembledSeries_isRoot_of_monic` — `eval (βHenselAssembled) Q = 0` for monic `H` (the genuine
  Hensel root).
* `βHenselAssembled_eq_gammaGenuine_of_monic` — the assembled numerator series IS the genuine
  Hensel root `gammaGenuine` for monic `H`.
* `βHensel_lift_identity_of_monic` — the repaired BCIKS20 lift identity holds at every order for
  monic `H`.
* `P2_closed_of_monic` — the packaged P2 conclusion (root + all-orders lift identity) for monic `H`.
* `restrictedMatchAt_of_monic` / `coeff_succ_βHenselAssembled_eq_of_monic` — the per-order carved
  residual and the quantitative normalized-quotient coefficient equation, both unconditional for
  monic `H`, re-derived top-down from the per-order full-sum vanishing through the proven
  extraction iff `restrictedMatchAt_iff_coeff_succ_βHenselAssembled_eq`.
-/

noncomputable section

open scoped BigOperators
open Finset
open Polynomial Polynomial.Bivariate
open ArkLib.PowerSeriesComposition
open BCIKS20AppendixA
open ProximityPrize.BCIKS20.GammaGenuine

namespace BCIKS20.HenselNumerator

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-! ## The full-sum vanishing (root) side, for monic `H` -/

/-- **All-orders full Faà-di-Bruno sum vanishing for monic `H` (axiom-clean).**
Reads the bottom-up proven monic carved match `restrictedFaaDiBrunoMatch_of_monic` through the
PROVEN Newton-split equivalence `restrictedMatch_iff_fullVanishes`. This is the genuine BCIKS20 A.4
root statement: the FULL, unrestricted `countPerms` order-`(t+1)` Faà-di-Bruno sum of
`eval (βHenselAssembled) Q` vanishes at every order, i.e. the `(A.1)`-assembled numerator series is
a root of `Q` to all positive orders. -/
theorem faaDiBrunoFullSumVanishes_of_monic (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hlc : H.leadingCoeff = 1) :
    FaaDiBrunoFullSumVanishes H x₀ R hHyp :=
  (restrictedMatch_iff_fullVanishes H x₀ R hHyp).1
    (restrictedFaaDiBrunoMatch_of_monic H x₀ R hHyp hlc)

/-- **Per-order full Faà-di-Bruno sum vanishing for monic `H` (axiom-clean).**
The order-induction-friendly single-order form: at every order `t`, the FULL order-`(t+1)`
Faà-di-Bruno sum vanishes for monic `H`. This is `faaDiBrunoFullSumVanishes_of_monic` projected to
a fixed order; it is the per-order top-down statement (the analogue, on the unrestricted side, of
the proven per-order match `partitionMatchAt_monic`). -/
theorem faaDiBrunoFullSum_succ_eq_zero_of_monic (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hlc : H.leadingCoeff = 1) (t : ℕ) :
    faaDiBrunoFullSum H x₀ R hHyp (t + 1) = 0 :=
  faaDiBrunoFullSumVanishes_of_monic H x₀ R hHyp hlc t

/-- **Per-order root-coefficient vanishing for monic `H` (axiom-clean).**
Every positive-order coefficient of `eval (βHenselAssembled) Q` vanishes for monic `H`. This is
the per-order full-sum vanishing read through the PROVEN identity
`faaDiBrunoFullSum n = coeff n (eval (βHenselAssembled) Q)` (`faaDiBrunoFullSum_eq_coeff`). -/
theorem coeff_succ_eval_βHenselAssembled_eq_zero_of_monic (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hlc : H.leadingCoeff = 1) (t : ℕ) :
    PowerSeries.coeff (t + 1)
        (Polynomial.eval (βHenselAssembled H x₀ R hHyp) (Q x₀ R H)) = 0 := by
  rw [← faaDiBrunoFullSum_eq_coeff H x₀ R hHyp (t + 1)]
  exact faaDiBrunoFullSum_succ_eq_zero_of_monic H x₀ R hHyp hlc t

/-! ## The genuine Hensel root and lift identity, for monic `H` -/

/-- **The assembled series is the genuine Hensel root for monic `H` (axiom-clean).**
`eval (βHenselAssembled) Q = 0`. Composes the proven monic match with the PROVEN reduction
`assembledSeries_isRoot_of_match`. With the order-zero vanishing already discharged upstream
(`coeff_zero_eval_βHenselAssembled`), this is the whole-series root statement, top-down. -/
theorem assembledSeries_isRoot_of_monic (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hlc : H.leadingCoeff = 1) :
    Polynomial.eval (βHenselAssembled H x₀ R hHyp) (Q x₀ R H) = 0 :=
  assembledSeries_isRoot_of_match H x₀ R hHyp
    (restrictedFaaDiBrunoMatch_of_monic H x₀ R hHyp hlc)

/-- **The assembled numerator series equals the genuine Hensel lift `gammaGenuine` for monic `H`
(axiom-clean).** By `gammaGenuine`-uniqueness applied to the monic root, the `(A.1)`-assembled
power series IS `gammaGenuine`. -/
theorem βHenselAssembled_eq_gammaGenuine_of_monic (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hlc : H.leadingCoeff = 1) :
    βHenselAssembled H x₀ R hHyp = gammaGenuine x₀ R H hHyp :=
  βHenselAssembled_eq_gammaGenuine H x₀ R hHyp
    (assembledSeries_isRoot_of_monic H x₀ R hHyp hlc)

/-- **The repaired BCIKS20 A.4 lift identity at every order, for monic `H` (axiom-clean).**
`embedding (βHensel … t) = αGenuine t · W^{t+1} · ξ^{2t-1}`. Composes the proven monic match with
the PROVEN reduction `βHensel_lift_identity_of_match`. -/
theorem βHensel_lift_identity_of_monic (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hlc : H.leadingCoeff = 1) (t : ℕ) :
    embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp t)
      = αGenuine H x₀ R hHyp t
          * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1)
          * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1) :=
  βHensel_lift_identity_of_match H x₀ R hHyp
    (restrictedFaaDiBrunoMatch_of_monic H x₀ R hHyp hlc) t

/-- **P2 closed for monic `H` (axiom-clean).** The packaged P2 conclusion for monic `H`: the
assembled series is the genuine Hensel root AND the repaired lift identity holds at every order.
Top-down endpoint composing the proven monic match with the PROVEN `P2_closed` reduction. -/
theorem P2_closed_of_monic (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hlc : H.leadingCoeff = 1) :
    (Polynomial.eval (βHenselAssembled H x₀ R hHyp) (Q x₀ R H) = 0)
    ∧ (∀ t : ℕ, embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp t)
        = αGenuine H x₀ R hHyp t
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1)) :=
  P2_closed H x₀ R hHyp (restrictedFaaDiBrunoMatch_of_monic H x₀ R hHyp hlc)

/-! ## Per-order carved residual + quantitative coefficient, re-derived TOP-DOWN

These lemmas recover the per-order carved residual `RestrictedFaaDiBrunoMatchAt` and the
normalized-quotient coefficient equation `coeff (t+1) βHenselAssembled = −rFdBSum t / ζ` from the
per-order FULL-sum vanishing alone — i.e. via the genuine top-down route the prompt describes,
using the PROVEN per-order Newton split (`faaDiBrunoFullSum_succ_eq`) and the PROVEN extraction iff
(`restrictedMatchAt_iff_coeff_succ_βHenselAssembled_eq`), rather than projecting the all-orders
match. This makes the per-order top-down derivation explicit and standalone. -/

/-- **Per-order carved residual for monic `H`, derived top-down from the full-sum vanishing
(axiom-clean).** From the single-order full-sum zero `faaDiBrunoFullSum (t+1) = 0` and the PROVEN
Newton split `faaDiBrunoFullSum (t+1) = restrictedFaaDiBrunoSum t + ζ · coeff(t+1) βHenselAssembled`,
the carved residual `RestrictedFaaDiBrunoMatchAt t` (`restrictedFaaDiBrunoSum t = −ζ · coeff(t+1)
βHenselAssembled`) follows by transposition. This is the per-order top-down derivation of the
carved core, using only the proven split (no projection of the all-orders match). -/
theorem restrictedMatchAt_of_monic (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hlc : H.leadingCoeff = 1) (t : ℕ) :
    RestrictedFaaDiBrunoMatchAt H x₀ R hHyp t := by
  have hfull := faaDiBrunoFullSum_succ_eq_zero_of_monic H x₀ R hHyp hlc t
  rw [faaDiBrunoFullSum_succ_eq H x₀ R hHyp t] at hfull
  unfold RestrictedFaaDiBrunoMatchAt
  linear_combination hfull

/-- **Per-order quantitative coefficient equation for monic `H`, top-down (axiom-clean).**
The normalized-quotient coefficient equation `coeff (t+1) βHenselAssembled = −restrictedFaaDiBrunoSum
t / ζ`, recovered for monic `H` from the per-order carved residual through the PROVEN extraction iff
`restrictedMatchAt_iff_coeff_succ_βHenselAssembled_eq` (which only uses `ζ ≠ 0`). -/
theorem coeff_succ_βHenselAssembled_eq_of_monic (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hlc : H.leadingCoeff = 1) (t : ℕ) :
    PowerSeries.coeff (t + 1) (βHenselAssembled H x₀ R hHyp)
      = -restrictedFaaDiBrunoSum H x₀ R hHyp t / ClaimA2.ζ R x₀ H :=
  (restrictedMatchAt_iff_coeff_succ_βHenselAssembled_eq H x₀ R hHyp t).1
    (restrictedMatchAt_of_monic H x₀ R hHyp hlc t)

end BCIKS20.HenselNumerator

section AxiomAudit
#print axioms BCIKS20.HenselNumerator.faaDiBrunoFullSumVanishes_of_monic
#print axioms BCIKS20.HenselNumerator.faaDiBrunoFullSum_succ_eq_zero_of_monic
#print axioms BCIKS20.HenselNumerator.coeff_succ_eval_βHenselAssembled_eq_zero_of_monic
#print axioms BCIKS20.HenselNumerator.assembledSeries_isRoot_of_monic
#print axioms BCIKS20.HenselNumerator.βHenselAssembled_eq_gammaGenuine_of_monic
#print axioms BCIKS20.HenselNumerator.βHensel_lift_identity_of_monic
#print axioms BCIKS20.HenselNumerator.P2_closed_of_monic
#print axioms BCIKS20.HenselNumerator.restrictedMatchAt_of_monic
#print axioms BCIKS20.HenselNumerator.coeff_succ_βHenselAssembled_eq_of_monic
end AxiomAudit
