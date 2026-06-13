/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.RungAgreementFisher

/-!
# PROXIMITY PRIZE WORKBENCH (#371 / #389)

Closed problem statement for the δ* prize, with the EXACT in-tree status of
every route, so a candidate conjecture can be checked against what is already
settled.  **Honesty contract: this file states the open target as a named
`Prop`; it contains NO proof of the open core and NO `sorry`.  A closed proof,
when found, replaces the target below — until then it is explicitly a target.**

## The reduction chain (all proven, axiom-clean, in-tree)

`ExplainableCoreSupply dom k m B`  (DeepBandMultiplicity.lean)
  ──`deep_band_badSet_card_of_supply`──▶  deep-band bad-scalar count
  ──(MCA threshold ledger)──▶  δ* lower bracket.

## What is SETTLED — and why the obvious routes are dead

* **Deep-band supply (agreement radius `t = k+m+1`, the capacity side) is
  `Θ`-EXPONENTIAL for `μ_n`** — `not_explainableCoreSupply_exponential`
  (`DeepBandSupplyExponential.lean`): the degree-`(k+m+1)` word over the
  roots-of-unity domain forces `≥ centralBinom s ≥ 4^s/(2s)` explainable
  cores (`r = 2s`, `n = 2sd`, `s = Θ(n)`).  So NO subexponential `B` exists
  at the deep-band radius.  **The supply route to a capacity-side bound is
  closed NEGATIVELY** — any conjecture routing through `ExplainableCoreSupply`
  at radius `k+m+1` is dead (the multiplicative BKR explosion, the analog of
  Ben-Sasson–Kopparty–Radhakrishnan FOCS'06 subspace polynomials).
* **Unconditional upper bound** `subJohnsonListBound_unconditional`
  (`L = C(n,k)/C(k+m+1,k)`) — also exponential at constant rate.  So the
  deep-band list is `Θ`-exponential on BOTH brackets; this is not where a
  poly bound can live.
* **Boundary band** `= C(n,k+1)` exactly (`UniversalBoundaryBound.lean`);
  production boundary failure `ε_mca ≈ 1` (`ProductionBoundaryFailure.lean`).
* **Low-degree unconditional pin** `δ* = 1 − r/2^μ` for `r ≤ √(2^μ)`
  (`kkh26_deltaStar_pin_lowdegree`, NubsCarson audit) — an infinite family,
  but at agreement radius `≈ √(kn)` (Johnson scale), NOT the deep band.

## THE TRUE OPEN CORE (where any winning conjecture must live)

The poly-list question at **Johnson-scale agreement** `a ≈ √(k·n)` (NOT the
deep-band radius `k+m+1`), for the EXPLICIT smooth dyadic domain `μ_{2^μ}`,
in the prize window `δ ∈ (1−√ρ, 1−ρ−Θ(1/log n))` at `ε* = 2⁻¹²⁸`.  The
tension is exactly the BKR barrier: structured (subgroup-rich dyadic)
domains are precisely the ones that CAN force super-poly lists just beyond
Johnson — so a winning conjecture must use a smooth-domain feature that
DEFEATS the multiplicative-subspace explosion, not a generic counting bound
(which is provably exponential here).

`PrizeListBound dom k a L` below is the closed target: at Johnson-scale
agreement `a`, every word has at most `L` agreeing degree-`< k` codewords,
with `L` small enough (`L·q^{?} < q·ε*`-admissible) to pin δ* strictly
inside the window.  Stated as a `Prop` — proving it for explicit `μ_n` with
a window-admissible `L` is the prize.
-/

open Polynomial
open scoped NNReal ENNReal ProbabilityTheory

namespace ProximityGap.PrizeWorkbench

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
/-- **The Johnson-scale list bound (the prize target).**  Every word admits at
most `L` degree-`< k` codewords agreeing with it on `≥ a` points.  The prize
is to prove this for the explicit smooth domain with `a` at Johnson scale
`≈ √(kn)` and `L` window-admissible (subexponential / poly), STRICTLY inside
`(1−√ρ, 1−ρ−Θ(1/log n))` — i.e. genuinely beyond Johnson, defeating the
multiplicative-BKR explosion that `not_explainableCoreSupply_exponential`
proves at the deep-band radius.  NOT proven here; this is the named target. -/
def PrizeListBound (dom : Fin n ↪ F) (k a L : ℕ) (P : Finset F[X]) : Prop :=
  ∀ w : Fin n → F,
    (P.filter (fun c => c.natDegree < k ∧
      a ≤ (Finset.univ.filter (fun i => c.eval (dom i) = w i)).card)).card ≤ L

end ProximityGap.PrizeWorkbench
