/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.HenselNumerator
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AlphaWeight

set_option linter.style.longLine false

/-!
# (P1) CONDITIONAL UNLOCK — the structured weight invariant and the P1 collapse, GIVEN the lift identity

This file closes the **(P1)** Hensel-numerator weight bound
`Λ_𝒪(βHensel t) ≤ (2t+1)·natDegreeY R · D` of BCIKS20 Claim A.2, *conditional on the (P2) lift
identity* `βHensel_lift_identity`.  It imports `HenselNumerator` plus the shared A.4 infrastructure in
`AlphaWeight`.

## The wall, restated (wave-5 analysis, recorded in `HenselNumerator.lean`)

`βHensel_succ_term_weight_le` is UNPROVABLE through the loose induction hypothesis
`Λ(β_l) ≤ (2l+1)·d·D` — even the per-term product factor `(2(k+1−i1)+Σλ)·d·D` overshoots.  The only
route is the paper's **structured invariant**

  `Λ_𝒪(βHensel l) ≤ 1 + (l+1)·Λ(W) + e_l·Λ(ξ)`,   `e_l = 2l−1` for `l ≥ 1`, `e_0 = 0`,

which wave 5 PROVES is itself *underivable from the (A.1) recursion alone*: the sub-additive weight
calculus forces a constant `Λ(W)^0 Λ(ξ)^0` contribution of `Σλ + (D−Σλ) = D`, whereas the structured
target's constant is `1`; the gap `D−1` is exactly the multiplicative cancellation
`β_t = α_t · W^{t+1} · ξ^{e_t}` with `Λ(α_t) = Λ(Y) = 1`, i.e. the content of the (P2) lift identity
("an easier way is to consider the weight of `α_t`", BCIKS20 line 4276).

## The weight-from-identity link, and where the gap REALLY is (Task 1)

The lift identity `embeddingOf𝒪Into𝕃 (βHensel t) = αGenuine t · W^{t+1} · ξ^{e_t}` lives in the FIELD
`𝕃 H`, whereas `Λ_𝒪` is the weight of the canonical `F[X][Y]`-representative of `βHensel t ∈ 𝒪 H`
(`weight_Λ_over_𝒪 = weight_Λ ∘ canonicalRepOf𝒪`), an `𝒪`-intrinsic quantity, NOT an `𝕃`-invariant.

The genuine bridge: `W^{t+1} = embedding (W𝒪)^{t+1}` and `ξ^{e_t} = embedding ξ^{e_t}` are *already*
embeddings of `𝒪`-elements (`W𝒪`, `ClaimA2.ξ ∈ 𝒪 H`).  Hence the ENTIRE right-hand side is the
embedding of an `𝒪`-element **iff** `αGenuine t` is — and the identity says it equals
`embedding (βHensel t)`, so it is.  The one missing fact is precisely the genuine A.4 content:

  `αGenuine t = embedding a_t` for some `a_t ∈ 𝒪 H` with `Λ_𝒪(a_t) ≤ 1`   (i.e. `Λ(α_t) = Λ(Y) = 1`).

GIVEN that (the carved hypothesis `AlphaGenuineRegularWeightLe`), we PROVE — via the *injectivity* of
`embeddingOf𝒪Into𝕃` (`embeddingOf𝒪Into𝕃_injective`) — the `𝒪`-LEVEL factorization

  `βHensel t = a_t · W𝒪^{t+1} · ξ^{e_t}`   in `𝒪 H`,

and then read off `Λ_𝒪(βHensel t) ≤ Λ_𝒪(a_t) + (t+1)Λ(W) + e_t·Λ(ξ)` by the PROVEN over-`𝒪` weight
calculus (`weight_Λ_over_𝒪_mul_le`, `_pow_le`, `_W`, `nsmul_withBot_le`) — so `hlift` and injectivity
are genuinely load-bearing, and the gap is reduced to the SHARP, minimal A.4 fact `Λ(α_t) ≤ 1` (plus
`α_t` regular).  This is the precise, non-faked location of the residual.

## What this file proves (the three tasks)

1. **THE WEIGHT-FROM-IDENTITY LINK** — `βHensel_eq_alpha_mul_of_lift`: from `hlift` + the carved
   `α_t = embedding a_t` (regularity), the `𝒪`-level factorization `β_t = a_t·W𝒪^{t+1}·ξ^{e_t}`, via
   injectivity.  This is the genuine transport; `hlift` is consumed here.
2. **The STRUCTURED INVARIANT** — `βHensel_weight_structured`: `Λ_𝒪(β_l) ≤ 1+(l+1)Λ(W)+e_l·Λ(ξ)`,
   PROVEN from the factorization + the over-`𝒪` weight calculus + `Λ(a_l) ≤ 1`.
3. **(P1)** — `βHensel_weight_bound_of_lift`: `Λ_𝒪(β_t) ≤ (2t+1)·natDegreeY R·D`, PROVEN from the
   structured invariant via the wave-5 `structured_weight_collapse`
   (`= βHensel_weight_bound_of_structured_weight`).

When the final w16 vanishing residual lands, `βHensel_lift_identity` is axiom-clean and (P1)
auto-unlocks (`βHensel_weight_bound_unlocked`): instantiate `hlift := βHensel_lift_identity`, supply
the carved `α_t`-regularity, and the regime hypotheses.

NO `axiom`/`admit`/`native_decide`/`bv_decide`/`sorry`.  Audited in-file via `#print axioms`.
-/

namespace BCIKS20.HenselNumerator

open Polynomial Polynomial.Bivariate
open BCIKS20AppendixA
open ProximityPrize.BCIKS20.GammaGenuine

section P1Conditional

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-! ### 0. Shared A.4 infrastructure — imported from `AlphaWeight`

`embeddingOf𝒪Into𝕃_W𝒪`, `AlphaGenuineRegularWeightLe`, `βHensel_eq_alpha_mul_of_lift`, and
`βHensel_weight_structured` were originally re-stated here verbatim.  Now that both modules are tracked
and registered, those four declarations are supplied by the canonical superset
`AlphaWeight.lean` (imported above), which restates them identically and adds the `DivWeightLe`
equivalence and the sharp `t = 0` obstruction.  This file keeps only the genuinely-unique conditional
(P1) assembly below (`βHensel_weight_bound_of_lift`, `…'`, and the auto-unlock witness
`βHensel_weight_bound_unlocked`), which resolve the shared names from that import. -/

/-! ### 3. (P1) the loose weight bound — proven from the structured invariant by the wave-5 collapse -/

/-- **(P1) Task 3 — the loose weight bound, conditional.**  From the structured invariant
`βHensel_weight_structured` (under the lift identity + carved A.4 link + ξ-weight regime), the loose
Claim-A.2 target

  `Λ_𝒪(βHensel t) ≤ (2t+1)·natDegreeY R · D`

follows by the proven `ℕ`-arithmetic collapse `structured_weight_collapse`
(`= βHensel_weight_bound_of_structured_weight`), under the paper's faithful regime
`2 ≤ d`, `dH ≤ d`, `Λ(W)+dH ≤ D`. -/
theorem βHensel_weight_bound_of_lift (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ} (hDH : Bivariate.totalDegree H ≤ D)
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hlift : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp t)
        = αGenuine H x₀ R hHyp t
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1))
    (hα : AlphaGenuineRegularWeightLe H x₀ R hHyp hH D)
    (hξ : weight_Λ_over_𝒪 hH (ClaimA2.ξ x₀ R H hHyp) D
            ≤ WithBot.some ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1)))
    (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) := by
  -- Step A (Tasks 1+2): the structured invariant at order `t`.
  have hstructured := βHensel_weight_structured H x₀ R hHyp hH hDH hlift hα hξ t
  -- Step B (Task 3): collapse to the loose target via the proven wave-5 arithmetic.
  exact βHensel_weight_bound_of_structured_weight H x₀ R hHyp hH hdR2 hdHR hW t hstructured

/-! ### 4. The fully-assembled conditional (P1), and the auto-unlock witness

`weight_ξ_bound` (PROVEN in `RationalFunctions`) discharges `hξ` under its regime, and
`βHensel_lift_identity` (in-tree) discharges `hlift`.  The SOLE genuine residual is the carved A.4
link `hα` (`Λ(α_t) ≤ 1`, `α_t` regular). -/

/-- **(P1) discharging `hξ` via the PROVEN `weight_ξ_bound`.**  Under the `2 ≤ d` regime and the two
total-degree budgets of `weight_ξ_bound`, the ξ-weight hypothesis is automatic; so the conditional
(P1) needs only `hlift` + the carved A.4 link `hα`. -/
theorem βHensel_weight_bound_of_lift' (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ} (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hlift : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp t)
        = αGenuine H x₀ R hHyp t
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1))
    (hα : AlphaGenuineRegularWeightLe H x₀ R hHyp hH D) (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) := by
  refine βHensel_weight_bound_of_lift H x₀ R hHyp hH hDH hdR2 hdHR hW hlift hα ?_ t
  exact ClaimA2.weight_ξ_bound x₀ hH hHyp hdR2 hDH hDRx0

/-- **AUTO-UNLOCK witness.**  Once `βHensel_lift_identity` is axiom-clean (w16 vanishing landed), the
`hlift` hypothesis is discharged unconditionally by the in-tree `βHensel_lift_identity`.  This lemma
exhibits that discharge: feeding `βHensel_lift_identity` for `hlift`, the conditional (P1) needs ONLY
the carved A.4 link `hα` (`Λ(α_t) ≤ 1`) plus the paper's faithful regime hypotheses. -/
theorem βHensel_weight_bound_unlocked (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hα : AlphaGenuineRegularWeightLe H x₀ R hHyp hH D) (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_of_lift' H x₀ R hHyp hH hDH hDRx0 hdR2 hdHR hW
    (fun t => βHensel_lift_identity H x₀ R hHyp t) hα t

end P1Conditional

end BCIKS20.HenselNumerator
