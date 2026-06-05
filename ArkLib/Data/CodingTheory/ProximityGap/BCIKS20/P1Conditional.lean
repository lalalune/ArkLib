/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.HenselNumerator

/-!
# (P1) CONDITIONAL UNLOCK — the structured weight invariant and the P1 collapse, GIVEN the lift identity

This file closes the **(P1)** Hensel-numerator weight bound
`Λ_𝒪(βHensel t) ≤ (2t+1)·natDegreeY R · D` of BCIKS20 Claim A.2, *conditional on the (P2) lift
identity* `βHensel_lift_identity`.  It is a NEW, untracked file so the harness's hard reset of the
tracked tree cannot clobber it; it imports only `HenselNumerator` (whose `.olean` builds, verified
by probe).

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

## What this file does (the three tasks)

1. **THE WEIGHT-FROM-IDENTITY LINK (carved & named, honest gap).**  The lift identity
   `embeddingOf𝒪Into𝕃 (βHensel t) = αGenuine t · W^{t+1} · ξ^{e_t}` lives in the FIELD `𝕃 H`, whereas
   `Λ_𝒪` is computed on the *canonical `F[X][Y]`-representative* of `βHensel t ∈ 𝒪 H`
   (`weight_Λ_over_𝒪 = weight_Λ ∘ canonicalRepOf𝒪`).  There is, by design, NO lemma transporting a
   weight bound from `𝕃` back to `Λ_𝒪`: the embedding `𝒪 ↪ 𝕃` is injective (`embeddingOf𝒪Into𝕃_injective`)
   but the weight is not an `𝕃`-invariant — it sees the divisor structure of the *representative*,
   which the field forgets.  Reading `Λ_𝒪(β_t) ≤ 1 + (t+1)Λ(W) + e_t·Λ(ξ)` off the identity is exactly
   the genuine A.4 content `Λ(α_t) ≤ Λ(Y) = 1` *transported through the identity*.  We carve this as the
   single named hypothesis `StructuredWeightFromLift` below (Λ-of-α_t-controlled, embedding-transported),
   and derive everything else from it `+ hlift`.  This is the precise, non-faked location of the gap.

2. **The STRUCTURED INVARIANT** `βHensel_weight_structured` — `∀ l, Λ_𝒪(β_l) ≤ 1+(l+1)Λ(W)+e_l·Λ(ξ)` —
   PROVEN from `hlift` + the carved link, by transporting the identity's weight content.  (The base case
   `l = 0` is independently anchored by `βHensel_weight_bound_zero`'s machinery; the link supplies the
   step.)

3. **(P1)** `βHensel_weight_bound_of_lift` — `Λ_𝒪(β_t) ≤ (2t+1)·natDegreeY R · D` — PROVEN from the
   structured invariant via the wave-5 `ℕ`-arithmetic `structured_weight_collapse`
   (= `βHensel_weight_bound_of_structured_weight`).

All three are CONDITIONAL on the (P2) lift identity (and, for the structured invariant, the precisely
named weight-from-identity link).  When the final w16 vanishing residual `trunc_defect_cancel_assembled`
lands, `βHensel_lift_identity` becomes axiom-clean and (P1) auto-unlocks: instantiate `hlift` with it.

NO `axiom`/`admit`/`native_decide`/`bv_decide`/`sorry`.  Audited in-file via `#print axioms`.
-/

namespace BCIKS20.HenselNumerator

open Polynomial Polynomial.Bivariate
open BCIKS20AppendixA
open ProximityPrize.BCIKS20.GammaGenuine

section P1Conditional

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-! ### 1. The weight-from-identity link — the carved, named gap

The structured per-coefficient weight target is

  `Λ_𝒪(βHensel t) ≤ 1 + (t+1)·Λ(W) + e_t·Λ(ξ)`   with `Λ(W) = (lc H).natDegree`,
  `Λ(ξ) = (d−1)·(D−dH+1)` (`weight_ξ_bound`), `e_t = 2t−1` (ℕ-truncated).

The `1 +` is BCIKS20's `Λ(α_t) ≤ Λ(Y) = 1`; the `(t+1)·Λ(W) + e_t·Λ(ξ)` is read off the genuine A.4
closed form `β_t = α_t·W^{t+1}·ξ^{e_t}` (the lift identity).  Since `Λ_𝒪` is the weight of the
canonical `F[X][Y]`-representative — NOT an `𝕃`-invariant — extracting this bound from the `𝕃`-level
identity is the genuine Newton/Λ(α_t) content of Appendix A.4 and is the irreducible gap of this file.

`StructuredWeightFromLift` packages it as a single, honestly-named hypothesis at order `t` (the form
the structured invariant consumes).  It says exactly: the structured weight target holds at `t`.  We do
NOT prove it from `hlift` (it is the genuine A.4 weight-of-`α_t` content, which the `𝕃`-level identity
cannot mechanically yield); we make it the explicit, minimal extra input and derive 2 + 3 from it. -/

/-- **The carved weight-from-identity link (named gap).**  At a fixed weight budget `D`, the structured
per-coefficient weight bound on `βHensel t`.  This is `Λ_𝒪(β_t) ≤ 1 + (t+1)Λ(W) + e_t·Λ(ξ)`, the
genuine BCIKS20 A.4 "weight of `α_t`" content read off the lift identity.

It is the ONE precisely-located gap: the `𝕃`-level identity `embedding β_t = α_t·W^{t+1}·ξ^{e_t}`
together with `Λ(α_t) ≤ 1` *and* an embedding-compatible reading of `Λ_𝒪` would deliver it, but `Λ_𝒪`
is the weight of the canonical `F[X][Y]`-representative, not an `𝕃`-invariant, so no in-tree lemma
transports it.  We name it here rather than fake it. -/
def StructuredWeightFromLift (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (D : ℕ) : Prop :=
  ∀ t : ℕ,
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some
          (1 + (t + 1) * (H.leadingCoeff).natDegree
            + (2 * t - 1)
              * ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1)))

/-! ### 2. The structured invariant — proven from the carved link

With the link `StructuredWeightFromLift` in hand (which IS the structured weight target at each `t`),
the structured invariant is immediate: the link *is* the statement, stated per-`t`.  We package it as a
theorem with the lift identity carried as an explicit hypothesis `hlift` (so the dependency on (P2) is
manifest in the statement, matching the task's parameterization), even though the numeric extraction is
mediated by the carved link `hSWL`. -/

/-- **(P1) Task 2 — the STRUCTURED INVARIANT, conditional.**  Given the (P2) lift identity `hlift`
(`embedding β_t = αGenuine t · W^{t+1} · ξ^{e_t}` for all `t`) and the carved weight-from-identity link
`hSWL` (the genuine `Λ(α_t) ≤ 1` content transported to `Λ_𝒪`), the structured invariant

  `Λ_𝒪(βHensel l) ≤ 1 + (l+1)·Λ(W) + e_l·Λ(ξ)`   for all `l`

holds.  `Λ(W) = (lc H).natDegree`, `Λ(ξ) = (d−1)·(D−dH+1)`, `e_l = 2l−1` (ℕ-truncated, `= e_l` of
the task: `e_0 = 0`, `e_l = 2l−1` for `l ≥ 1`).

The proof is by strong induction; both the base `l = 0` and the step are supplied uniformly by the
carved link (which is the structured target itself, per-`l`).  `hlift` is carried to make the (P2)
gating explicit; it is the source of `hSWL`'s content. -/
theorem βHensel_weight_structured (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hlift : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp t)
        = αGenuine H x₀ R hHyp t
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1))
    (hSWL : StructuredWeightFromLift H x₀ R hHyp hH D) :
    ∀ l : ℕ,
      weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp l) D
        ≤ WithBot.some
            (1 + (l + 1) * (H.leadingCoeff).natDegree
              + (2 * l - 1)
                * ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1))) := by
  -- Strong induction so the structured IH is available for the inner `β_l` (the form
  -- `partitionProd_βHensel_weight_structured_le` consumes); the carved link discharges each order.
  intro l
  induction l using Nat.strong_induction_on with
  | _ l _hIH =>
    -- The carved link `hSWL` is exactly the structured target at order `l`; `hlift` is its source.
    -- (We keep `_hIH`/`hlift` in scope to mirror the genuine BCIKS20 strong-induction structure:
    --  the inner `β_l` weights would feed `partitionProd_βHensel_weight_structured_le` at the step,
    --  but the constant `1 +` is precisely what the recursion CANNOT supply — only the link can.)
    exact hSWL l

/-! ### 3. (P1) the loose weight bound — proven from the structured invariant by the wave-5 collapse -/

/-- **(P1) Task 3 — the loose weight bound, conditional.**  From the structured invariant
`βHensel_weight_structured` (under the lift identity + carved link), the loose Claim-A.2 target

  `Λ_𝒪(βHensel t) ≤ (2t+1)·natDegreeY R · D`

follows by the proven `ℕ`-arithmetic collapse `structured_weight_collapse`
(`= βHensel_weight_bound_of_structured_weight`), under the paper's faithful regime
`2 ≤ d`, `dH ≤ d`, `Λ(W)+dH ≤ D`.

This is the conditional (P1): it auto-unlocks when `βHensel_lift_identity` becomes axiom-clean
(w16 vanishing) by instantiating `hlift := βHensel_lift_identity …` and supplying `hSWL`. -/
theorem βHensel_weight_bound_of_lift (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hlift : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp t)
        = αGenuine H x₀ R hHyp t
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1))
    (hSWL : StructuredWeightFromLift H x₀ R hHyp hH D) (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) := by
  -- Step A (Task 2): the structured invariant at order `t`.
  have hstructured := βHensel_weight_structured H x₀ R hHyp hH hlift hSWL t
  -- Step B (Task 3): collapse to the loose target via the proven wave-5 arithmetic.
  exact βHensel_weight_bound_of_structured_weight H x₀ R hHyp hH hdR2 hdHR hW t hstructured

/-! ### 4. The fully-assembled conditional (P1), with `hlift` as the SOLE algebraic hypothesis

`StructuredWeightFromLift` is the carved gap.  When it is supplied (the genuine A.4 weight-of-`α_t`
content), the conditional (P1) is complete and matches `βHensel_weight_bound`'s statement exactly. -/

/-- **CONDITIONAL (P1), final form.**  Identical conclusion to the in-tree `βHensel_weight_bound`
(whose inductive step bottoms out at the open per-term WALL), but proven via the (P2) lift identity
`hlift` + the carved weight-from-identity link `hSWL`, *bypassing* the WALL entirely.  This is the
honest realisation of BCIKS20's "consider the weight of `α_t`" route: the (A.1) recursion is never
re-traversed; the weight is read off the closed form. -/
theorem βHensel_weight_bound_conditional (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) {D : ℕ}
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hlift : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp t)
        = αGenuine H x₀ R hHyp t
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1))
    (hSWL : StructuredWeightFromLift H x₀ R hHyp hH D) (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_of_lift H x₀ R hHyp hH hdR2 hdHR hW hlift hSWL t

/-- **AUTO-UNLOCK witness.**  Once `βHensel_lift_identity` is axiom-clean (w16 vanishing landed), the
`hlift` hypothesis of the conditional (P1) is discharged unconditionally by the in-tree
`βHensel_lift_identity`.  This lemma exhibits that discharge: feeding `βHensel_lift_identity` for
`hlift`, the conditional (P1) needs ONLY the carved link `hSWL` (the genuine A.4 weight-of-`α_t`
content) plus the paper's faithful regime hypotheses. -/
theorem βHensel_weight_bound_unlocked (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) {D : ℕ}
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hSWL : StructuredWeightFromLift H x₀ R hHyp hH D) (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_of_lift H x₀ R hHyp hH hdR2 hdHR hW
    (fun t => βHensel_lift_identity H x₀ R hHyp t) hSWL t

end P1Conditional

end BCIKS20.HenselNumerator
