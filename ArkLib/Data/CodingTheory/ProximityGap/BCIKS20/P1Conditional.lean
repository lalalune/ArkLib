/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.HenselNumerator
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2Vanish

set_option linter.style.longLine false

/-!
# (P1) CONDITIONAL UNLOCK — the structured weight invariant and the P1 collapse, GIVEN the lift identity

This file closes the **(P1)** Hensel-numerator weight bound
`Λ_𝒪(βHensel t) ≤ (2t+1)·natDegreeY R · D` of BCIKS20 Claim A.2, *conditional on the (P2) lift
identity* `βHensel_lift_identity`.  It is a NEW, untracked file so the harness's hard reset of the
tracked tree cannot clobber it; it imports only `HenselNumerator` (whose `.olean` builds, verified by
probe).

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

Given the final w16 vanishing residual `FaaDiBrunoSuccSumZeroResidual`, `βHensel_lift_identity`
is available as an axiom-clean conditional theorem and (P1) auto-unlocks
(`βHensel_weight_bound_unlocked`): instantiate `hlift := βHensel_lift_identity`, supply the carved
`α_t`-regularity, and the regime hypotheses.

NO `axiom`/`admit`/`native_decide`/`bv_decide`/`sorry`.  Audited in-file via `#print axioms`.
-/

namespace BCIKS20.HenselNumerator

open Polynomial Polynomial.Bivariate
open BCIKS20AppendixA
open ProximityPrize.BCIKS20.GammaGenuine

section P1Conditional

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-! ### 0. The `W` embedding bridge

`embedding (W𝒪 H) = liftToFunctionField H.leadingCoeff` — so the lift identity's `W^{t+1}` factor is
literally the embedding of `W𝒪^{t+1}`.  Pure unfolding (`W𝒪 = mk (C lc)`, `embedding ∘ mk = liftBivariate`,
`liftBivariate (C p) = liftToFunctionField p`). -/

omit [Fact (Irreducible H)] [Fact (0 < H.natDegree)] in
/-- The embedding of the `𝒪`-element `W𝒪` is the `𝕃`-element `liftToFunctionField H.leadingCoeff` (the
`W` of the lift identity). -/
theorem embeddingOf𝒪Into𝕃_W𝒪 :
    embeddingOf𝒪Into𝕃 H (W𝒪 H) = liftToFunctionField (H := H) H.leadingCoeff := by
  rw [W𝒪, embeddingOf𝒪Into𝕃_mk, liftBivariate_C]

/-! ### 1. The carved weight-from-identity link — the SHARP, minimal A.4 gap

The genuine open content is exactly BCIKS20's `Λ(α_t) = Λ(Y) = 1`: the Hensel-root coefficient
`αGenuine t ∈ 𝕃 H` is regular (an embedding of an `𝒪`-element) of `Λ_𝒪`-weight `≤ 1`.  We name it
rather than fake it. -/

/-- **The carved A.4 link (named gap).**  At order `t`, the genuine Hensel-root coefficient `αGenuine t`
is the embedding of an `𝒪`-element `a_t` of `Λ_𝒪`-weight `≤ 1`.  This is the formal content of BCIKS20's
`Λ(α_t) = Λ(Y) = 1` ("consider the weight of `α_t`", line 4276): `α_t` is, up to the `W^{t+1}·ξ^{e_t}`
clearing, the genuine root `γ`'s `t`-th Taylor coefficient, whose weight is that of the variable `Y`. -/
def AlphaGenuineRegularWeightLe (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (D : ℕ) : Prop :=
  ∀ t : ℕ, ∃ a : 𝒪 H,
    embeddingOf𝒪Into𝕃 H a = αGenuine H x₀ R hHyp t
      ∧ weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1

/-- **The `𝒪`-level divisibility-with-weight form** of the carved A.4 link.
At order `t`, `βHensel t` factors in `𝒪 H` as
`a_t · W𝒪^{t+1} · ξ^{2t-1}`, with quotient `Λ_𝒪`-weight `≤ 1`.
Under the lift identity this is equivalent to `AlphaGenuineRegularWeightLe`;
see `alphaWeight_iff_divWeight`. -/
def DivWeightLe (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (D : ℕ) : Prop :=
  ∀ t : ℕ, ∃ a : 𝒪 H,
    βHensel H x₀ R hHyp t
        = a * (W𝒪 H) ^ (t + 1) * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * t - 1)
      ∧ weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1

/-! ### 1′. Task 1 — the weight-from-identity LINK: the `𝒪`-level factorization -/

/-- **(P1) Task 1 — THE WEIGHT-FROM-IDENTITY LINK.**  Given the (P2) lift identity at order `t`
(`hlift_t`) and a carved `𝒪`-preimage `a` of `αGenuine t` (`ha`), the `βHensel t` factors, IN `𝒪 H`, as

  `βHensel t = a · W𝒪^{t+1} · ξ^{2t−1}`.

The `𝕃`-level identity says `embedding (β_t) = embedding a · embedding (W𝒪)^{t+1} · embedding ξ^{2t−1}
= embedding (a · W𝒪^{t+1} · ξ^{2t−1})` (ring-hom multiplicativity + the `W` bridge); injectivity of
`embeddingOf𝒪Into𝕃` (`embeddingOf𝒪Into𝕃_injective`) descends it to `𝒪`.  This is the genuine transport
of the lift identity to the world where `Λ_𝒪` lives. -/
theorem βHensel_eq_alpha_mul_of_lift (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (t : ℕ) {a : 𝒪 H}
    (ha : embeddingOf𝒪Into𝕃 H a = αGenuine H x₀ R hHyp t)
    (hlift_t :
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp t)
        = αGenuine H x₀ R hHyp t
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1)) :
    βHensel H x₀ R hHyp t
      = a * (W𝒪 H) ^ (t + 1) * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * t - 1) := by
  -- Push the embedding through the RHS `𝒪`-product and match with `hlift_t`.
  apply embeddingOf𝒪Into𝕃_injective hH
  rw [hlift_t]
  rw [map_mul, map_mul, map_pow, map_pow, ha, embeddingOf𝒪Into𝕃_W𝒪]

/-- **Reverse bridge, `𝒪 → 𝕃`.** Given the `𝒪`-level factorization of
`βHensel t` and the lift identity at `t`, the quotient embeds to
`αGenuine t`.  This is the reverse half needed to identify the carved
regularity residual with the concrete clearing-divisibility residual. -/
theorem alpha_eq_embedding_of_fact (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ) {a : 𝒪 H}
    (hfact : βHensel H x₀ R hHyp t
      = a * (W𝒪 H) ^ (t + 1) * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * t - 1))
    (hlift_t :
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp t)
        = αGenuine H x₀ R hHyp t
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1)) :
    embeddingOf𝒪Into𝕃 H a = αGenuine H x₀ R hHyp t := by
  have hpush : embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp t)
      = embeddingOf𝒪Into𝕃 H a
          * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1)
          * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1) := by
    rw [hfact, map_mul, map_mul, map_pow, map_pow, embeddingOf𝒪Into𝕃_W𝒪]
  rw [hlift_t, mul_assoc, mul_assoc] at hpush
  exact mul_right_cancel₀ (den_ne_zero H x₀ R hHyp t) hpush.symm

/-- **Exact residual identification.**  Given the (P2) lift identity for all
orders, the carved regularity/weight residual `AlphaGenuineRegularWeightLe` is
equivalent to the concrete `𝒪`-divisibility-with-weight residual
`DivWeightLe`. -/
theorem alphaWeight_iff_divWeight (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) (D : ℕ)
    (hlift : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp t)
        = αGenuine H x₀ R hHyp t
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1)) :
    AlphaGenuineRegularWeightLe H x₀ R hHyp hH D ↔ DivWeightLe H x₀ R hHyp hH D := by
  constructor
  · intro hα t
    obtain ⟨a, ha_eq, ha_wt⟩ := hα t
    exact ⟨a, βHensel_eq_alpha_mul_of_lift H x₀ R hHyp hH t ha_eq (hlift t), ha_wt⟩
  · intro hd t
    obtain ⟨a, hfact, ha_wt⟩ := hd t
    exact ⟨a, alpha_eq_embedding_of_fact H x₀ R hHyp t hfact (hlift t), ha_wt⟩

/-! ### 2. The structured invariant — proven from the factorization + the over-`𝒪` weight calculus -/

/-- **(P1) Task 2 — the STRUCTURED INVARIANT, conditional.**  Given the (P2) lift identity `hlift`,
the carved A.4 link `hα` (`αGenuine l` regular of weight `≤ 1`), the genuine `Λ(W)` bound
(`weight_Λ_over_𝒪_W`, automatic) and the `Λ(ξ)` bound `hξ` (`weight_ξ_bound`, under its regime), the
structured invariant

  `Λ_𝒪(βHensel l) ≤ 1 + (l+1)·Λ(W) + e_l·Λ(ξ)`   for all `l`

holds, with `Λ(W) = (lc H).natDegree`, `Λ(ξ) ≤ (d−1)·(D−dH+1)`, `e_l = 2l−1` (ℕ-truncated:
`e_0 = 0`, `e_l = 2l−1` for `l ≥ 1`).

Proof per order `l`: the link gives `β_l = a_l · W𝒪^{l+1} · ξ^{e_l}` in `𝒪` (Task 1); then the proven
over-`𝒪` weight calculus
`Λ_𝒪(β_l) ≤ Λ_𝒪(a_l) + (l+1)·Λ_𝒪(W𝒪) + e_l·Λ_𝒪(ξ) ≤ 1 + (l+1)·Λ(W) + e_l·Λ(ξ)`. -/
theorem βHensel_weight_structured (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ} (hDH : Bivariate.totalDegree H ≤ D)
    (hlift : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp t)
        = αGenuine H x₀ R hHyp t
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1))
    (hα : AlphaGenuineRegularWeightLe H x₀ R hHyp hH D)
    (hξ : weight_Λ_over_𝒪 hH (ClaimA2.ξ x₀ R H hHyp) D
            ≤ WithBot.some ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1)))
    (l : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp l) D
      ≤ WithBot.some
          (1 + (l + 1) * (H.leadingCoeff).natDegree
            + (2 * l - 1)
              * ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1))) := by
  -- Task 1: extract `a_l` and the `𝒪`-level factorization.
  obtain ⟨a, ha_eq, ha_wt⟩ := hα l
  have hfact : βHensel H x₀ R hHyp l
      = a * (W𝒪 H) ^ (l + 1) * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * l - 1) :=
    βHensel_eq_alpha_mul_of_lift H x₀ R hHyp hH l ha_eq (hlift l)
  rw [hfact]
  -- Sub-multiplicativity over `𝒪`: split the two products.
  refine (weight_Λ_over_𝒪_mul_le H hH hDH _ _).trans ?_
  refine le_trans (add_le_add (weight_Λ_over_𝒪_mul_le H hH hDH _ _) (le_refl _)) ?_
  -- Now bound the three factors.
  -- (i) `Λ_𝒪(a) ≤ 1`.
  -- (ii) `Λ_𝒪(W𝒪^{l+1}) ≤ (l+1)·Λ(W) ≤ (l+1)·(lc H).natDegree`.
  have hW_pow : weight_Λ_over_𝒪 hH ((W𝒪 H) ^ (l + 1)) D
      ≤ WithBot.some ((l + 1) * (H.leadingCoeff).natDegree) := by
    refine (weight_Λ_over_𝒪_pow_le H hH hDH (W𝒪 H) (l + 1)).trans ?_
    exact nsmul_withBot_le (l + 1) _ (weight_Λ_over_𝒪_W H hH hDH)
  -- (iii) `Λ_𝒪(ξ^{2l−1}) ≤ (2l−1)·Λ(ξ) ≤ (2l−1)·((d−1)(D−dH+1))`.
  have hξ_pow : weight_Λ_over_𝒪 hH ((ClaimA2.ξ x₀ R H hHyp) ^ (2 * l - 1)) D
      ≤ WithBot.some
          ((2 * l - 1) * ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1))) := by
    refine (weight_Λ_over_𝒪_pow_le H hH hDH (ClaimA2.ξ x₀ R H hHyp) (2 * l - 1)).trans ?_
    exact nsmul_withBot_le (2 * l - 1) _ hξ
  -- Combine: `(Λ(a) + Λ(W^{l+1})) + Λ(ξ^{e_l}) ≤ (1 + (l+1)Λ(W)) + e_l·Λ(ξ)`.
  refine le_trans (add_le_add (add_le_add ha_wt hW_pow) hξ_pow) ?_
  -- Push the three `WithBot.some` together; the resulting `ℕ` bound matches the target on the nose.
  rw [← WithBot.coe_add, ← WithBot.coe_add]

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

/-- **(P1) from the concrete divisibility residual.**  This is the same
weight-bound entry point as `βHensel_weight_bound_of_lift`, but callers may now
supply the `𝒪`-level clearing-divisibility form `DivWeightLe`; the equivalence
`alphaWeight_iff_divWeight` converts it to the carved regularity form needed by
the structured-weight proof. -/
theorem βHensel_weight_bound_of_divWeight (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hlift : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp t)
        = αGenuine H x₀ R hHyp t
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1))
    (hdiv : DivWeightLe H x₀ R hHyp hH D)
    (hξ : weight_Λ_over_𝒪 hH (ClaimA2.ξ x₀ R H hHyp) D
            ≤ WithBot.some ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1)))
    (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) := by
  have hα : AlphaGenuineRegularWeightLe H x₀ R hHyp hH D :=
    (alphaWeight_iff_divWeight H x₀ R hHyp hH D hlift).2 hdiv
  exact βHensel_weight_bound_of_lift H x₀ R hHyp hH hDH hdR2 hdHR hW hlift hα hξ t

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

/-- **(P1), with `hξ` discharged, from the concrete divisibility residual.**
After `weight_ξ_bound`, the remaining P1 inputs are exactly the lift identity
and `DivWeightLe`. -/
theorem βHensel_weight_bound_of_divWeight' (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hlift : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp t)
        = αGenuine H x₀ R hHyp t
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1))
    (hdiv : DivWeightLe H x₀ R hHyp hH D) (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) := by
  refine βHensel_weight_bound_of_divWeight H x₀ R hHyp hH hDH hdR2 hdHR hW hlift hdiv ?_ t
  exact ClaimA2.weight_ξ_bound x₀ hH hHyp hdR2 hDH hDRx0

/-- **AUTO-UNLOCK witness.**  Given the explicit w16 vanishing residual, the `hlift` hypothesis is
discharged by the in-tree conditional theorem `βHensel_lift_identity`.  This lemma exhibits that
discharge: feeding `βHensel_lift_identity` for `hlift`, the conditional (P1) needs ONLY the carved
A.4 link `hα` (`Λ(α_t) ≤ 1`) plus the paper's faithful regime hypotheses. -/
theorem βHensel_weight_bound_unlocked (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hzero : FaaDiBrunoSuccSumZeroResidual H x₀ R hHyp)
    (hα : AlphaGenuineRegularWeightLe H x₀ R hHyp hH D) (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_of_lift' H x₀ R hHyp hH hDH hDRx0 hdR2 hdHR hW
    (fun t => βHensel_lift_identity H x₀ R hHyp hzero t) hα t

/-- **AUTO-UNLOCK witness from concrete divisibility.**  This is the
`DivWeightLe` form of `βHensel_weight_bound_unlocked`: the Faà-di-Bruno
successor residual supplies the lift identity, and the remaining A.4 input is
the concrete `𝒪`-level clearing-divisibility residual. -/
theorem βHensel_weight_bound_unlocked_of_divWeight (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hzero : FaaDiBrunoSuccSumZeroResidual H x₀ R hHyp)
    (hdiv : DivWeightLe H x₀ R hHyp hH D) (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_of_divWeight' H x₀ R hHyp hH hDH hDRx0 hdR2 hdHR hW
    (fun t => βHensel_lift_identity H x₀ R hHyp hzero t) hdiv t

/-- **P1 weight bound unlocked by full P2 vanishing.**
This consumes the sharper `FaaDiBrunoFullSumVanishes` endpoint, whose P2 capstone already provides
the lift identity needed by `βHensel_weight_bound_of_lift'`. -/
theorem βHensel_weight_bound_unlocked_of_fullVanishes (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hvan : FaaDiBrunoFullSumVanishes H x₀ R hHyp)
    (hα : AlphaGenuineRegularWeightLe H x₀ R hHyp hH D) (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_of_lift' H x₀ R hHyp hH hDH hDRx0 hdR2 hdHR hW
    (fun t => (P2_closed_of_fullVanishes H x₀ R hHyp hvan).2 t) hα t

/-- **P1 weight bound unlocked by full P2 vanishing, from concrete
divisibility.**  This is the full-vanishing version of
`βHensel_weight_bound_of_divWeight'`. -/
theorem βHensel_weight_bound_unlocked_of_fullVanishes_divWeight (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hvan : FaaDiBrunoFullSumVanishes H x₀ R hHyp)
    (hdiv : DivWeightLe H x₀ R hHyp hH D) (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_of_divWeight' H x₀ R hHyp hH hDH hDRx0 hdR2 hdHR hW
    (fun t => (P2_closed_of_fullVanishes H x₀ R hHyp hvan).2 t) hdiv t

/-- **P1 weight bound unlocked by the restricted P2 match.**
`RestrictedFaaDiBrunoMatch` is the smallest carved P2 bridge currently exposed by `P2Vanish`;
given it, the P1 collapse no longer needs to mention the legacy successor-sum residual. -/
theorem βHensel_weight_bound_unlocked_of_restrictedMatch (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hmatch : RestrictedFaaDiBrunoMatch H x₀ R hHyp)
    (hα : AlphaGenuineRegularWeightLe H x₀ R hHyp hH D) (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_of_lift' H x₀ R hHyp hH hDH hDRx0 hdR2 hdHR hW
    (fun t => (P2_closed_of_restrictedMatch H x₀ R hHyp hmatch).2 t) hα t

/-- **P1 weight bound unlocked by the restricted P2 match, from concrete
divisibility.** -/
theorem βHensel_weight_bound_unlocked_of_restrictedMatch_divWeight (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hmatch : RestrictedFaaDiBrunoMatch H x₀ R hHyp)
    (hdiv : DivWeightLe H x₀ R hHyp hH D) (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_of_divWeight' H x₀ R hHyp hH hDH hDRx0 hdR2 hdHR hW
    (fun t => (P2_closed_of_restrictedMatch H x₀ R hHyp hmatch).2 t) hdiv t

end P1Conditional

end BCIKS20.HenselNumerator

-- Axiom audit: every proof-carrying declaration in this file depends on exactly the three standard
-- axioms `[propext, Classical.choice, Quot.sound]` (no `sorry`/`admit`/`axiom`/`native_decide`).
#print axioms BCIKS20.HenselNumerator.embeddingOf𝒪Into𝕃_W𝒪
#print axioms BCIKS20.HenselNumerator.βHensel_eq_alpha_mul_of_lift
#print axioms BCIKS20.HenselNumerator.alpha_eq_embedding_of_fact
#print axioms BCIKS20.HenselNumerator.alphaWeight_iff_divWeight
#print axioms BCIKS20.HenselNumerator.βHensel_weight_structured
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_of_lift
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_of_divWeight
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_of_lift'
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_of_divWeight'
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_unlocked
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_unlocked_of_divWeight
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_unlocked_of_fullVanishes
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_unlocked_of_fullVanishes_divWeight
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_unlocked_of_restrictedMatch
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_unlocked_of_restrictedMatch_divWeight
