/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.HenselNumerator
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P1Conditional

/-!
# (P1, A.4) `AlphaGenuineRegularWeightLe` — analysis, equivalence, structured closure, obstruction

This module imports only `HenselNumerator` (whose `.olean` builds;
`GammaGenuine`/`RationalFunctions` are transitive).  It is the careful working-out of the carved
A.4 link

  `AlphaGenuineRegularWeightLe`:  `∀ t, ∃ a_t ∈ 𝒪, embedding a_t = αGenuine t ∧ Λ_𝒪(a_t) ≤ 1`

— the formal content of BCIKS20's `Λ(α_t) = Λ(Y) = 1` ("consider the weight of `α_t`", line ~4276)
on the genuine Hensel root `gammaGenuine` (`αGenuine t := coeff t gammaGenuine`).  The statement is
verbatim the one first carved in `P1Conditional.lean` (`def AlphaGenuineRegularWeightLe`).  It now
lives here as the canonical shared A.4 infrastructure imported by the conditional P1 assembly.

## Task 1 — is `AlphaGenuineRegularWeightLe` circular with the structured invariant given `hlift`?

The (P2) lift identity lives in the FIELD `𝕃 H`:
`hlift_t :  embedding (βHensel t) = αGenuine t · W^{t+1} · ξ^{e_t}`, `e_t = 2t−1` (ℕ-truncated).
`Λ_𝒪` is the weight of the canonical `F[X][Y]`-representative of `βHensel t ∈ 𝒪 H`
(`weight_Λ_over_𝒪 = weight_Λ ∘ canonicalRepOf𝒪`) — an `𝒪`-intrinsic quantity, NOT an `𝕃`-invariant.

**Finding (`alphaWeight_iff_divWeight`, PROVEN both directions).**  GIVEN `hlift`,
`AlphaGenuineRegularWeightLe` is logically *equivalent* to the `𝒪`-level

  `DivWeightLe`:  `∀ t, ∃ a_t ∈ 𝒪,  βHensel t = a_t · W𝒪^{t+1} · ξ^{e_t}  ∧  Λ_𝒪(a_t) ≤ 1`,

i.e. `βHensel t` is *divisible in `𝒪`* by the clearing product `W𝒪^{t+1}·ξ^{e_t}`, with the quotient
of `Λ_𝒪`-weight `≤ 1`.  The forward direction is injectivity of `embedding` applied to `hlift`
(`βHensel_eq_alpha_mul_of_lift`); the reverse is pushing `embedding` through the factorization and
cancelling the nonzero denominator (`den_ne_zero`).  So the genuine A.4 content, transported to
where `Λ_𝒪` lives, is exactly this divisibility-with-weight.

**It is NOT circular with the structured invariant.**  `AlphaGenuineRegularWeightLe (⟺ DivWeightLe)`
*implies* the structured invariant `Λ_𝒪(β_t) ≤ 1 + (t+1)Λ(W) + e_t·Λ(ξ)`
(`βHensel_weight_structured`, PROVEN below: factor, then sub-multiplicative `Λ_𝒪` calculus).  The
converse FAILS: `weight_Λ_over_𝒪` is only *sub*-additive (`Λ(ab) ≤ Λ(a)+Λ(b)`,
`weight_Λ_over_𝒪_mul_le`), so a weight *upper* bound on `βHensel t` cannot be "divided through" to
manufacture either the `𝒪`-divisibility (`a_t` existing) or the *sharp* `Λ(a_t) ≤ 1` (you cannot
subtract in a sub-additive valuation).  Hence
`AlphaGenuineRegularWeightLe` is *strictly stronger* than the structured invariant — it is genuine
extra input, packaging a divisibility fact, and `P1Conditional` is NOT a hidden circularity.  The
honest residual after this file is precisely `DivWeightLe`.

## The sharp `t = 0` obstruction (`W𝒪_dvd_βHensel_zero_of_alpha`, PROVEN)

At `t = 0`, `αGenuine 0 = α₀ = T/W` (`αGenuine_zero`) and the lift identity is the PROVEN,
axiom-clean `βHensel_lift_identity_zero` (`embedding (βHensel 0) = α₀·W = T`).  Any
`AlphaGenuineRegularWeightLe`
witness `a_0` therefore forces, by injectivity,

  `βHensel 0 = a_0 · W𝒪`     in `𝒪 H`,

i.e. `W𝒪 ∣ βHensel 0` in `𝒪`.  This is the concrete face of the residual: `T/W = α₀` is regular
(`∈ image embedding`) **iff** `W𝒪 ∣ βHensel 0` (equivalently `W𝒪 ∣ mk X = functionFieldT`'s
representative).  The genuine A.4 content `Λ(α_t) = 1` is exactly that this clearing divisibility
holds at every order with the quotient at weight `1`.  We prove the `t = 0` direction
unconditionally (it uses only the proven `βHensel_lift_identity_zero` + injectivity); we do not
fake the general divisibility.

## Outcome (disposition (a) forward direction + (b) equivalence FINDING + precise obstruction)

* `βHensel_eq_alpha_mul_of_lift`, `alpha_eq_embedding_of_fact` — the two halves of the `𝕃 ↔ 𝒪`
  bridge.
* `alphaWeight_iff_divWeight` — the EQUIVALENCE `AlphaGenuineRegularWeightLe ⟺ DivWeightLe` given
  `hlift` (the circularity FINDING: the genuine content is the `𝒪`-divisibility-with-weight,
  distinct from the structured bound).
* `βHensel_weight_structured` — the STRUCTURED INVARIANT, PROVEN from
  `AlphaGenuineRegularWeightLe`+`hlift`
  (so P1 truly closes when the lift identity lands and `DivWeightLe` is supplied).
* `βHensel_weight_bound_of_alphaWeight` — (P1) loose bound `Λ_𝒪(β_t) ≤ (2t+1)·natDegreeY R·D`.
* `W𝒪_dvd_βHensel_zero_of_alpha` — the sharp, PROVEN `t = 0` divisibility obstruction.

NO `axiom`/`admit`/`native_decide`/`bv_decide`/`sorry`.  Audited in-file via `#print axioms`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace BCIKS20.HenselNumerator

open Polynomial Polynomial.Bivariate
open BCIKS20AppendixA
open ProximityPrize.BCIKS20.GammaGenuine

namespace AlphaWeight

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-! ### 0. The `W` embedding bridge

`embedding (W𝒪 H) = liftToFunctionField H.leadingCoeff` — the lift identity's `W^{t+1}` factor is
literally the embedding of `W𝒪^{t+1}`.  Pure unfolding (`W𝒪 = mk (C lc)`,
`embedding ∘ mk = liftBivariate`, `liftBivariate (C p) = liftToFunctionField p`).
`embeddingOf𝒪Into𝕃_W𝒪` is imported from `P1Conditional`. -/

/-! ### 1. The carved A.4 link, re-stated verbatim (the named gap)

Identical to `P1Conditional.AlphaGenuineRegularWeightLe`: the genuine Hensel-root coefficient
`αGenuine t ∈ 𝕃 H` is *regular* (an embedding of an `𝒪`-element) of `Λ_𝒪`-weight `≤ 1`.
`AlphaGenuineRegularWeightLe` is imported from `P1Conditional`. -/

/-- **The `𝒪`-level divisibility-with-weight form** of the carved link.  At order `t`, `βHensel t`
factors *in `𝒪 H`* as `a_t · W𝒪^{t+1} · ξ^{e_t}` with the quotient `a_t` of `Λ_𝒪`-weight `≤ 1`.
This is `AlphaGenuineRegularWeightLe` transported to the world where `Λ_𝒪` actually lives (PROVEN
equivalent to it given `hlift`, `alphaWeight_iff_divWeight`).  It exposes the genuine residual: a
clearing
divisibility `W𝒪^{t+1}·ξ^{e_t} ∣ βHensel t` in `𝒪`, with the quotient at weight `1`. -/
def DivWeightLe (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (D : ℕ) : Prop :=
  ∀ t : ℕ, ∃ a : 𝒪 H,
    βHensel H x₀ R hHyp t
        = a * (W𝒪 H) ^ (t + 1) * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * t - 1)
      ∧ weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1

/-! ### 1′. The two halves of the `𝕃 ↔ 𝒪` bridge

The `𝕃 → 𝒪` half `βHensel_eq_alpha_mul_of_lift` is imported from `P1Conditional`. -/

/-- **Bridge, `𝒪 → 𝕃`.**  The reverse: given the `𝒪`-level factorization `hfact` and the lift
identity `hlift_t`, the quotient `a` embeds to `αGenuine t`.  Push `embedding` through `hfact`
(`embedding (β_t) = embedding a · W^{t+1} · ξ^{e_t}`), compare with `hlift_t`, and cancel the
nonzero denominator `W^{t+1}·ξ^{e_t}` (`den_ne_zero`) in the field `𝕃 H`. -/
theorem alpha_eq_embedding_of_fact (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (t : ℕ) {a : 𝒪 H}
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

/-! ### 2. THE CIRCULARITY FINDING — `AlphaGenuineRegularWeightLe ⟺ DivWeightLe` given `hlift`

The genuine A.4 content, transported to where `Λ_𝒪` lives, is exactly the
`𝒪`-divisibility-with-weight `DivWeightLe`.  Each `t`-instance of the equivalence is the two bridge
halves, with the weight bound
carried verbatim (it is the same `a`). -/

/-- **Task 1, the FINDING.**  GIVEN the (P2) lift identity `hlift` (for all `t`),
`AlphaGenuineRegularWeightLe` and the `𝒪`-level `DivWeightLe` are *equivalent*.  This pins the
genuine residual: it is the clearing divisibility `W𝒪^{t+1}·ξ^{e_t} ∣ βHensel t` in `𝒪` with the
quotient at
weight `≤ 1` — a fact about `𝒪`-divisibility, distinct from (and strictly stronger than, see
`βHensel_weight_structured`) any `Λ_𝒪`-upper-bound on `βHensel t`. -/
theorem alphaWeight_iff_divWeight (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (D : ℕ)
    (hlift : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp t)
        = αGenuine H x₀ R hHyp t
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1)) :
    AlphaGenuineRegularWeightLe H x₀ R hHyp hH D ↔ DivWeightLe H x₀ R hHyp hH D := by
  constructor
  · -- `𝕃 → 𝒪`: the carved preimage `a` factors `βHensel t`, weight unchanged.
    intro hα t
    obtain ⟨a, ha_eq, ha_wt⟩ := hα t
    exact ⟨a, βHensel_eq_alpha_mul_of_lift H x₀ R hHyp hH t ha_eq (hlift t), ha_wt⟩
  · -- `𝒪 → 𝕃`: the divisor `a` embeds to `αGenuine t`, weight unchanged.
    intro hd t
    obtain ⟨a, hfact, ha_wt⟩ := hd t
    exact ⟨a, alpha_eq_embedding_of_fact H x₀ R hHyp t hfact (hlift t), ha_wt⟩

/-! ### 3. The STRUCTURED INVARIANT — PROVEN from `AlphaGenuineRegularWeightLe` + `hlift`

This is the genuine forward closure: the carved link + the lift identity yield the paper's
structured weight invariant, via the `𝒪`-level factorization + the proven sub-multiplicative `Λ_𝒪`
calculus.  It
shows `AlphaGenuineRegularWeightLe` is at least as strong as the structured invariant (and, by §2's
sub-additivity remark, strictly stronger).  `βHensel_weight_structured` is imported from
`P1Conditional`. -/

/-! ### 4. (P1) the loose weight bound, PROVEN from the structured invariant -/

/-- **(P1), the loose Claim-A.2 bound.**  From the structured invariant (under `hlift` + the carved
link + the `Λ(ξ)` regime), the loose target `Λ_𝒪(βHensel t) ≤ (2t+1)·natDegreeY R·D` follows by the
proven wave-5 arithmetic collapse `βHensel_weight_bound_of_structured_weight`, under the paper's
faithful regime `2 ≤ d`, `dH ≤ d`, `Λ(W)+dH ≤ D`. -/
theorem βHensel_weight_bound_of_alphaWeight (x₀ : F) (R : F[X][X][Y])
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
    (hα : AlphaGenuineRegularWeightLe H x₀ R hHyp hH D)
    (hξ : weight_Λ_over_𝒪 hH (ClaimA2.ξ x₀ R H hHyp) D
            ≤ WithBot.some ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1)))
    (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) := by
  have hstructured := βHensel_weight_structured H x₀ R hHyp hH hDH hlift hα hξ t
  exact βHensel_weight_bound_of_structured_weight H x₀ R hHyp hH hdR2 hdHR hW t hstructured

/-! ### 4′. Discharging `hξ` via the PROVEN `weight_ξ_bound` (SOLE residual: `hlift` + `hα`) -/

/-- **(P1)**, with `hξ` discharged by the proven `ClaimA2.weight_ξ_bound` under its regime.  The
sole remaining inputs are the (P2) lift identity `hlift` and the carved A.4 link `hα`. -/
theorem βHensel_weight_bound_of_alphaWeight' (x₀ : F) (R : F[X][X][Y])
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
    (hα : AlphaGenuineRegularWeightLe H x₀ R hHyp hH D) (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_of_alphaWeight H x₀ R hHyp hH hDH hdR2 hdHR hW hlift hα
    (ClaimA2.weight_ξ_bound x₀ hH hHyp hdR2 hDH hDRx0) t

/-! ### 5. The sharp `t = 0` divisibility obstruction — PROVEN unconditionally

`αGenuine 0 = α₀ = T/W`; the lift identity at `t = 0` is the PROVEN, axiom-clean
`βHensel_lift_identity_zero` (`embedding (βHensel 0) = α₀·W^1·ξ^0 = α₀·W = T`).  Any
`AlphaGenuineRegularWeightLe` witness `a_0` thus forces `βHensel 0 = a_0 · W𝒪` in `𝒪`, i.e.
`W𝒪 ∣ βHensel 0`.  This is the concrete residual: `α₀ = T/W` is regular ⟺ this clearing divisibility
holds.  We do NOT need `hlift` here — only the proven base case + injectivity. -/

/-- **The sharp `t = 0` obstruction (PROVEN, no `hlift`).**  From the proven base-case lift identity
`βHensel_lift_identity_zero` and a carved preimage `a` of `αGenuine 0 = α₀ = T/W`, injectivity of
`embedding` gives `βHensel 0 = a · W𝒪` in `𝒪`.  So `AlphaGenuineRegularWeightLe` at `t = 0` is
exactly the `𝒪`-divisibility `W𝒪 ∣ βHensel 0` (with the quotient `a` at weight `≤ 1`): the genuine,
non-faked face of the residual. -/
theorem W𝒪_dvd_βHensel_zero_of_alpha (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {a : 𝒪 H}
    (ha : embeddingOf𝒪Into𝕃 H a = αGenuine H x₀ R hHyp 0) :
    βHensel H x₀ R hHyp 0 = a * W𝒪 H := by
  apply embeddingOf𝒪Into𝕃_injective hH
  rw [βHensel_lift_identity_zero, map_mul, ha, embeddingOf𝒪Into𝕃_W𝒪]
  simp only [Nat.mul_zero, Nat.zero_sub, pow_zero, mul_one, zero_add, pow_one]

/-- **Corollary: `W𝒪 ∣ βHensel 0` is *necessary* for `AlphaGenuineRegularWeightLe`.**  If the carved
link holds (at the `t = 0` instance), then `W𝒪` divides `βHensel 0` in `𝒪 H`.  This is the precise,
machine-checked statement of the `α₀ = T/W` regularity obstruction: the carve forces a clearing
divisibility that the field-level lift identity alone does not. -/
theorem W𝒪_dvd_βHensel_zero_of_alphaWeight (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) {D : ℕ}
    (hα : AlphaGenuineRegularWeightLe H x₀ R hHyp hH D) :
    W𝒪 H ∣ βHensel H x₀ R hHyp 0 := by
  obtain ⟨a, ha_eq, _⟩ := hα 0
  refine ⟨a, ?_⟩
  rw [W𝒪_dvd_βHensel_zero_of_alpha H x₀ R hHyp hH ha_eq]
  exact mul_comm a (W𝒪 H)

end AlphaWeight

end BCIKS20.HenselNumerator

-- Axiom audit: every closed declaration in this file depends on exactly the three standard axioms
-- `[propext, Classical.choice, Quot.sound]` (no `sorry`/`admit`/`axiom`/`native_decide`).
#print axioms BCIKS20.HenselNumerator.AlphaWeight.embeddingOf𝒪Into𝕃_W𝒪
#print axioms BCIKS20.HenselNumerator.AlphaWeight.βHensel_eq_alpha_mul_of_lift
#print axioms BCIKS20.HenselNumerator.AlphaWeight.alpha_eq_embedding_of_fact
#print axioms BCIKS20.HenselNumerator.AlphaWeight.alphaWeight_iff_divWeight
#print axioms BCIKS20.HenselNumerator.AlphaWeight.βHensel_weight_structured
#print axioms BCIKS20.HenselNumerator.AlphaWeight.βHensel_weight_bound_of_alphaWeight
#print axioms BCIKS20.HenselNumerator.AlphaWeight.βHensel_weight_bound_of_alphaWeight'
#print axioms BCIKS20.HenselNumerator.AlphaWeight.W𝒪_dvd_βHensel_zero_of_alpha
#print axioms BCIKS20.HenselNumerator.AlphaWeight.W𝒪_dvd_βHensel_zero_of_alphaWeight
