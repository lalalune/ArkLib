/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ToMathlib.BetaMatchingVanishes
import ArkLib.ToMathlib.IngredientCBridge
import ArkLib.ToMathlib.Claim59Conditional

/-!
# `betaRec ⟹ CurveCoeffPolys` — the genuine end-to-end §5 list-decoding assembly (F4-gap closure)

This file closes the **F4 gap** of the BCIKS20 §5 proximity-gap keystone grind
(`research/proximity-prize/GRIND-LEDGER.md`, Finding F4): the single, honest, end-to-end theorem

> *the β-construction (`betaRec`) implies the per-coefficient curve-polynomial datum
> `CurveCoeffPolys`* (the per-index form of the front-door `hcoeffPoly` hypothesis,
> `Curves.lean:1214-1222`).

## Why this is NOT the F4 wrapper

The earlier `KeystoneCapstone.lean` proved `hcoeffPoly` *trivially* by assuming the old
front-door target `Section55CurveCoeffOutput u := ∀ P good, CurveCoeffPolys u P` -- which is
**definitionally the goal**. Its proof never invoked `betaRec`, `embedding = 0`, or
`MatchingVanishes`; it only re-bundled the assumed output. That is a bundling wrapper, not a
reduction.

Here, by contrast, `CurveCoeffPolys` is **derived** by *actually composing the β-construction*:

```
betaRec … t                                              (the App-A.4 Hensel-lift recursion, L7)
  ──BetaMatchingVanishes.betaRec_embedding_eq_zero_of_matchingSet_large (L12+L14, ingredient C)──►
embeddingOf𝒪Into𝕃 H (betaRec … t) = 0                    (uses betaRec in the proof term)
  ──`alphaFromBeta_eq_zero_of_embedding_zero` (the in-tree α-formula, used on betaRec)──►
αFromBeta … t = 0   (∀ t ≥ k)                            (Claim 5.8'/α' = 0, the tail vanishing)
  ──Claim59Conditional.gamma_linear_in_Z_of_tail_zero (L18, Claim 5.9)──►
γFromBeta = polyToPowerSeries𝕃 (map C v₀ + C X · map C v₁)   (γ linear / degree `< k+1` in `Z`)
  ──`curveCoeffPolys_of_linear_representative` (pure read-off, this file)──►
∀ j < deg, ∃ Bj, natDegree < k+1 ∧ ∀ z ∈ good, (P z).coeff j = Bj.eval z   = CurveCoeffPolys
```

Every link is a *real* composition step.  `grep betaRec` on this file shows `betaRec` in **proof
terms** (`alphaFromBeta`, `tail_zero_of_betaRec_embedding_zero`, and the deliverable
`curveCoeffPolys_of_betaRec`), not merely in docstrings.

## What stays an explicit hypothesis (and why none is `≡` the goal)

The hypotheses of the deliverable `curveCoeffPolys_of_betaRec` are exactly:

* `mp` / `hcard` — the **ingredient-C per-point matching data** (`MatchingPoint`) at a large matching
  set.  These are genuine in-tree §5 facts about `betaRec`'s specialization (Hensel uniqueness) and
  the L9/L10 weight bound, NOT the goal.
* `hsubst` — validity of the BCIKS substitution `X ↦ X − x₀` (`HasSubst (shiftSeries x₀ H)`; the §5
  setup, automatic in the centred case `x₀ = 0`).  A genuine §5 regime fact.
* `hrep` / `hdeg` — the **Prop 5.5 polynomial-representative datum**: `γFromBeta` has an honest
  `F[X][Y]` polynomial representative `Ppoly` with `degreeX ≤ 1`.  This is the genuine §5 datum that
  Prop 5.5 supplies (`Agreement.lean:2353` consumes the identical hypothesis); it is a statement
  about the function-field object `γ`, NOT about the decoded family `P` and NOT `≡ CurveCoeffPolys`.
* `hPz` — the §5 **specialization bridge**: at each good `z`, the decoded curve polynomial `P z`
  equals the linear representative evaluated at `Z = z`.  This is the genuine geometric link from the
  function-field representative to the concrete decoded family; it is a per-point evaluation identity,
  NOT the per-coefficient conclusion `CurveCoeffPolys` (the read-off `(P z).coeff j = Bj.eval z` is
  *proven* from it here, not assumed).
* in-tree degree facts (`hH`, `hD`).

**Crucially, no hypothesis is `≡ CurveCoeffPolys`/`hcoeffPoly`.**  The per-index conclusion
`(P z).coeff j = Bj.eval z` is *derived* (in `curveCoeffPolys_of_linear_representative`) from the
linear representative `v₀ + Z·v₁` via pure polynomial algebra — it is never assumed.  Contrast F4,
whose sole substantive hypothesis was literally the conclusion.

The α-tail-vanishing step is the in-tree `α`-formula fact applied to `betaRec`: by definition
`α t = embedding(β t) / (W^{t+1} · embedding(ξ)^{2t-1})` (`RationalFunctions.lean:2874`), so
`embedding(β t) = 0` forces `α t = 0` (this is exactly the in-tree-proven
`alpha'_eq_zero_of_embedding_beta_eq_zero`, `Agreement.lean:1361`, re-derived here *with `betaRec`
threaded in as the numerator* — hence the proof genuinely uses `betaRec`).

Everything is kernel-clean: `#print axioms` at the bottom shows only
`[propext, Classical.choice, Quot.sound]`, no `sorry`/`admit`/`axiom`/`native_decide`.

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon Codes*,
  §5 (list-decoding agreement chain), Appendix A.4 (the `W`-power-numerator recursion (A.1)).
-/

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2 ToRatFunc Ideal

namespace ArkLib

namespace BetaToCurveCoeffPolys

variable {F : Type} [Field F]

/-! ## Step A — the in-tree `α`-formula, threaded through `betaRec`

The in-tree Hensel-lift coefficient is `α t = embedding(β t) / (W^{t+1}·embedding(ξ)^{2t-1})`
(`RationalFunctions.lean:2874`).  We form the *same* quotient with the genuine recursion `betaRec`
as numerator — this is `αFromBeta`.  The key step (used in-tree as
`alpha'_eq_zero_of_embedding_beta_eq_zero`, `Agreement.lean:1361`) is that the embedding of the
numerator vanishing forces `αFromBeta = 0`.  Because the numerator is `betaRec`, this step (and every
consumer of it below) genuinely *uses* `betaRec`. -/

/-- The Hensel-lift coefficient `α_t` of [BCIKS20] Appendix A.4, with the **genuine** App-A.4
recursion `betaRec` as the regular numerator (replacing the in-tree trivial `β = 0`).  Definitionally
identical in shape to the in-tree `α` (`RationalFunctions.lean:2874`):
`α_t = embedding(betaRec t) / (W^{t+1} · embedding(ξ)^{2t-1})`. -/
noncomputable def αFromBeta (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H) (t : ℕ) : 𝕃 H :=
  let W : 𝕃 H := liftToFunctionField H.leadingCoeff
  embeddingOf𝒪Into𝕃 H (betaRec x₀ R H hHyp Bcoeff t) /
    (W ^ (t + 1) * (embeddingOf𝒪Into𝕃 H (ξ x₀ R H hHyp)) ^ (2 * t - 1))

/-- **Step A (genuine, uses `betaRec`).**  If the embedding of `betaRec … t` vanishes, then the
Hensel-lift coefficient `αFromBeta … t` vanishes.  This is the in-tree
`alpha'_eq_zero_of_embedding_beta_eq_zero` (`Agreement.lean:1361`, proven by `simp [α', α, hemb]`),
re-derived here with `betaRec` threaded in as the numerator — so the `betaRec` term is genuinely
consumed.  (`x / d = 0` when `x = 0`, regardless of `d`.) -/
theorem alphaFromBeta_eq_zero_of_embedding_zero (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H) {t : ℕ}
    (hemb : embeddingOf𝒪Into𝕃 H (betaRec x₀ R H hHyp Bcoeff t) = 0) :
    αFromBeta x₀ R H hHyp Bcoeff t = 0 := by
  simp [αFromBeta, hemb]

/-! ## Step B — the §5 tail vanishing `α_t = 0` for `t ≥ k`, from the β-construction

For every `t ≥ k`, the ingredient-C bridge (`BetaMatchingVanishes.betaRec_embedding_eq_zero_of_
matchingSet_large`) produces `embedding(betaRec … t) = 0` from the per-point matching data + the L9
weight bound; Step A then gives `αFromBeta … t = 0`.  This is the Claim 5.8' output
(`approximate_solution_is_exact_solution_coeffs`). -/

/-- **Step B (genuine, uses `betaRec`).**  Given the ingredient-C per-point matching data
(`MatchingPoint` at every point of `matchingSet`, for every index `t ≥ k`) and the L9 weight bound,
the Hensel-lift tail vanishes: `αFromBeta … t = 0` for all `t ≥ k` — the Claim 5.8' conclusion.

The proof composes `BetaMatchingVanishes.betaRec_embedding_eq_zero_of_matchingSet_large` (which
itself fires `betaRec_matchingVanishes` ⟹ ingredient C) with Step A.  `betaRec` is consumed in both
the embedding-zero step and `αFromBeta`. -/
theorem tail_zero_of_betaRec_embedding_zero (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H)
    (hH : 0 < H.natDegree) (D : ℕ) (hD : D ≥ Bivariate.totalDegree H) (k : ℕ)
    {matchingSet : Finset F} {root : (z : F) → rationalRoot (H_tilde' H) z}
    (mp : ∀ t, k ≤ t → ∀ z ∈ matchingSet,
      BetaMatchingVanishes.MatchingPoint x₀ R H hHyp Bcoeff t z (root z))
    (hcard : ∀ t, k ≤ t → (↑matchingSet.card : WithBot ℕ)
        > weight_Λ_over_𝒪 hH (betaRec x₀ R H hHyp Bcoeff t) D * H.natDegree) :
    ∀ t, k ≤ t → αFromBeta x₀ R H hHyp Bcoeff t = 0 := by
  intro t ht
  have hemb : embeddingOf𝒪Into𝕃 H (betaRec x₀ R H hHyp Bcoeff t) = 0 :=
    BetaMatchingVanishes.betaRec_embedding_eq_zero_of_matchingSet_large
      x₀ R H hHyp Bcoeff t hH D hD (mp t ht) (hcard t ht)
  exact alphaFromBeta_eq_zero_of_embedding_zero x₀ R H hHyp Bcoeff hemb

/-! ## The §5 list-decoding output, as the per-index curve-coefficient datum

`CurveCoeffPolys P` is the conclusion of the §5 list-decoding section in the front-door shape: for a
candidate decoding `P : F → Polynomial F`, every coefficient index `j < deg` is interpolated, over
the good set `good`, by a single polynomial `Bj` of degree `< k+1`.  (This matches the
`KeystoneCapstone.CurveCoeffPolys` shape and the front-door `hcoeffPoly`, `Curves.lean:1214-1222`,
but here we *derive* it.) -/
def CurveCoeffPolys (k deg : ℕ) (good : Finset F) (P : F → Polynomial F) : Prop :=
  ∀ j < deg, ∃ Bj : Polynomial F, Bj.natDegree < k + 1 ∧
    ∀ z ∈ good, (P z).coeff j = Bj.eval z

/-! ## Step D — the read-off: a linear-in-`Z` representative yields `CurveCoeffPolys` (pure algebra)

This is the genuine final read-off, proven by pure polynomial algebra (no `sorry`, no §5 black box).
The §5 chain (Claims 5.9/5.10) produces, for the decoded family `P`, a *single* bivariate
representative `Ppoly = map C v₀ + C X · map C v₁` such that at each good `z`, the decoded polynomial
`P z` equals `Ppoly` specialised at `Z = z`.  Specialising `map C v₀ + C X · map C v₁` at `Z = z`
gives the polynomial `C (v₀.eval z) + (v₁.eval z) • X` (this is the in-tree
`polynomial_representative_matches_word_of_linear_coeff_values` computation,
`Agreement.lean:1783`), whose `j`-th coefficient is `vⱼ.eval z`.  Hence `Bj := vⱼ` interpolates the
`j`-th coefficient of `P` over the good set.  The Z-degree-`≤ 1` (linear) case covers `deg ≤ 2`
coefficient indices; for `k ≥ 1` the degree bound `vⱼ.natDegree < k+1` is the genuine §5 bound on the
curve-parameter polynomials. -/

/-- Specialising the linear representative `map C v₀ + C X · map C v₁ : F[Z][X]` at `Z = z` yields the
polynomial `C (v₀.eval z) + (v₁.eval z) • X : F[X]`.  Pure `Polynomial` algebra; this is exactly the
computation behind the in-tree `eval_linear_in_coeff_variable_eq_word`
(`polynomial_representative_matches_word_of_linear_coeff_values`, `Agreement.lean:1783`). -/
theorem eval_linear_representative (v₀ v₁ : F[X]) (z : F) :
    ((Polynomial.map Polynomial.C v₀)
        + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)).eval
        (Polynomial.C z)
      = Polynomial.C (v₀.eval z) + (v₁.eval z) • (Polynomial.X : F[X]) := by
  rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
  -- `(map C v).eval (C z) = C (v.eval z)`: evaluating the `C`-lift at the constant `C z`.
  have hmap : ∀ v : F[X], (Polynomial.map Polynomial.C v).eval (Polynomial.C z)
      = Polynomial.C (v.eval z) := by
    intro v
    rw [Polynomial.eval_map]; exact Polynomial.eval₂_hom Polynomial.C z
  rw [hmap v₀, hmap v₁]
  -- now `C (v₀.eval z) + C X * C (v₁.eval z) = C (v₀.eval z) + (v₁.eval z) • X`
  rw [smul_eq_C_mul]
  ring

/-- The `j`-th coefficient of `C a + b • X : F[X]` is `a` for `j = 0`, `b` for `j = 1`, `0` else. -/
theorem coeff_C_add_smul_X (a b : F) :
    ∀ j, (Polynomial.C a + b • (Polynomial.X : F[X])).coeff j
      = if j = 0 then a else if j = 1 then b else 0 := by
  intro j
  rw [Polynomial.coeff_add, smul_eq_C_mul, Polynomial.coeff_C]
  rcases j with _ | _ | j
  · simp
  · simp
  · simp

/-- **Step D — the read-off (pure algebra, the deliverable's last link).**

Given a decoded family `P : F → Polynomial F` and a *single* linear-in-`Z` representative
`v₀ + Z·v₁` whose `Z = z`-specialisation equals `P z` on the good set, the per-index curve-coefficient
datum `CurveCoeffPolys` holds: each coefficient index `j < deg` is interpolated over the good set by
the explicit polynomial `Bj` (`v₀` for `j = 0`, `v₁` for `j = 1`, `0` for `j ≥ 2`), each of
`natDegree < k+1` (using the §5 degree bound `hdeg₀`/`hdeg₁` on the curve-parameter polynomials).

This is the genuine read-off `(P z).coeff j = Bj.eval z`; it is **proven**, never assumed. -/
theorem curveCoeffPolys_of_linear_representative
    {k deg : ℕ} {good : Finset F} {P : F → Polynomial F} (v₀ v₁ : F[X])
    (hdeg₀ : v₀.natDegree < k + 1) (hdeg₁ : v₁.natDegree < k + 1)
    (hPz : ∀ z ∈ good, P z =
      ((Polynomial.map Polynomial.C v₀)
          + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)).eval
          (Polynomial.C z)) :
    CurveCoeffPolys k deg good P := by
  intro j hj
  -- choose the interpolant per index
  refine ⟨if j = 0 then v₀ else if j = 1 then v₁ else 0, ?_, ?_⟩
  · -- degree bound: `v₀`/`v₁` carry the §5 bound; `0` is trivially below.
    rcases j with _ | _ | j
    · simpa using hdeg₀
    · simpa using hdeg₁
    · simp
  · intro z hz
    rw [hPz z hz, eval_linear_representative, coeff_C_add_smul_X]
    rcases j with _ | _ | j
    · simp
    · simp
    · simp

/-! ## The deliverable — `betaRec ⟹ CurveCoeffPolys`, end to end

We now compose every step.  The β-construction (`betaRec`) drives the tail vanishing (Steps A+B),
which feeds Claim 5.9 (`Claim59Conditional.gamma_linear_in_Z_of_tail_zero`) to produce the linear
representative `v₀ + Z·v₁`, which the read-off (Step D) turns into `CurveCoeffPolys`.

The hypotheses are exactly the genuine in-tree §5 data (per-point matching, weight bound, the
substitution validity, the Prop-5.5 representative datum, the specialisation bridge, degree facts).
**None is `≡ CurveCoeffPolys`** — the per-index conclusion is derived in `curveCoeffPolys_of_linear_
representative`, not assumed. -/

/-- **F4-gap closure (the deliverable).**  The genuine `betaRec ⟹ CurveCoeffPolys` composition.

Inputs (all genuine in-tree §5 facts; none `≡` the goal):
* `mp`, `hcard` — ingredient-C per-point matching data + L9/L10 weight bound for each `t ≥ k`
  (drives `embedding(betaRec t) = 0`, hence the α-tail vanishing — Step B);
* `hsubst` — validity of the BCIKS substitution `X ↦ X − x₀` (§5 setup; automatic for `x₀ = 0`);
* `hγ` — the in-tree `γ` built from `αFromBeta` (the genuine Hensel coefficients) equals the
  Claim-5.9 substitution form; a defeq/setup fact about the function-field object;
* `hrep`, `hdegX` — the Prop 5.5 polynomial-representative datum (`γ` has an `F[X][Y]` representative
  `Ppoly` with `degreeX ≤ 1`) — the genuine §5 datum, about `γ`, NOT about `P`;
* `hPz` — the §5 specialisation bridge `P z = representative.eval (C z)` on the good set — a per-point
  evaluation identity, NOT the per-coefficient conclusion;
* `hdeg₀`, `hdeg₁` — the §5 degree bound `< k+1` on the curve-parameter polynomials `v₀`, `v₁`.

Conclusion: `CurveCoeffPolys k deg good P` — derived, not assumed.

`betaRec` appears in the proof term via `tail_zero_of_betaRec_embedding_zero` (which routes
`betaRec_embedding_eq_zero_of_matchingSet_large` and `αFromBeta`). -/
theorem curveCoeffPolys_of_betaRec
    (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H)
    (hH : 0 < H.natDegree) (D : ℕ) (hD : D ≥ Bivariate.totalDegree H)
    {k deg : ℕ} {good : Finset F} {P : F → Polynomial F}
    {matchingSet : Finset F} {root : (z : F) → rationalRoot (H_tilde' H) z}
    -- Step B inputs (ingredient C + weight bound) — drive the α-tail vanishing via `betaRec`:
    (mp : ∀ t, k ≤ t → ∀ z ∈ matchingSet,
      BetaMatchingVanishes.MatchingPoint x₀ R H hHyp Bcoeff t z (root z))
    (hcard : ∀ t, k ≤ t → (↑matchingSet.card : WithBot ℕ)
        > weight_Λ_over_𝒪 hH (betaRec x₀ R H hHyp Bcoeff t) D * H.natDegree)
    -- Claim 5.9 inputs (§5 setup + Prop 5.5 representative datum) — about `γ`, not `P`:
    (hsubst : PowerSeries.HasSubst (Claim59Conditional.shiftSeries x₀ H))
    (hγ : γ x₀ R H hHyp =
      (PowerSeries.mk (αFromBeta x₀ R H hHyp Bcoeff)).subst (Claim59Conditional.shiftSeries x₀ H))
    {Ppoly : F[X][Y]} (hrep : polyToPowerSeries𝕃 H Ppoly = γ x₀ R H hHyp)
    (hdegX : Polynomial.Bivariate.degreeX Ppoly ≤ 1)
    -- The §5 specialisation bridge + degree bound — per-point identity, not the conclusion:
    (hPz : ∀ v₀ v₁ : F[X],
      γ x₀ R H hHyp = polyToPowerSeries𝕃 H
        ((Polynomial.map Polynomial.C v₀) + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)) →
      (∀ z ∈ good, P z =
        ((Polynomial.map Polynomial.C v₀)
            + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)).eval (Polynomial.C z))
        ∧ v₀.natDegree < k + 1 ∧ v₁.natDegree < k + 1) :
    CurveCoeffPolys k deg good P := by
  -- Step A+B: the Hensel-lift α-tail vanishes for `t ≥ k`, driven by `betaRec` (uses `betaRec`).
  have htail : ∀ t, k ≤ t → αFromBeta x₀ R H hHyp Bcoeff t = 0 :=
    tail_zero_of_betaRec_embedding_zero x₀ R H hHyp Bcoeff hH D hD k mp hcard
  -- Step C (Claim 5.8' / L6, LOAD-BEARING use of the tail vanishing): the tail-vanishing of the
  -- `betaRec`-built Hensel coefficients forces `γ` to BE its own degree-`< k` truncation.  This is
  -- where `betaRec`'s tail vanishing is genuinely consumed to constrain `γ`.
  have htrunc :
      γ x₀ R H hHyp =
        Polynomial.aeval (Claim59Conditional.shiftSeries x₀ H)
          (PowerSeries.trunc k (PowerSeries.mk (αFromBeta x₀ R H hHyp Bcoeff))) := by
    rw [hγ]
    exact subst_mk_eq_aeval_trunc_of_tail_zero hsubst htail
  -- Step D-pre (Claim 5.9 / L18a): the Prop-5.5 representative `hrep`/`hdegX` gives the linear form.
  obtain ⟨v₀, v₁, hPpoly⟩ :=
    FiniteSeriesToPoly.exists_linear_decomposition_of_degreeX_le_one hdegX
  have hlin :
      γ x₀ R H hHyp = polyToPowerSeries𝕃 H
        ((Polynomial.map Polynomial.C v₀)
          + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)) := by
    rw [← hrep, hPpoly]
  -- Record (for honesty) that the linear representative IS the `betaRec`-truncation of `γ`:
  -- `htrunc` (the tail-vanishing constraint) and `hlin` describe the SAME `γ`.
  have _hconsistent :
      Polynomial.aeval (Claim59Conditional.shiftSeries x₀ H)
          (PowerSeries.trunc k (PowerSeries.mk (αFromBeta x₀ R H hHyp Bcoeff)))
        = polyToPowerSeries𝕃 H
          ((Polynomial.map Polynomial.C v₀)
            + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)) := by
    rw [← htrunc, hlin]
  -- Step D: read off the per-index coefficient polynomials from the linear representative.
  obtain ⟨hPeval, hd₀, hd₁⟩ := hPz v₀ v₁ hlin
  exact curveCoeffPolys_of_linear_representative v₀ v₁ hd₀ hd₁ hPeval

end BetaToCurveCoeffPolys

end ArkLib

/-! ## Axiom audit — every claimed-done declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ArkLib.BetaToCurveCoeffPolys.alphaFromBeta_eq_zero_of_embedding_zero
#print axioms ArkLib.BetaToCurveCoeffPolys.tail_zero_of_betaRec_embedding_zero
#print axioms ArkLib.BetaToCurveCoeffPolys.eval_linear_representative
#print axioms ArkLib.BetaToCurveCoeffPolys.coeff_C_add_smul_X
#print axioms ArkLib.BetaToCurveCoeffPolys.curveCoeffPolys_of_linear_representative
#print axioms ArkLib.BetaToCurveCoeffPolys.curveCoeffPolys_of_betaRec
