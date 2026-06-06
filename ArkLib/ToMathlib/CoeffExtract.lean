/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ToMathlib.BetaMatchingVanishes

set_option linter.style.longLine false

/-!
# The `(X−x₀)^t` coefficient extraction discharging `coeffExtract` (brick **L12**)

This file proves the residual **coefficient-extraction** step of brick L12 (the `coeffExtract` field
of `BetaMatchingVanishes.MatchingPoint`).  Once Hensel uniqueness pins the two power series equal
```
aβ  =  aP          (the equality "π_z(γ) = P_z" of App-A §5.2.6, from `hensel_root_unique`)
```
reading off the `(X−x₀)^t` coefficient and threading `betaRec`'s defining relation to `α`
(`α_t = embedding(betaRec … t) / (W^{t+1} · ξ^{e_t})`, π_z-specialized) yields the scalar vanishing
`π_z z root (betaRec … t) = 0`.

## The genuine content, isolated as the smallest explicit hypotheses

The §5.2.6 reduction "`π_z(γ) = P_z` ⟹ `π_z(α_t) = 0` ⟹ `π_z(β_t) = 0`" rests on exactly three facts
about the *specialized* (`π_z`-image) data — none of which is a `sorry`/`axiom`:

* `hαβ` — the **`α_t`-identity, π_z-specialized**: the `(X−x₀)^t` coefficient of the specialization
  `aβ` of `γ` is `π_z(α_t)`, which by `betaRec`'s defining relation
  `α_t = embedding(betaRec … t) / (W^{t+1} · ξ^{e_t})` reads as
  `coeff t aβ = π_z(betaRec … t) / (w ^ (t+1) * x ^ e)`, where `w = π_z(W)`, `x = π_z(ξ)`.
* `haP` — the **proximate root reads zero** at the `(X−x₀)^t` slot: `coeff t aP = 0` (App-A §5.2.6;
  for `t` above the truncation index the proximate-root series carries no `(X−x₀)^t` term).
* `hw`, `hx` — **`π_z(W), π_z(ξ) ≠ 0`** (the unit specializations).

Given these, the proof is *pure coefficient extraction + field algebra*:
`aβ = aP` ⟹ `coeff t aβ = coeff t aP = 0` ⟹ `π_z(betaRec … t) / (w^{t+1} · x^e) = 0` ⟹ (denominator a
unit, field) `π_z(betaRec … t) = 0`.  No power-series `subst` junk is needed — we work with
`PowerSeries.coeff t` directly (per note F1: over a field the `(X−x₀)`-shift `subst` must not be
`subst`-collapsed; reading a single coefficient sidesteps it entirely).

## What this file delivers

* `coeff_extract_scalar` — the **field-level core**: from `coeff t aβ = s / D` (with `s` the target
  scalar, `D ≠ 0` the unit denominator), `coeff t aP = 0`, and `aβ = aP`, conclude `s = 0`.  This is
  the entire mathematical content, stated over a bare field with no ArkLib baggage.
* `coeff_extract_betaRec` — the **`MatchingPoint`-shaped** version: with `w = π_z(W)`, `x = π_z(ξ)`,
  the per-point bridging facts `hαβ`/`haP`/`hw`/`hx`, it produces
  `aβ = aP → (π_z z root) (betaRec … t) = 0` — *exactly the type of the `coeffExtract` field*.
* `MatchingPoint.mk_coeffExtract` — a wrapper turning the bridging facts into the `coeffExtract`
  function, so a `MatchingPoint` can be assembled and `betaRec_matchingVanishes` fires without any
  residual.

Everything is kernel-clean (`#print axioms` at the bottom; only
`propext / Classical.choice / Quot.sound`).
-/

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2 PowerSeries

namespace ArkLib

namespace CoeffExtract

/-! ### The field-level coefficient-extraction core

The whole §5.2.6 step, distilled to its arithmetic essence over a bare field `k`.  Two power series
`aβ`, `aP` are equal; the `t`-th coefficient of `aβ` is a scalar `s` divided by a *nonzero*
denominator `D` (the `W^{t+1}·ξ^{e}` factor, π_z-specialized — nonzero because `π_z(W), π_z(ξ)` are);
the `t`-th coefficient of `aP` is `0`.  Then `s = 0`.

Reading off one coefficient is the *correct* way to extract — it never touches the `(X−x₀)`-shift
`subst` that would otherwise need delicate bookkeeping (note F1). -/

/-- **Coefficient-extraction core (over a field).**  If two power series agree, the `t`-th
coefficient of one is `s / D` with `D ≠ 0`, and the `t`-th coefficient of the other is `0`, then
`s = 0`.

This is `betaRec`'s `(X−x₀)^t` extraction stripped to field arithmetic: `aβ = aP` forces the
`t`-th coefficients equal, the right one is `0`, so `s / D = 0`; `D ≠ 0` over a field gives `s = 0`. -/
theorem coeff_extract_scalar {k : Type*} [Field k]
    {aβ aP : PowerSeries k} (t : ℕ) {s D : k}
    (hαβ : PowerSeries.coeff t aβ = s / D) (hD : D ≠ 0)
    (haP : PowerSeries.coeff t aP = 0)
    (heq : aβ = aP) :
    s = 0 := by
  -- Read off the `t`-th coefficient of the power-series equality `aβ = aP`.
  have hcoeff : PowerSeries.coeff t aβ = PowerSeries.coeff t aP := by rw [heq]
  -- Combine with the two bridging readings: `s / D = 0`.
  rw [hαβ, haP] at hcoeff
  -- `D ≠ 0` over a field, so the numerator vanishes.
  exact (div_eq_zero_iff.mp hcoeff).resolve_right hD

/-- A convenience repackaging: the unit denominator `D` written as a product
`w ^ a * x ^ e` of two nonzero scalars (the shape `W^{t+1} · ξ^{e_t}` takes after π_z).  The
product of nonzero field elements is nonzero, so `coeff_extract_scalar` applies. -/
theorem coeff_extract_scalar_prod {k : Type*} [Field k]
    {aβ aP : PowerSeries k} (t : ℕ) {s w x : k} (a e : ℕ)
    (hαβ : PowerSeries.coeff t aβ = s / (w ^ a * x ^ e))
    (hw : w ≠ 0) (hx : x ≠ 0)
    (haP : PowerSeries.coeff t aP = 0)
    (heq : aβ = aP) :
    s = 0 :=
  coeff_extract_scalar t hαβ (mul_ne_zero (pow_ne_zero a hw) (pow_ne_zero e hx)) haP heq

end CoeffExtract

namespace BetaMatchingVanishes

variable {F : Type} [Field F]

/-! ### The `MatchingPoint`-shaped coefficient extraction

We now produce exactly the function the `coeffExtract` field of `MatchingPoint` asks for:
`aβ = aP → (π_z z root) (betaRec … t) = 0`.  The bridging facts are the π_z-specialized form of
`betaRec`'s defining relation to `α` and of the proximate-root reading; they are supplied as
explicit hypotheses (the genuine L12 content, never a `sorry`). -/

variable {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]}
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] {hHyp : Hypotheses x₀ R H}
    {Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H} {t : ℕ}
    {z : F} {root : rationalRoot (H_tilde' H) z}

/-- **The `(X−x₀)^t` coefficient extraction for `betaRec` (the `coeffExtract` content).**

Given:
* `aβ`, `aP` the two specialized power series (`π_z(γ)` and `P_z`) at the matching point `z`;
* `hαβ` — the π_z-specialized `α_t`-identity: the `(X−x₀)^t` coefficient of `aβ` equals
  `(π_z z root) (betaRec … t)` divided by the specialized prefactor `w ^ a * x ^ e`
  (where `w = (π_z z root)(W_𝒪 H)`, `x = (π_z z root)(ξ …)`, `a = t+1`, `e = e_t`);
* `haP` — the proximate root reads zero at index `t`: `coeff t aP = 0`;
* `hw`, `hx` — `π_z(W), π_z(ξ) ≠ 0`,

the Hensel equality `aβ = aP` yields the scalar vanishing `(π_z z root) (betaRec … t) = 0`.

This is precisely a term of the `coeffExtract` field's type
`aβ = aP → (π_z z root) (betaRec x₀ R H hHyp Bcoeff t) = 0`. -/
theorem coeff_extract_betaRec
    {aβ aP : PowerSeries F} {w x : F} {a e : ℕ}
    (hαβ : PowerSeries.coeff t aβ =
        (π_z z root) (betaRec x₀ R H hHyp Bcoeff t) / (w ^ a * x ^ e))
    (hw : w ≠ 0) (hx : x ≠ 0)
    (haP : PowerSeries.coeff t aP = 0) :
    aβ = aP → (π_z z root) (betaRec x₀ R H hHyp Bcoeff t) = 0 :=
  fun heq => CoeffExtract.coeff_extract_scalar_prod t a e hαβ hw hx haP heq

/-- **Assemble a `MatchingPoint`'s `coeffExtract` from the bridging facts.**

A wrapper exposing `coeff_extract_betaRec` as the `coeffExtract` function directly, so that — given
the §5 geometry's Hensel data (`f`, `aβ`, `aP`, `a₀`, the root/congruence/unit facts) *and* the
π_z-specialized bridging facts — a `MatchingPoint` can be constructed with **no residual
hypothesis**: `coeffExtract := MatchingPoint.mk_coeffExtract …`.  Then
`BetaMatchingVanishes.betaRec_matchingVanishes` fires. -/
theorem MatchingPoint.mk_coeffExtract
    {aβ aP : PowerSeries F} {w x : F} {a e : ℕ}
    (hαβ : PowerSeries.coeff t aβ =
        (π_z z root) (betaRec x₀ R H hHyp Bcoeff t) / (w ^ a * x ^ e))
    (hw : w ≠ 0) (hx : x ≠ 0)
    (haP : PowerSeries.coeff t aP = 0) :
    aβ = aP → (π_z z root) (betaRec x₀ R H hHyp Bcoeff t) = 0 :=
  coeff_extract_betaRec hαβ hw hx haP

/-- **Self-contained per-point conclusion via the bridging facts.**  Combines Hensel uniqueness
(`hensel_root_unique`, supplied here as the equality `heq : aβ = aP`) with the coefficient
extraction, giving `(π_z z root) (betaRec … t) = 0`.  This is the shape `MatchingPoint.pi_z_eq_zero`
reaches once `coeffExtract` is realized by `coeff_extract_betaRec`. -/
theorem pi_z_betaRec_eq_zero_of_bridge
    {aβ aP : PowerSeries F} {w x : F} {a e : ℕ}
    (hαβ : PowerSeries.coeff t aβ =
        (π_z z root) (betaRec x₀ R H hHyp Bcoeff t) / (w ^ a * x ^ e))
    (hw : w ≠ 0) (hx : x ≠ 0)
    (haP : PowerSeries.coeff t aP = 0)
    (heq : aβ = aP) :
    (π_z z root) (betaRec x₀ R H hHyp Bcoeff t) = 0 :=
  coeff_extract_betaRec hαβ hw hx haP heq

end BetaMatchingVanishes

end ArkLib

-- Axiom audit: every claimed-done declaration must rest only on
-- `[propext, Classical.choice, Quot.sound]`.
#print axioms ArkLib.CoeffExtract.coeff_extract_scalar
#print axioms ArkLib.CoeffExtract.coeff_extract_scalar_prod
#print axioms ArkLib.BetaMatchingVanishes.coeff_extract_betaRec
#print axioms ArkLib.BetaMatchingVanishes.MatchingPoint.mk_coeffExtract
#print axioms ArkLib.BetaMatchingVanishes.pi_z_betaRec_eq_zero_of_bridge
