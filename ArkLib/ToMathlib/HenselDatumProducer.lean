/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.HPzBridge

/-!
# Producing the per-`z` Hensel datum `HPzBridge.HenselDatum` from the §5 standing data

`ArkLib.HPzBridge.hPz_of_henselDatum` (`ArkLib/ToMathlib/HPzBridge.lean`) — wired into the keystone
by `KeystoneAssembly.section5DataFin_of_producers` — consumes, for every linear representative
`(v₀, v₁)` consistent with the `γ`-hypothesis, the per-`z` **Hensel root datum**
`HPzBridge.HenselDatum u P v₀ v₁`.  That datum bundles, *for every good curve parameter*
`z ∈ RS_goodCoeffsCurve u δ`:

* the per-`z` matching polynomial `f z : (PowerSeries F)[Y]` (the Guruswami–Sudan factor specialised
  at `z`, lifted to the coordinate power-series ring `F⟦X⟧`);
* the per-`z` approximation `a₀ z : F⟦X⟧` (the §5 degree-`0` simple root `α₀`);
* the two **root** facts `(f z).IsRoot ↑(P z)` and `(f z).IsRoot ↑(lift.eval (C z))`;
* the two **congruences** `↑(P z) ≡ a₀ z` and `↑(lift.eval (C z)) ≡ a₀ z` modulo `X`;
* the **unit-derivative** `IsUnit ((f z).derivative.eval (a₀ z))` — separability of the matching
  coordinate.

This file **PRODUCES** that datum.  The mathematical content delivered here is the
*separability ⟹ unit-derivative* step of [BCIKS20] App-A §5.2.6: at a simple root, the derivative of
a separable polynomial is a unit.  We prove it over `F⟦X⟧` and feed it into the datum, so the
unit-derivative field is **constructed**, not assumed.

## What is derived vs. what is the isolated §5 residual

The genuinely irreducible per-`z` inputs are the §5 regime data that define the *good set* and the
matching structure — root membership and the Hensel congruence.  They are isolated as the smallest
explicit hypothesis, a per-`z` bundle `SepHenselInput`, which carries:

* `f`, `a₀`              — the matching polynomial and approximation (data);
* `hProot`, `hQroot`    — the two roots (the §5 GS divisibility, `MatchingExtractor`);
* `hPapprox`, `hQapprox` — the two Hensel congruences (the §5 closeness/approximation data);
* `hsep`                — per-`z` **separability** of the matching polynomial `f z` (the `hsep`
                          graph condition of `BCIKS20AppendixA.ClaimA2.Hypotheses`, transported to
                          the specialised matching polynomial).

`SepHenselInput` does **not** carry the unit-derivative.  The producer
`henselDatum_of_sepInput` constructs it: the approximation `a₀ z` is an approximate root of `f z`
(`f z` evaluated at `a₀ z` lies in `span {X}` — derived from `hProot z` and `hPapprox z`,
`approxRoot_of_isRoot_of_congr`), and at an approximate root of a *separable* polynomial the
derivative is a unit (`isUnit_derivative_eval_of_separable`).  Thus `hderiv` is genuinely *produced*
from `hsep`, not posited.

## The two atomic derivations (kernel-checked)

* `eval_sub_mem_span_X_of_congr` — `a ≡ b mod X ⟹ f.eval a ≡ f.eval b mod X` (`sub_dvd_eval_sub`).
* `approxRoot_of_isRoot_of_congr` — from `f.IsRoot ↑Pz` and `↑Pz ≡ a₀ mod X`, the approximate-root
  fact `f.eval a₀ ∈ span {X}`.
* `isUnit_derivative_eval_of_separable` — from `f.Separable` and `f.eval a₀ ∈ span {X}` (an
  approximate root), the **unit derivative** `IsUnit (f'.eval a₀)`, via the Bézout identity of
  separability evaluated at `a₀` and `PowerSeries.isUnit_iff_constantCoeff`.

## The deliverables

* `henselDatum_of_sepInput`   — `SepHenselInput → HPzBridge.HenselDatum` (the producer).
* `hPz_of_sepHenselInput`     — end-to-end: per-`(v₀, v₁)` `SepHenselInput` + degree bounds ⟹ the
  full `hPz` field, via `HPzBridge.hPz_of_henselDatum`.
* `henselDatum_of_matchingDvd_and_sep` — the `MatchingExtractor`-route variant: the two root facts
  are supplied as the GS matching-factor divisibilities `(X − C ↑·) ∣ f z` and converted to roots by
  `Polynomial.dvd_iff_isRoot`, the rest as in `SepHenselInput`.  This records that the root fields
  are exactly the per-`z` GS factor divisibility the bricks `MatchingExtractor` /
  `MultiplicityDatum` deliver, now over the coordinate power-series ring.

Everything is kernel-clean — `#print axioms` at the bottom rests only on
`propext / Classical.choice / Quot.sound`.

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon Codes*,
  §5 (list-decoding agreement chain), §6.2 (Theorem 6.2), Appendix A §5.2.6 (Hensel uniqueness
  `π_z(γ) = P_z`, separable simple root).
-/

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2
open ProximityGap Code ReedSolomon NNReal
open scoped BigOperators

namespace ArkLib

namespace HenselDatumProducer

/-! ## Atomic derivation 1 — congruence is preserved by polynomial evaluation -/

variable {F : Type} [Field F]

/-- If `a ≡ b` modulo `X` (their difference lies in `span {X}`), then `f.eval a ≡ f.eval b` modulo
`X` for any `f : (F⟦X⟧)[Y]`.  `a − b ∣ f.eval a − f.eval b` (`sub_dvd_eval_sub`), and `X ∣ a − b`, so
`X ∣ f.eval a − f.eval b`. -/
theorem eval_sub_mem_span_X_of_congr (f : Polynomial (PowerSeries F)) {a b : PowerSeries F}
    (h : a - b ∈ Ideal.span {(PowerSeries.X : PowerSeries F)}) :
    f.eval a - f.eval b ∈ Ideal.span {(PowerSeries.X : PowerSeries F)} := by
  rw [Ideal.mem_span_singleton] at h ⊢
  exact h.trans (Polynomial.sub_dvd_eval_sub a b f)

/-- **The approximation is an approximate root.**  From an exact root `f.IsRoot r` and the
congruence `r ≡ a₀ mod X`, the approximation `a₀` is an *approximate* root of `f`:
`f.eval a₀ ∈ span {X}`.  (This is what an order-`0` Hensel approximation means.) -/
theorem approxRoot_of_isRoot_of_congr (f : Polynomial (PowerSeries F)) {r a₀ : PowerSeries F}
    (hroot : f.IsRoot r)
    (hcongr : r - a₀ ∈ Ideal.span {(PowerSeries.X : PowerSeries F)}) :
    f.eval a₀ ∈ Ideal.span {(PowerSeries.X : PowerSeries F)} := by
  -- `f.eval r − f.eval a₀ ∈ span {X}` and `f.eval r = 0`, so `−f.eval a₀ ∈ span {X}`.
  have hsub : f.eval r - f.eval a₀ ∈ Ideal.span {(PowerSeries.X : PowerSeries F)} :=
    eval_sub_mem_span_X_of_congr f hcongr
  rw [Polynomial.IsRoot.def] at hroot
  rw [hroot, zero_sub] at hsub
  -- `−(f.eval a₀) ∈ span {X} ⟹ f.eval a₀ ∈ span {X}`.
  simpa using (Ideal.neg_mem_iff _).mp hsub

/-! ## Atomic derivation 2 — separability ⟹ unit derivative at an approximate root

This is the genuine [BCIKS20] App-A §5.2.6 *simple root* fact: at an approximate root `a₀` of a
**separable** polynomial `f` over the local ring `F⟦X⟧`, the derivative `f'(a₀)` is a unit.
Separability gives a Bézout identity `u·f + v·f' = 1`; evaluating at `a₀` and reading the constant
coefficient (the maximal ideal is `span {X}`, killing `f.eval a₀`) leaves `f'(a₀)`'s constant
coefficient a unit, hence `f'(a₀)` is a unit (`PowerSeries.isUnit_iff_constantCoeff`). -/

/-- **Separability ⟹ unit derivative (the produced `hderiv` field).**  If `f : (F⟦X⟧)[Y]` is
separable and `a₀` is an approximate root (`f.eval a₀ ∈ span {X}`), then the derivative `f'(a₀)` is a
unit.  This is the App-A §5.2.6 simple-root datum, derived from separability — *not* assumed. -/
theorem isUnit_derivative_eval_of_separable (f : Polynomial (PowerSeries F))
    {a₀ : PowerSeries F} (hsep : f.Separable)
    (h0 : f.eval a₀ ∈ Ideal.span {(PowerSeries.X : PowerSeries F)}) :
    IsUnit (f.derivative.eval a₀) := by
  obtain ⟨u, v, huv⟩ := hsep
  -- Bézout identity `u·f + v·f' = 1` evaluated at `a₀`.
  have heval : (u.eval a₀) * (f.eval a₀) + (v.eval a₀) * (f.derivative.eval a₀) = 1 := by
    have := congrArg (Polynomial.eval a₀) huv
    simpa using this
  rw [PowerSeries.isUnit_iff_constantCoeff]
  -- `f.eval a₀` has zero constant coefficient (it lies in `span {X}`).
  have hcc0 : PowerSeries.constantCoeff (f.eval a₀) = 0 := by
    rw [← PowerSeries.X_dvd_iff, ← Ideal.mem_span_singleton]
    exact h0
  -- Read off the constant coefficient of the Bézout identity.
  have hcc := congrArg (PowerSeries.constantCoeff (R := F)) heval
  simp only [map_add, map_mul, map_one, hcc0, mul_zero, zero_add] at hcc
  -- `cc(v(a₀)) · cc(f'(a₀)) = 1`, so `cc(f'(a₀))` is a unit.
  exact IsUnit.of_mul_eq_one _ (by rw [mul_comm]; exact hcc)

/-- **`hderiv` from separability + a root + a congruence (the form the datum needs).**  Combines the
two derivations: `r` an exact root and `r ≡ a₀ mod X` make `a₀` an approximate root, at which
separability of `f` forces `f'(a₀)` to be a unit. -/
theorem isUnit_derivative_of_separable_of_isRoot_of_congr (f : Polynomial (PowerSeries F))
    {r a₀ : PowerSeries F} (hsep : f.Separable) (hroot : f.IsRoot r)
    (hcongr : r - a₀ ∈ Ideal.span {(PowerSeries.X : PowerSeries F)}) :
    IsUnit (f.derivative.eval a₀) :=
  isUnit_derivative_eval_of_separable f hsep (approxRoot_of_isRoot_of_congr f hroot hcongr)

end HenselDatumProducer

/-! ## The §5 per-`z` residual bundle and the `HenselDatum` producer

We carry the full env of `HPzBridge.HenselDatum` (`ι`, `F`, the curve/decoding data). -/

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

namespace HenselDatumProducer

/-- **The isolated §5 per-`z` residual** for a given linear representative `(v₀, v₁)`.

This is the smallest explicit input from which `HPzBridge.HenselDatum` is *produced*: it is the
`HenselDatum` minus the unit-derivative, *plus* per-`z` separability of the matching polynomial.  The
unit-derivative is then derived (`henselDatum_of_sepInput`), so this bundle is strictly weaker — it
never mentions `IsUnit`.

Every field is a genuine §5 regime datum (none is the per-`z` polynomial identity `hPz` derives):

* `f`, `a₀`             — the GS matching polynomial specialised at `z` over `F⟦X⟧`, and the §5
                          degree-`0` approximation `α₀` (data);
* `hProot`, `hQroot`   — both `↑(P z)` and `↑(lift.eval (C z))` are roots of `f z` (the §5 GS
                          factor divisibility, `MatchingExtractor.matchingFactor_dvd_…`, over the
                          coordinate power-series ring);
* `hPapprox`, `hQapprox` — both reduce mod `X` to `a₀ z` (the §5 Hensel congruences);
* `hsep`               — `f z` is separable (the `hsep` graph condition of
                          `BCIKS20AppendixA.ClaimA2.Hypotheses`, transported to the specialised
                          matching polynomial — separability of `R(x₀, ·)` is preserved by the §5
                          specialisation). -/
structure SepHenselInput {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (u : WordStack F (Fin (k + 1)) ι) (P : F → Polynomial F) (v₀ v₁ : F[X]) : Type where
  /-- per-`z` matching polynomial over `F⟦X⟧`. -/
  f : F → Polynomial (PowerSeries F)
  /-- per-`z` common approximation. -/
  a₀ : F → PowerSeries F
  /-- `↑(P z)` is a root of the matching polynomial. -/
  hProot : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
    (f z).IsRoot ((P z : PowerSeries F))
  /-- `↑(lift.eval (C z))` is a root of the matching polynomial. -/
  hQroot : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
    (f z).IsRoot
      ((((Polynomial.map Polynomial.C v₀)
          + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)).eval
            (Polynomial.C z) : F[X]) : PowerSeries F)
  /-- `↑(P z)` reduces to the approximation mod `X`. -/
  hPapprox : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
    (P z : PowerSeries F) - a₀ z ∈ Ideal.span {(PowerSeries.X : PowerSeries F)}
  /-- `↑(lift.eval (C z))` reduces to the approximation mod `X`. -/
  hQapprox : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
    ((((Polynomial.map Polynomial.C v₀)
        + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)).eval
          (Polynomial.C z) : F[X]) : PowerSeries F) - a₀ z
      ∈ Ideal.span {(PowerSeries.X : PowerSeries F)}
  /-- per-`z` separability of the matching polynomial (the §5 `hsep` graph condition). -/
  hsep : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
    (f z).Separable

/-- **THE PRODUCER.**  From the isolated §5 residual `SepHenselInput`, produce the per-`z` Hensel
root datum `HPzBridge.HenselDatum` consumed by `HPzBridge.hPz_of_henselDatum`.

The `f`/`a₀` data and the four root/congruence facts are passed through; the **unit-derivative
field is constructed** from per-`z` separability via
`isUnit_derivative_of_separable_of_isRoot_of_congr` (`hsep z` + `hProot z` + `hPapprox z`). -/
def henselDatum_of_sepInput {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F} {v₀ v₁ : F[X]}
    (d : SepHenselInput (k := k) (deg := deg) (domain := domain) (δ := δ) u P v₀ v₁) :
    HPzBridge.HenselDatum (k := k) (deg := deg) (domain := domain) (δ := δ) u P v₀ v₁ where
  f := d.f
  a₀ := d.a₀
  hProot := d.hProot
  hQroot := d.hQroot
  hPapprox := d.hPapprox
  hQapprox := d.hQapprox
  hderiv := fun z hz =>
    isUnit_derivative_of_separable_of_isRoot_of_congr (d.f z) (d.hsep z hz)
      (d.hProot z hz) (d.hPapprox z hz)

end HenselDatumProducer

/-! ## End-to-end: feeding `hPz` directly from the §5 residual -/

/-- **`hPz` from the §5 per-`z` residual (end-to-end).**  For every linear representative `(v₀, v₁)`
consistent with the `γ`-hypothesis, the §5 residual `SepHenselInput` together with the degree bounds
yields the full `hPz` field — the producer `henselDatum_of_sepInput` builds the `HenselDatum`, and
`HPzBridge.hPz_of_henselDatum` derives the per-`z` identity from it (via Hensel uniqueness) and
attaches the degree bounds.

This is exactly the input shape `KeystoneAssembly.section5DataFin_of_producers` threads as `hHensel`
/ `hdeg`, with the unit-derivative obligation discharged from separability rather than assumed. -/
theorem hPz_of_sepHenselInput {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    {hHyp : BCIKS20AppendixA.ClaimA2.Hypotheses x₀ R H}
    {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F}
    (hInput : ∀ v₀ v₁ : F[X],
      BCIKS20AppendixA.ClaimA2.γ x₀ R H hHyp = BCIKS20AppendixA.polyToPowerSeries𝕃 H
        ((Polynomial.map Polynomial.C v₀)
          + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)) →
      HenselDatumProducer.SepHenselInput
        (k := k) (deg := deg) (domain := domain) (δ := δ) u P v₀ v₁)
    (hdeg : ∀ v₀ v₁ : F[X],
      BCIKS20AppendixA.ClaimA2.γ x₀ R H hHyp = BCIKS20AppendixA.polyToPowerSeries𝕃 H
        ((Polynomial.map Polynomial.C v₀)
          + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)) →
      v₀.natDegree < k + 1 ∧ v₁.natDegree < k + 1) :
    ∀ v₀ v₁ : F[X],
      BCIKS20AppendixA.ClaimA2.γ x₀ R H hHyp = BCIKS20AppendixA.polyToPowerSeries𝕃 H
        ((Polynomial.map Polynomial.C v₀)
          + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)) →
      (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
        P z = ((Polynomial.map Polynomial.C v₀)
            + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)).eval
            (Polynomial.C z))
        ∧ v₀.natDegree < k + 1 ∧ v₁.natDegree < k + 1 :=
  HPzBridge.hPz_of_henselDatum
    (fun v₀ v₁ hlin => HenselDatumProducer.henselDatum_of_sepInput (hInput v₀ v₁ hlin)) hdeg

namespace HenselDatumProducer

/-! ## The `MatchingExtractor` route: roots from the GS matching-factor divisibility

The two root facts of `SepHenselInput` are, in §5, the GS matching-factor divisibilities
`(Y − ↑(P z)) ∣ f z` and `(Y − ↑(lift.eval (C z))) ∣ f z` (`MatchingExtractor.matchesGraph_iff_dvd`
/ `MatchingExtractor.matchingFactor_dvd_of_orderM_and_count`), here over the coordinate power-series
ring `F⟦X⟧`.  `Polynomial.dvd_iff_isRoot` turns each divisibility into the corresponding `IsRoot`
fact, so the producer can be fed directly from the divisibility shape the bricks deliver. -/

/-- **The producer, `MatchingExtractor`/divisibility route.**  Identical to `henselDatum_of_sepInput`
except the two root facts arrive as the GS matching-factor divisibilities
`(X − C ↑(P z)) ∣ f z` and `(X − C ↑(lift.eval (C z))) ∣ f z` (`Polynomial.X` is the outer variable
`Y`); each is converted to an `IsRoot` by `Polynomial.dvd_iff_isRoot`, and the unit-derivative is
again produced from separability.  This is the shape the bricks
`MatchingExtractor.matchingFactor_dvd_of_orderM_and_count` (with the per-`z` multiplicity from
`MultiplicityDatum.hord_of_rootMultiplicity_ge`) deliver, transported to `F⟦X⟧`. -/
def henselDatum_of_matchingDvd_and_sep {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F} {v₀ v₁ : F[X]}
    (f : F → Polynomial (PowerSeries F)) (a₀ : F → PowerSeries F)
    (hPdvd : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      (Polynomial.X - Polynomial.C ((P z : PowerSeries F))) ∣ f z)
    (hQdvd : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      (Polynomial.X - Polynomial.C
        ((((Polynomial.map Polynomial.C v₀)
            + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)).eval
              (Polynomial.C z) : F[X]) : PowerSeries F)) ∣ f z)
    (hPapprox : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      (P z : PowerSeries F) - a₀ z ∈ Ideal.span {(PowerSeries.X : PowerSeries F)})
    (hQapprox : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      ((((Polynomial.map Polynomial.C v₀)
          + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)).eval
            (Polynomial.C z) : F[X]) : PowerSeries F) - a₀ z
        ∈ Ideal.span {(PowerSeries.X : PowerSeries F)})
    (hsep : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      (f z).Separable) :
    HPzBridge.HenselDatum (k := k) (deg := deg) (domain := domain) (δ := δ) u P v₀ v₁ :=
  henselDatum_of_sepInput
    { f := f
      a₀ := a₀
      hProot := fun z hz => (Polynomial.dvd_iff_isRoot).mp (hPdvd z hz)
      hQroot := fun z hz => (Polynomial.dvd_iff_isRoot).mp (hQdvd z hz)
      hPapprox := hPapprox
      hQapprox := hQapprox
      hsep := hsep }

end HenselDatumProducer

end ArkLib

/-! ## Axiom audit — must rest only on `[propext, Classical.choice, Quot.sound]`. -/
#print axioms ArkLib.HenselDatumProducer.eval_sub_mem_span_X_of_congr
#print axioms ArkLib.HenselDatumProducer.approxRoot_of_isRoot_of_congr
#print axioms ArkLib.HenselDatumProducer.isUnit_derivative_eval_of_separable
#print axioms ArkLib.HenselDatumProducer.isUnit_derivative_of_separable_of_isRoot_of_congr
#print axioms ArkLib.HenselDatumProducer.henselDatum_of_sepInput
#print axioms ArkLib.hPz_of_sepHenselInput
#print axioms ArkLib.HenselDatumProducer.henselDatum_of_matchingDvd_and_sep
