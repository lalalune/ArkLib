/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.MpProducer
import ArkLib.ToMathlib.HenselDatumProducer
import ArkLib.ToMathlib.MatchingExtractor

-- Documentation-heavy file (BCIKS §5 / App-A.4 prose in the docstrings); the long-line style
-- linter is disabled locally, matching the sibling supply files.
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Supplying the `mpFin` field of `BetaCurveInputFin` — the ingredient-C per-point matching geometry

The finite-range §5 bundle `KeystoneStrictResidual.BetaCurveInputFin`
(`ArkLib/ToMathlib/KeystoneStrictResidual.lean`), consumed by the keystone front door
`correlatedAgreement_affine_curves_johnson_of_betaRecFin_strict`, carries the per-point matching
datum over the *finite* counting range `k ≤ t ≤ T`:

```
mpFin : ∀ t, k ≤ t → t ≤ T → ∀ z ∈ matchingSet,
  BetaMatchingVanishes.MatchingPoint x₀ R H hHyp Bcoeff t z (root z)
```

`MpProducer.mkMatchingPoint` (`MpProducer.lean`) already reduces one `MatchingPoint` to **13 explicit
per-point inputs**: the nine §5 root-geometry facts (`f`, `aβ`, `aP`, `a₀`, the two `IsRoot`, the two
mod-`(X−x₀)` congruences, the unit-derivative `hderiv`) plus the four π_z-specialised bridging facts
(`hαβ`/`hw`/`hx`/`haP_coeff`), with `coeffExtract` discharged in tree.  This file performs the **next
reduction**, exactly mirroring `HenselDatumProducer` (which does the same for the `hPz` branch):

1. **`hderiv` is *derived*, not assumed.**  The simple-root unit-derivative
   `IsUnit (f.derivative.eval a₀)` is the App-A §5.2.6 separability ⟹ simple-root fact.  It is
   produced from per-point **separability** of the matching polynomial `f` (the `hsep` graph
   condition of `BCIKS20AppendixA.ClaimA2.Hypotheses`, transported to the specialised matching
   polynomial — `Hypotheses.separable_evalX`, available in the GS-factor `Bundle`'s `hHyp`) plus the
   root/congruence facts already on hand, via
   `HenselDatumProducer.isUnit_derivative_of_separable_of_isRoot_of_congr`.  So the nine root-geometry
   fields are cut to **eight + separability**, never positing `IsUnit`.

2. **The proximate root `aP = P_z` is a root of the matching polynomial** — this is exactly the
   Gap-B keystone `Q_vanishes_on_close_codeword_graph` (`Agreement.lean`, PROVEN) / the
   `MatchingExtractor` brick output `(Y − P_z) ∣ Q_z`, transported to the coordinate power-series ring
   `F⟦X⟧`: the GS factorisation supplies `haP_root` from the divisibility `(Y − aP) ∣ f` via
   `Polynomial.dvd_iff_isRoot`.  We expose the divisibility route so the root field is fed directly
   from the brick's output, not assumed.

## The `t`-(in)dependence of `MatchingPoint`, and why one geometry serves all `t`

`MatchingPoint x₀ R H hHyp Bcoeff t z root` depends on `t` only through

* the conclusion of `coeffExtract` (`(π_z z root)(betaRec … t) = 0`), and
* the two `t`-indexed bridging readings `hαβ` (`coeff t aβ = …`) and `haP_coeff` (`coeff t aP = 0`).

The nine root-geometry fields — the matching polynomial `f`, the two roots `aβ = π_z(γ)` and
`aP = P_z`, the approximation `a₀ = α₀`, the two `IsRoot`/congruence facts and the unit derivative —
are properties of the **matching place `z`**, *independent of the truncation index `t`*.  So a single
per-`z` geometry bundle (`PlaceGeometry` below) serves *every* `t ∈ [k, T]`; only the scalar
coefficient readings vary with `t`.  This is why `mpFin_of_close_word` consumes one geometry producer
(per `z`) and a per-`(t, z)` bridging producer, and threads them uniformly across the finite range.

## What this file delivers

* `PlaceGeometry` — the `t`-uniform per-`z` matching-place geometry **without** the unit derivative:
  `f`, `aβ`, `aP`, `a₀`, the two roots, the two congruences, and per-place **separability** of `f`.
  This is the smallest honest §5 input (it never mentions `IsUnit`).
* `BridgeData` — the per-`(t, z)` π_z-specialised bridging facts (`hαβ`/`hw`/`hx`/`haP_coeff`) that
  carry the L12 `α_t`-identity coefficient reading; `coeffExtract` is discharged from them in tree.
* `mkMatchingPoint_of_graph_vanishing` — from a `PlaceGeometry` (separability ⟹ `hderiv` derived) and
  `BridgeData` at `(t, z)`, produce a `MatchingPoint x₀ R H hHyp Bcoeff t z root`.  The
  `aP`-root field is the GS graph-vanishing / `MatchingExtractor` output; `hderiv` is the produced
  separability datum; only the bridging readings remain as genuine §5 per-point inputs.
* `mpFin_of_close_word` — assemble the exact `mpFin` field
  `∀ t, k ≤ t → t ≤ T → ∀ z ∈ matchingSet, MatchingPoint …` from a per-`z` `PlaceGeometry` producer
  and a per-`(t, z)` `BridgeData` producer (the same place geometry reused at every `t`).
* `mpFin_of_graph_vanishing_dvd` — the `MatchingExtractor`-route convenience: the `aP`-root arrives as
  the GS matching-factor divisibility `(Y − aP) ∣ f`, converted to the root via
  `Polynomial.dvd_iff_isRoot`, recording that the proximate-root membership is exactly the brick's
  Gap-B output.

## Per-hypothesis disposition of `mkMatchingPoint`

| `MatchingPoint` field | disposition |
| --------------------- | ----------- |
| `f`, `aβ`, `aP`, `a₀` | carried (`PlaceGeometry` data — the §5 place geometry) |
| `haβ_root`            | carried (`π_z(γ)` is a root of `f`; the §5 specialisation datum) |
| `haP_root`            | **GS graph-vanishing** (`MatchingExtractor` / `Q_vanishes_on_close_codeword_graph`) |
| `haβ_cong`, `haP_cong`| carried (the §5 mod-`X` Hensel congruences) |
| `hderiv`              | **derived** from `PlaceGeometry.hsep` via `isUnit_derivative_of_separable_of_isRoot_of_congr` |
| `coeffExtract`        | discharged in tree (`MatchingPoint.mk_coeffExtract`, from `BridgeData`) |

Two named residual surfaces remain, both genuine §5 per-point inputs, never the goal and never a
`sorry`: the `PlaceGeometry` (the place's root/congruence/separability geometry) and the `BridgeData`
(the L12 π_z-specialised coefficient readings).

Everything is kernel-clean (`#print axioms` at the bottom; only `propext / Classical.choice /
Quot.sound`).

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon Codes*,
  §5 (list-decoding agreement chain), Appendix A.2 / A.4 (the `W`-power numerator recursion (A.1),
  §5.2.6 matching geometry, Hensel uniqueness `π_z(γ) = P_z`, separable simple root).
-/

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2 ToRatFunc Ideal
open PowerSeries

namespace ArkLib

namespace MpFinSupply

variable {F : Type} [Field F]

variable {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]}
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] {hHyp : Hypotheses x₀ R H}
    {Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H}

/-! ## The `t`-uniform per-place geometry (without the unit derivative)

`PlaceGeometry` carries the genuine §5 root geometry at a single matching place `z` — the matching
polynomial `f`, the two roots `aβ = π_z(γ)` and `aP = P_z`, the approximation `a₀ = α₀`, the two
`IsRoot`/congruence facts, and per-place **separability** of `f` — but *not* the unit derivative,
which `mkMatchingPoint_of_graph_vanishing` produces from `hsep`.  None of these fields mentions `t`:
the place geometry is shared by every truncation index. -/

/-- The `t`-uniform §5 matching-place geometry at a single point `z`, in the smallest shape from
which `mkMatchingPoint_of_graph_vanishing` builds a `MatchingPoint` (it never mentions `IsUnit`; the
unit derivative is *derived* from `hsep`).  Every field is a genuine §5 per-place datum: the matching
polynomial `f`, the specialisation `aβ = π_z(γ)` and proximate root `aP = P_z`, the approximation
`a₀`, the two `IsRoot` facts (`haP_root` being exactly the GS graph-vanishing output), the two
mod-`(X−x₀)` Hensel congruences, and separability of `f`. -/
structure PlaceGeometry (z : F) : Type where
  /-- The matching polynomial `f_z : (F⟦X⟧)[Y]`. -/
  f : Polynomial (PowerSeries F)
  /-- The power-series specialisation `aβ = π_z(γ)` of `betaRec … t` at `z` (`t`-independent). -/
  aβ : PowerSeries F
  /-- The proximate-root power series `aP = P_z` (ingredient B; `t`-independent). -/
  aP : PowerSeries F
  /-- The common degree-0 simple approximation `a₀ = α₀` mod `(X−x₀)`. -/
  a₀ : PowerSeries F
  /-- `aβ = π_z(γ)` is a root of the matching polynomial. -/
  haβ_root : f.IsRoot aβ
  /-- `aP = P_z` is a root of the matching polynomial (the GS graph-vanishing / `MatchingExtractor`
  output, `(Y − aP) ∣ f`, via `Polynomial.dvd_iff_isRoot`). -/
  haP_root : f.IsRoot aP
  /-- `aβ` reduces mod `(X−x₀)` to the approximation `a₀`. -/
  haβ_cong : aβ - a₀ ∈ Ideal.span {(PowerSeries.X : PowerSeries F)}
  /-- `aP` reduces mod `(X−x₀)` to the approximation `a₀`. -/
  haP_cong : aP - a₀ ∈ Ideal.span {(PowerSeries.X : PowerSeries F)}
  /-- Per-place **separability** of the matching polynomial (the §5 `hsep` graph condition,
  transported to the specialised matching polynomial; this is `Hypotheses.separable_evalX` of the
  GS-factor bundle's `hHyp`, specialised at `z`).  The unit-derivative `hderiv` is *derived* from
  this — never assumed. -/
  hsep : f.Separable

/-- The derived simple-root unit derivative `IsUnit (f.derivative.eval a₀)` of a `PlaceGeometry`:
the App-A §5.2.6 separability ⟹ simple-root datum, produced from `hsep` together with the root
`haβ_root` and congruence `haβ_cong` via
`HenselDatumProducer.isUnit_derivative_of_separable_of_isRoot_of_congr`.  This is the field
`mkMatchingPoint_of_graph_vanishing` feeds into `MatchingPoint.hderiv`. -/
theorem PlaceGeometry.hderiv {z : F} (g : PlaceGeometry (F := F) z) :
    IsUnit (g.f.derivative.eval g.a₀) :=
  HenselDatumProducer.isUnit_derivative_of_separable_of_isRoot_of_congr
    g.f g.hsep g.haβ_root g.haβ_cong

/-! ## The per-`(t, z)` π_z-specialised bridging facts

`BridgeData` carries the L12 `α_t`-identity coefficient readings at the truncation index `t` and the
place `z`: the π_z-specialised `coeff t aβ = π_z(betaRec … t) / (w ^ a * x ^ e)`, the unit
nonvanishings `w, x ≠ 0`, and the proximate-root reading `coeff t aP = 0`.  These are exactly the
inputs `MatchingPoint.mk_coeffExtract` (`CoeffExtract.lean`) discharges `coeffExtract` from. -/

/-- The per-`(t, z)` π_z-specialised bridging facts feeding the in-tree `coeffExtract` discharge.
`aβ`, `aP` are the place's two power series (matching the `PlaceGeometry`'s `aβ`, `aP`): the `(X−x₀)^t`
coefficient of `aβ` reads `π_z(betaRec … t)` over the specialised prefactor `w ^ a * x ^ e`
(`w = π_z(W) ≠ 0`, `x = π_z(ξ) ≠ 0`), and the proximate root reads zero at index `t`. -/
structure BridgeData (t : ℕ) (z : F) (root : rationalRoot (H_tilde' H) z)
    (aβ aP : PowerSeries F) : Type where
  /-- The π_z-specialised `α_t`-identity exponents. -/
  w : F
  /-- The π_z-specialised `α_t`-identity exponent base for `ξ`. -/
  x : F
  /-- The `W`-power exponent (`a = t + 1`). -/
  a : ℕ
  /-- The `ξ`-power exponent (`e = e_t`). -/
  e : ℕ
  /-- The π_z-specialised `α_t`-identity coefficient reading. -/
  hαβ : PowerSeries.coeff t aβ =
    (π_z z root) (betaRec x₀ R H hHyp Bcoeff t) / (w ^ a * x ^ e)
  /-- `w = π_z(W) ≠ 0`. -/
  hw : w ≠ 0
  /-- `x = π_z(ξ) ≠ 0`. -/
  hx : x ≠ 0
  /-- The proximate root reads zero at index `t`. -/
  haP_coeff : PowerSeries.coeff t aP = 0

/-! ## The per-point constructor — `MatchingPoint` from place geometry + bridging facts

`mkMatchingPoint_of_graph_vanishing` discharges the full `mkMatchingPoint` hypothesis list at one
`(t, z)`: the place geometry supplies the eight carried root/congruence fields, `hderiv` is derived
from `hsep`, the `aP`-root is the GS graph-vanishing output, and the `BridgeData` supplies the four
π_z-specialised readings from which `coeffExtract` is discharged in tree. -/

/-- **`MatchingPoint` from graph-vanishing + separability (the discharged constructor).**

From the `t`-uniform §5 place geometry `g : PlaceGeometry z` (matching polynomial, two roots — the
proximate one being the GS graph-vanishing / `MatchingExtractor` output — two Hensel congruences, and
separability) together with the per-`(t, z)` bridging data `bd : BridgeData t z root g.aβ g.aP`,
produce a `BetaMatchingVanishes.MatchingPoint x₀ R H hHyp Bcoeff t z root`.

Disposition of `mkMatchingPoint`'s hypotheses: the eight root/congruence fields are carried from `g`;
`hderiv` is *derived* from `g.hsep` (`PlaceGeometry.hderiv`); `coeffExtract` is discharged in tree
from `bd` via `MatchingPoint.mk_coeffExtract`.  No field is assumed `IsUnit`, none is `≡` the goal. -/
def mkMatchingPoint_of_graph_vanishing {t : ℕ} {z : F} {root : rationalRoot (H_tilde' H) z}
    (g : PlaceGeometry (F := F) z)
    (bd : BridgeData (x₀ := x₀) (R := R) (H := H) (hHyp := hHyp) (Bcoeff := Bcoeff)
      t z root g.aβ g.aP) :
    BetaMatchingVanishes.MatchingPoint x₀ R H hHyp Bcoeff t z root :=
  MpProducer.mkMatchingPoint
    (x₀ := x₀) (R := R) (H := H) (hHyp := hHyp) (Bcoeff := Bcoeff) (t := t) (z := z) (root := root)
    g.f g.aβ g.aP g.a₀ g.haβ_root g.haP_root g.haβ_cong g.haP_cong g.hderiv
    bd.hαβ bd.hw bd.hx bd.haP_coeff

/-- **Sanity: the constructed bundle yields the per-point conclusion.**  Firing
`MatchingPoint.pi_z_eq_zero` (Hensel uniqueness + the in-tree `coeffExtract`) on
`mkMatchingPoint_of_graph_vanishing` gives the geometric matching vanishing
`(π_z z root)(betaRec … t) = 0`. -/
theorem mkMatchingPoint_of_graph_vanishing_pi_z_eq_zero
    {t : ℕ} {z : F} {root : rationalRoot (H_tilde' H) z}
    (g : PlaceGeometry (F := F) z)
    (bd : BridgeData (x₀ := x₀) (R := R) (H := H) (hHyp := hHyp) (Bcoeff := Bcoeff)
      t z root g.aβ g.aP) :
    (π_z z root) (betaRec x₀ R H hHyp Bcoeff t) = 0 :=
  (mkMatchingPoint_of_graph_vanishing g bd).pi_z_eq_zero

/-! ## Assembling the `mpFin` finite-range family

`mpFin_of_close_word` threads a per-`z` place geometry and a per-`(t, z)` bridging producer over the
finite counting range `k ≤ t ≤ T`, producing exactly the `mpFin` field of `BetaCurveInputFin`.  The
place geometry is reused at every `t` (it is `t`-uniform); only the `BridgeData` varies with `t`. -/

/-- **The `mpFin` field from a place-geometry producer + a bridging producer.**

Given, for every matching point `z ∈ matchingSet`, the `t`-uniform §5 place geometry
`geom z : PlaceGeometry z`, and for every `(t, z)` in the finite range `k ≤ t ≤ T` the
per-`(t, z)` bridging data `bridge t … z … : BridgeData t z (root z) (geom z).aβ (geom z).aP`,
assemble the finite-range family in the exact shape of `BetaCurveInputFin.mpFin`:

```
∀ t, k ≤ t → t ≤ T → ∀ z ∈ matchingSet, MatchingPoint x₀ R H hHyp Bcoeff t z (root z).
```

Each point is `mkMatchingPoint_of_graph_vanishing (geom z) (bridge t … z …)`; the same place
geometry serves every `t`. -/
def mpFin_of_close_word {k T : ℕ} {matchingSet : Finset F}
    {root : (z : F) → rationalRoot (H_tilde' H) z}
    (geom : (z : F) → z ∈ matchingSet → PlaceGeometry (F := F) z)
    (bridge : ∀ t, k ≤ t → t ≤ T → ∀ z, (hz : z ∈ matchingSet) →
      BridgeData (x₀ := x₀) (R := R) (H := H) (hHyp := hHyp) (Bcoeff := Bcoeff)
        t z (root z) (geom z hz).aβ (geom z hz).aP) :
    ∀ t, k ≤ t → t ≤ T → ∀ z ∈ matchingSet,
      BetaMatchingVanishes.MatchingPoint x₀ R H hHyp Bcoeff t z (root z) :=
  fun t hkt htT z hz =>
    mkMatchingPoint_of_graph_vanishing (geom z hz) (bridge t hkt htT z hz)

/-! ## The `MatchingExtractor`/divisibility route for the proximate root

The proximate-root field `haP_root` of `PlaceGeometry` is, in §5, the GS matching-factor
divisibility `(Y − aP) ∣ f` — exactly the output of the Gap-B keystone
`Q_vanishes_on_close_codeword_graph` (`Agreement.lean`) / the brick
`MatchingExtractor.matchingFactor_dvd_of_orderM_and_count`, transported to the coordinate
power-series ring `F⟦X⟧`.  `Polynomial.dvd_iff_isRoot` turns the divisibility into the root fact, so
the place geometry can be assembled directly from the divisibility the brick delivers. -/

/-- **`PlaceGeometry` from the GS matching-factor divisibility.**  Identical to the `PlaceGeometry`
constructor except the proximate-root field arrives as the GS matching-factor divisibility
`(X − C aP) ∣ f` (`Polynomial.X` is the outer variable `Y`), converted to `f.IsRoot aP` via
`Polynomial.dvd_iff_isRoot`.  This records that `haP_root` is exactly the Gap-B keystone /
`MatchingExtractor` output `(Y − P_z) ∣ Q_z`, transported to `F⟦X⟧`. -/
def placeGeometry_of_matchingDvd {z : F}
    (f : Polynomial (PowerSeries F)) (aβ aP a₀ : PowerSeries F)
    (haβ_root : f.IsRoot aβ)
    (haP_dvd : (Polynomial.X - Polynomial.C aP) ∣ f)
    (haβ_cong : aβ - a₀ ∈ Ideal.span {(PowerSeries.X : PowerSeries F)})
    (haP_cong : aP - a₀ ∈ Ideal.span {(PowerSeries.X : PowerSeries F)})
    (hsep : f.Separable) :
    PlaceGeometry (F := F) z where
  f := f
  aβ := aβ
  aP := aP
  a₀ := a₀
  haβ_root := haβ_root
  haP_root := (Polynomial.dvd_iff_isRoot).mp haP_dvd
  haβ_cong := haβ_cong
  haP_cong := haP_cong
  hsep := hsep

/-- **The `mpFin` field, `MatchingExtractor`/divisibility route.**  As `mpFin_of_close_word`, but the
per-`z` place geometry is supplied via `placeGeometry_of_matchingDvd` from the GS matching-factor
divisibility `(Y − aP) ∣ f` (the Gap-B keystone / brick output), the remaining root/congruence/
separability facts, and the per-`(t, z)` bridging data. -/
def mpFin_of_graph_vanishing_dvd {k T : ℕ} {matchingSet : Finset F}
    {root : (z : F) → rationalRoot (H_tilde' H) z}
    (f : (z : F) → Polynomial (PowerSeries F))
    (aβ aP a₀ : (z : F) → PowerSeries F)
    (haβ_root : ∀ z ∈ matchingSet, (f z).IsRoot (aβ z))
    (haP_dvd : ∀ z ∈ matchingSet, (Polynomial.X - Polynomial.C (aP z)) ∣ f z)
    (haβ_cong : ∀ z ∈ matchingSet, aβ z - a₀ z ∈ Ideal.span {(PowerSeries.X : PowerSeries F)})
    (haP_cong : ∀ z ∈ matchingSet, aP z - a₀ z ∈ Ideal.span {(PowerSeries.X : PowerSeries F)})
    (hsep : ∀ z ∈ matchingSet, (f z).Separable)
    (bridge : ∀ t, k ≤ t → t ≤ T → ∀ z, z ∈ matchingSet →
      BridgeData (x₀ := x₀) (R := R) (H := H) (hHyp := hHyp) (Bcoeff := Bcoeff)
        t z (root z) (aβ z) (aP z)) :
    ∀ t, k ≤ t → t ≤ T → ∀ z ∈ matchingSet,
      BetaMatchingVanishes.MatchingPoint x₀ R H hHyp Bcoeff t z (root z) :=
  mpFin_of_close_word
    (geom := fun z hz =>
      placeGeometry_of_matchingDvd (z := z) (f z) (aβ z) (aP z) (a₀ z)
        (haβ_root z hz) (haP_dvd z hz) (haβ_cong z hz) (haP_cong z hz) (hsep z hz))
    (bridge := bridge)

end MpFinSupply

end ArkLib

/-! ## Axiom audit — every declaration here must rest only on
`[propext, Classical.choice, Quot.sound]`, with no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ArkLib.MpFinSupply.PlaceGeometry.hderiv
#print axioms ArkLib.MpFinSupply.mkMatchingPoint_of_graph_vanishing
#print axioms ArkLib.MpFinSupply.mkMatchingPoint_of_graph_vanishing_pi_z_eq_zero
#print axioms ArkLib.MpFinSupply.mpFin_of_close_word
#print axioms ArkLib.MpFinSupply.placeGeometry_of_matchingDvd
#print axioms ArkLib.MpFinSupply.mpFin_of_graph_vanishing_dvd
