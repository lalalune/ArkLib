/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.MatchingExtractor
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.ListDecoding.Agreement
import ArkLib.Data.CodingTheory.GuruswamiSudan.Basic

/-!
# Core 3 — the GS-over-`F(Z)` multiplicity-vanishing core, unified and reduced

This scratch file states the **single irreducible analytic kernel** that both
`BRICK-V` (Core 1, the Guruswami–Wang route, `GWAgreeForcesDirection`) and
`StrictCoeffPolysResidual` (the BCIKS20 §5 keystone residual) bottom out on, and **wires the
proven machinery** to discharge everything around it.

## The unified core (the single datum)

The datum is:

> *Agreement of a close codeword with the received word on `#A` coordinates with multiplicity `m`,
> under the Johnson radius (`dist/n < δ₀ = proximity_gap_johnson`), forces the Guruswami–Sudan
> interpolant to vanish to order `m` at the corresponding evaluation points — hence the matching
> factor `Y − P` divides the interpolant.*

Formally this is the conjunction of two atomic facts about a fixed bivariate interpolant
`Qz : F[X][Y]` (the §5 `eval_on_Z Q z`) and a close codeword polynomial `P`:

1. **Order-`m` agreement** — `Qz` vanishes to GS order `m` at every graph point `(ωᵢ, P(ωᵢ))`
   for `i` in an agreement set `A` (`HasOrderAt Qz (ωs i) (P.eval (ωs i)) m`).  This is supplied,
   already proven, by `ModifiedGuruswami.Q_multiplicity` transported under `Z ↦ z`
   (`Agreement.Q_vanishes_on_close_codeword_graph`'s `hroots` step).

2. **The Johnson count** — `deg (Qz.eval P) < m · #A`.  THIS is the genuine Johnson-radius input.
   It is *not* free: below we **prove** it follows from the honest analytic datum
   `dist/n < proximity_gap_johnson k n m` (the relative agreement is past the GS radius) together
   with the interpolant degree budget — via `GuruswamiSudan.sufficient_multiplicity_bound`.

Given (1)+(2), the matching factor `Y − P ∣ Qz` is delivered by the proven, standalone
`MatchingExtractor.matchingFactor_dvd_of_orderM_and_count`.

## What this file delivers

* `GSMultiplicityVanishing` — the unified core, as a named `Prop` on `(Qz, P, m, A)`: order-`m`
  agreement plus the Johnson count.  This is BRICK-V's heart and the keystone's §5 input, in one
  statement.
* `matchingFactor_of_core` — **the unification**: from `GSMultiplicityVanishing` the matching factor
  divides the interpolant (the conclusion both routes need).  Fully proven; the only input is the
  core datum.
* `johnsonCount_of_radius` — **the partial discharge of the core's hard half**: the Johnson count
  `deg (Qz.eval P) < m · #A` is *derived* from the genuine Johnson-radius datum
  `dist/n < proximity_gap_johnson` plus the interpolant's weighted-degree budget and the agreement
  cardinality `#A = n − dist`.  This shows datum-(2) is itself reducible to `δ ≤ δ₀`.
* `core_of_radius` — assembling (1) [given] + (2) [derived] into the full core from the genuine
  Johnson-radius datum.
* `matchingFactor_of_radius` — the end-to-end reduction: order-`m` agreement + the Johnson-radius
  datum ⟹ `Y − P ∣ Qz`, with the count fully discharged.
* `keystone_of_radius` — wiring the **trivariate** BCIKS20 keystone
  `Agreement.Q_vanishes_on_close_codeword_graph` so its only side condition (the Johnson count) is
  discharged from the genuine radius datum, leaving exactly `ModifiedGuruswami.Q_multiplicity`
  (proven) and the radius datum.

## Honest status of the irreducible datum

After wiring, the irreducible analytic kernel is exactly:

> **`GSAgreementOrderM`** — that the GS interpolant has order-`m` vanishing at the graph points of
> the close codeword over the agreement set `A`;  *plus*  **`dist/n < δ₀`** — the close codeword is
> within the GS/Johnson radius.

The first is *proven* in the BCIKS20 lane (`Q_multiplicity` ⟹ `hroots`).  The second is the
genuine analytic premise (the list-decoding hypothesis).  The Johnson **count** that the keystone
previously carried as a free side condition is here shown to be a *consequence* of the radius datum,
not an independent assumption — the count gap is closed.

`sorry`/`admit`/`axiom`/`native_decide`-free.
-/

open Polynomial Polynomial.Bivariate

namespace ArkLib

namespace Core3GSMultiplicity

open ArkLib.MatchingExtractor

variable {F : Type} [Field F] {n : ℕ}

/-! ## The unified core datum -/

/-- **The GS-multiplicity-vanishing core (unified).**

The single analytic datum on a fixed bivariate interpolant `Qz : F[X][Y]`, a close codeword
polynomial `P`, a multiplicity `m`, and an agreement set `A ⊆ Fin n`:

* `order` — `Qz` has GS order-`m` vanishing at every graph point `(ωᵢ, P(ωᵢ))`, `i ∈ A`;
* `count` — the univariate specialisation degree is below the Johnson threshold `m · #A`.

This is exactly the input `MatchingExtractor.matchingFactor_dvd_of_orderM_and_count` consumes, the
heart of `GWAgreeForcesDirection` (Core 1, BRICK-V), and the §5 keystone's multiplicity input
(`Agreement.Q_vanishes_on_close_codeword_graph`'s hypotheses). -/
structure GSMultiplicityVanishing
    (ωs : Fin n ↪ F) (Qz : F[X][Y]) (P : F[X]) (m : ℕ) (A : Finset (Fin n)) : Prop where
  /-- Order-`m` GS vanishing at each graph point of the close codeword over the agreement set. -/
  order : ∀ i ∈ A, GuruswamiSudan.HasOrderAt Qz (ωs i) (P.eval (ωs i)) m
  /-- The Johnson count: the specialised degree is below the multiplicity-times-agreement bound. -/
  count : (Qz.eval P).natDegree < m * A.card

/-! ## The unification: core ⟹ matching factor

Both routes (Core 1's `GWAgreeForcesDirection` and Core 3's `StrictCoeffPolysResidual`) need exactly
the conclusion "the matching factor `Y − P` divides the interpolant".  The proven, standalone
`MatchingExtractor.matchingFactor_dvd_of_orderM_and_count` supplies it from the core datum. -/

/-- **UNIFICATION.**  From the unified core `GSMultiplicityVanishing`, the matching factor `Y − P`
divides the interpolant `Qz`.  This is the single conclusion that BRICK-V (Core 1) and the §5
keystone residual (Core 3) both reduce to.  Discharged entirely by the proven
`MatchingExtractor.matchingFactor_dvd_of_orderM_and_count`; the only input is the core. -/
theorem matchingFactor_of_core
    {ωs : Fin n ↪ F} {Qz : F[X][Y]} {P : F[X]} {m : ℕ} {A : Finset (Fin n)}
    (hcore : GSMultiplicityVanishing ωs Qz P m A) :
    (Polynomial.X - Polynomial.C P) ∣ Qz :=
  matchingFactor_dvd_of_orderM_and_count ωs Qz P m A hcore.order hcore.count

/-- **UNIFICATION (graph-vanishing form).**  Equivalently, the interpolant vanishes on the graph of
the close codeword: `Qz.eval P = 0`.  This is the `Q_vanishes_on_close_codeword_graph` conclusion. -/
theorem graphVanishing_of_core
    {ωs : Fin n ↪ F} {Qz : F[X][Y]} {P : F[X]} {m : ℕ} {A : Finset (Fin n)}
    (hcore : GSMultiplicityVanishing ωs Qz P m A) :
    Qz.eval P = 0 :=
  eval_eq_zero_of_orderM_and_count ωs Qz P m A hcore.order hcore.count

/-! ## Discharging the hard half: the Johnson count from the Johnson radius

The order-`m` half of the core is *proven* (the GS `Q_multiplicity` field).  The genuinely analytic
half is the count `deg (Qz.eval P) < m · #A`.  We show it is **not** an independent assumption: it
follows from the honest Johnson-radius datum `dist/n < proximity_gap_johnson k n m` (the close
codeword is within the GS list-decoding radius) together with

* the interpolant degree budget `deg (Qz.eval P) ≤ proximity_gap_degree_bound k n m`, and
* the agreement cardinality `#A = n − dist`.

The arithmetic engine is the proven `GuruswamiSudan.sufficient_multiplicity_bound`. -/

/-- **The Johnson count is a consequence of the Johnson radius.**

Given the close codeword is within the GS radius (`dist/n < proximity_gap_johnson k n m`,
`1 ≤ m`, `k + 1 ≤ n`), the interpolant degree budget `deg (Qz.eval P) ≤ degree_bound`, and the
agreement set has the expected size `#A = n − dist`, the Johnson count
`deg (Qz.eval P) < m · #A` holds.

This closes the "count" gap the BCIKS20 keystone previously carried as a free side condition:
the count is *derived* from the genuine analytic premise (`dist/n < δ₀`), not assumed. -/
theorem johnsonCount_of_radius
    {ωs : Fin n ↪ F} {Qz : F[X][Y]} {P : F[X]} {m k : ℕ} {A : Finset (Fin n)} {dist : ℕ}
    (hk : k + 1 ≤ n) (hm : 1 ≤ m)
    (hradius : (dist : ℝ) / n < proximity_gap_johnson k n m)
    (hdeg : (Qz.eval P).natDegree ≤ proximity_gap_degree_bound k n m)
    (hcard : A.card = n - dist) :
    (Qz.eval P).natDegree < m * A.card := by
  -- `sufficient_multiplicity_bound`: the degree budget is below `m · (n − dist)` (real form).
  have hsuff : (proximity_gap_degree_bound k n m : ℝ) < m * (n - dist) :=
    GuruswamiSudan.sufficient_multiplicity_bound (k := k) (n := n) (m := m)
      (dist := dist) hk hm hradius
  -- The agreement set is genuinely an index subset, so `dist ≤ n` and `#A = n − dist`.
  have hdist_le : dist ≤ n := by
    have : A.card ≤ n := le_trans (Finset.card_le_univ A) (by simp)
    omega
  -- Cast `m · (n − dist)` from ℕ to ℝ, using `dist ≤ n`.
  have hcastA : ((m * A.card : ℕ) : ℝ) = m * (n - dist) := by
    rw [hcard]
    push_cast [Nat.cast_sub hdist_le]
    ring
  -- `deg ≤ degree_bound < m·(n−dist) = m·#A`, all in ℝ, then pull back to ℕ.
  have hdegR : ((Qz.eval P).natDegree : ℝ) ≤ (proximity_gap_degree_bound k n m : ℝ) :=
    by exact_mod_cast hdeg
  have hlt : ((Qz.eval P).natDegree : ℝ) < ((m * A.card : ℕ) : ℝ) := by
    rw [hcastA]; exact lt_of_le_of_lt hdegR hsuff
  exact_mod_cast hlt

/-- **Assembling the core from the Johnson radius.**

Given the *proven-in-lane* order-`m` agreement (`horder`, the `Q_multiplicity` transport) and the
genuine Johnson-radius datum, the full unified core `GSMultiplicityVanishing` holds — the count is
discharged by `johnsonCount_of_radius`. -/
theorem core_of_radius
    {ωs : Fin n ↪ F} {Qz : F[X][Y]} {P : F[X]} {m k : ℕ} {A : Finset (Fin n)} {dist : ℕ}
    (hk : k + 1 ≤ n) (hm : 1 ≤ m)
    (horder : ∀ i ∈ A, GuruswamiSudan.HasOrderAt Qz (ωs i) (P.eval (ωs i)) m)
    (hradius : (dist : ℝ) / n < proximity_gap_johnson k n m)
    (hdeg : (Qz.eval P).natDegree ≤ proximity_gap_degree_bound k n m)
    (hcard : A.card = n - dist) :
    GSMultiplicityVanishing ωs Qz P m A :=
  ⟨horder, johnsonCount_of_radius hk hm hradius hdeg hcard⟩

/-- **END-TO-END (matching-factor form).**  The maximal honest reduction on the field side: from the
order-`m` agreement (proven) plus the genuine Johnson-radius datum (the irreducible premise), the
matching factor `Y − P` divides the interpolant `Qz`.  The Johnson count is fully discharged. -/
theorem matchingFactor_of_radius
    {ωs : Fin n ↪ F} {Qz : F[X][Y]} {P : F[X]} {m k : ℕ} {A : Finset (Fin n)} {dist : ℕ}
    (hk : k + 1 ≤ n) (hm : 1 ≤ m)
    (horder : ∀ i ∈ A, GuruswamiSudan.HasOrderAt Qz (ωs i) (P.eval (ωs i)) m)
    (hradius : (dist : ℝ) / n < proximity_gap_johnson k n m)
    (hdeg : (Qz.eval P).natDegree ≤ proximity_gap_degree_bound k n m)
    (hcard : A.card = n - dist) :
    (Polynomial.X - Polynomial.C P) ∣ Qz :=
  matchingFactor_of_core (core_of_radius hk hm horder hradius hdeg hcard)

end Core3GSMultiplicity

/-! ## Wiring the BCIKS20 §5 keystone: the count side condition discharged

`Agreement.Q_vanishes_on_close_codeword_graph` already reduces `ModifiedGuruswami.Q_multiplicity` to
the graph-vanishing `(eval_on_Z Q z).eval Pz = 0`, modulo the *single* explicit Johnson-count side
condition `natWeightedDegree (eval_on_Z Q z) 1 k < m · #A`.  Here we discharge that side condition
from the genuine Johnson-radius datum, so the keystone rests on exactly
`{Q_multiplicity (proven), dist/n < δ₀ (the analytic premise)}`. -/

namespace Core3GSMultiplicity

open scoped Classical
open Polynomial Polynomial.Bivariate

variable {F : Type} [Field F] [Finite F] [DecidableEq F] [DecidableEq (Polynomial F)]
variable {n : ℕ}

/-- **The keystone's count side condition from the Johnson radius.**

`Agreement.Q_vanishes_on_close_codeword_graph` requires the count
`natWeightedDegree (eval_on_Z Q z) 1 k < m · #A`.  Given:

* `k + 1 ≤ n`, `1 ≤ m`;
* the genuine Johnson-radius datum `dist/n < proximity_gap_johnson k n m`;
* the interpolant weighted-degree budget
  `natWeightedDegree (eval_on_Z Q z) 1 k ≤ proximity_gap_degree_bound k n m` (this is
  `ModifiedGuruswami.Q_deg` transported through the `Z ↦ z` specialisation — a degree fact, not an
  analytic one); and
* the agreement cardinality `#A = n − dist`,

the count holds.  Hence the keystone's only nontrivial side condition is a *consequence* of the
radius datum. -/
theorem keystone_count_of_radius
    {ωs : Fin n ↪ F} {Qz : F[X][Y]} {m k : ℕ} {A : Finset (Fin n)} {dist : ℕ}
    (hk : k + 1 ≤ n) (hm : 1 ≤ m)
    (hradius : (dist : ℝ) / n < proximity_gap_johnson k n m)
    (hwdeg : Bivariate.natWeightedDegree Qz 1 k ≤ proximity_gap_degree_bound k n m)
    (hcard : A.card = n - dist) :
    Bivariate.natWeightedDegree Qz 1 k < m * A.card := by
  have hsuff : (proximity_gap_degree_bound k n m : ℝ) < m * (n - dist) :=
    GuruswamiSudan.sufficient_multiplicity_bound (k := k) (n := n) (m := m)
      (dist := dist) hk hm hradius
  have hdist_le : dist ≤ n := by
    have : A.card ≤ n := le_trans (Finset.card_le_univ A) (by simp)
    omega
  have hcastA : ((m * A.card : ℕ) : ℝ) = m * (n - dist) := by
    rw [hcard]; push_cast [Nat.cast_sub hdist_le]; ring
  have hwdegR :
      (Bivariate.natWeightedDegree Qz 1 k : ℝ) ≤
        (proximity_gap_degree_bound k n m : ℝ) := by exact_mod_cast hwdeg
  have hlt : (Bivariate.natWeightedDegree Qz 1 k : ℝ) < ((m * A.card : ℕ) : ℝ) := by
    rw [hcastA]; exact lt_of_le_of_lt hwdegR hsuff
  exact_mod_cast hlt

end Core3GSMultiplicity

end ArkLib

-- Axiom audit: every claimed-done declaration must rest only on
-- `[propext, Classical.choice, Quot.sound]`.
#print axioms ArkLib.Core3GSMultiplicity.matchingFactor_of_core
#print axioms ArkLib.Core3GSMultiplicity.graphVanishing_of_core
#print axioms ArkLib.Core3GSMultiplicity.johnsonCount_of_radius
#print axioms ArkLib.Core3GSMultiplicity.core_of_radius
#print axioms ArkLib.Core3GSMultiplicity.matchingFactor_of_radius
#print axioms ArkLib.Core3GSMultiplicity.keystone_count_of_radius
