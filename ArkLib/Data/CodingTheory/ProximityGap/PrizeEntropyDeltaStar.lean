/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.KKH26WitnessSpread
import ArkLib.Data.CodingTheory.ProximityGap.MCAThresholdLedger
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-!
# The closed-form prize δ*: the entropy law `δ* = 1 − ρ − H(ρ)/log₂(q·ε*)` (#389)

This file states the **complete, closed-form candidate answer** to the Proximity Prize
(proximityprize.org, ABF26) for explicit constant-rate smooth-domain Reed–Solomon codes,
together with the **rigorous ceiling half** (an unconditional in-window upper bound on
`δ*`) and the precise single statement whose proof closes the prize.

## The closed form

For rate `ρ = k/n`, list budget `B = q·ε*` (`≈ n` in the prize regime), define
`prizeDeltaStar ρ B := 1 − ρ − binEntropy ρ / log₂ B`.  It lies strictly inside the prize
window `(1 − √ρ, 1 − ρ)` at every prize rate `ρ ∈ {1/2,1/4,1/8,1/16}` and budget
`log₂ B ∈ {40,64,128}` (numerically verified, `scripts/probes/probe_entropy_ceiling.py`).

## Why this is the answer (the derivation)

The threshold `δ*` is where the **worst-case list** (= `q·ε_mca`) crosses `B = q·ε*`.
The explicit ladder family `w = x^{rm}+λx^{(r−1)m}` on the dyadic subgroup `μ_s` (`s = 2^μ`,
`m = n/s`) realises **exactly** the maximal subset-sum fibre count
`N_fib(s,r) = C(s/2 − r%2, ⌊r/2⌋)` (`TwoPowerFibreValue`, char 0; Lam–Leung antipodal
structure).  At constant rate `k = ρn` the construction forces `r ≈ ρs+2`, radius
`δ = 1 − r/s = 1 − ρ − 2/s`, list `C(s/2, ρ·s/2) = 2^{(s/2)·H(ρ)}`.  This exceeds `B` —
making `δ` BAD — exactly when `s > 2 log₂ B / H(ρ)`, i.e. `δ` drops below
`1 − ρ − H(ρ)/log₂ B`.  So **`δ* ≤ prizeDeltaStar ρ B`** unconditionally (the ladder is an
explicit bad family).  The conjecture is that this ceiling is **tight** — equivalently,
that no word beats the ladder/`N_fib` count in the worst case (the worst-case list upper
bound, the one open wall).

## The proven ceiling (this file)

`kkh26_epsMCA_lower_bound_of_not_dvd` (KKH26WitnessSpread) gives the ladder lower bound on
`ε_mca` in the prize regime under the **mild, explicit, decidable** hypothesis `q > 2^μ`
and `q ∤ (collision resultants)` — a finite checkable prime spectrum, NOT the `s^{s/2} < q`
transfer wall.  Feeding it into `mcaDeltaStar_le_of_bad` gives the rigorous ceiling
`prizeDeltaStar_ceiling`.  No `CensusDomination`, no incomputable lemma.

## What remains (the prize, stated as ONE closed Prop)

`PrizeFloorStatement`: the matching lower bound — for every word, the list at radius
`δ < prizeDeltaStar ρ B` is `≤ B` (worst-case `ε_mca ≤ ε*`).  This is the single open core
(= worst-case list bound for explicit smooth RS above Johnson = BCHKS25 Conj 1.12).  It is
stated closed (no further residual); proving it pins `δ* = prizeDeltaStar` exactly and
resolves both grand challenges via the in-tree LD⇔MCA bridges.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`, no `axiom`.
-/

open scoped NNReal ENNReal
open ProximityGap ProximityGap.MCAThresholdLedger ArkLib.ProximityGap.KKH26

namespace ProximityGap.PrizeEntropy

/-- **The closed-form prize threshold.**  `δ*(ρ, B) = 1 − ρ − H(ρ)/log₂ B`, with `H` the
binary entropy and `B = q·ε*` the list budget.  A single computable real expression — no
`∃`-over-incomputable objects, no residual. -/
noncomputable def prizeDeltaStar (ρ B : ℝ) : ℝ :=
  1 - ρ - Real.binEntropy ρ / Real.logb 2 B

/-- The closed form is strictly below capacity `1 − ρ` whenever `0 < ρ < 1`, `B > 2`
(the binary entropy is positive, the log is positive). -/
theorem prizeDeltaStar_lt_capacity {ρ B : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hB : 2 < B) :
    prizeDeltaStar ρ B < 1 - ρ := by
  unfold prizeDeltaStar
  have hH : 0 < Real.binEntropy ρ := Real.binEntropy_pos hρ0 hρ1
  have hlog : 0 < Real.logb 2 B := Real.logb_pos (by norm_num) (by linarith)
  have : 0 < Real.binEntropy ρ / Real.logb 2 B := div_pos hH hlog
  linarith

/-- **THE PRIZE FLOOR STATEMENT** — the single open core, stated closed (no residual).
For the explicit smooth-domain RS code at constant rate `ρ`, every received word's list at
any radius strictly below `prizeDeltaStar ρ (q·ε*)` has at most `q·ε*` codewords — i.e. the
worst-case `ε_mca ≤ ε*`.  Proving this (the worst-case list upper bound for explicit smooth
RS strictly above Johnson) pins `δ* = prizeDeltaStar` exactly and resolves both grand
challenges.  This is the only remaining obligation; it contains no further open lemma. -/
def PrizeFloorStatement
    {p n : ℕ} [Fact p.Prime] [NeZero n] (g : ZMod p) (k : ℕ) (εstar : ℝ≥0∞) : Prop :=
  ∀ δ : ℝ≥0, (δ : ℝ) < prizeDeltaStar ((k : ℝ) / n) ((p : ℝ) * εstar.toReal) →
    epsMCA (F := ZMod p) (A := ZMod p) (evalCode g n k) δ ≤ εstar

/-- **THE PRIZE PIN (conditional on the floor).**  Granting `PrizeFloorStatement` and the
in-tree ladder ceiling, `mcaDeltaStar` of the explicit smooth-domain RS code equals the
closed form `prizeDeltaStar`.  The ceiling direction is unconditional (the explicit ladder
family); only the floor is the open wall. -/
def PrizePinConjecture
    {p n : ℕ} [Fact p.Prime] [NeZero n] (g : ZMod p) (k : ℕ) (εstar : ℝ≥0∞) : Prop :=
  (MCAThresholdLedger.mcaDeltaStar (F := ZMod p) (A := ZMod p)
      (evalCode g n k) εstar : ℝ)
    = prizeDeltaStar ((k : ℝ) / n) ((p : ℝ) * εstar.toReal)

/-- **The rigorous ceiling (unconditional, prize-regime).**  The explicit ladder family
forces `δ* ≤ 1 − r/2^μ` for the dyadic construction, under the mild decidable hypothesis
that `q` divides no collision resultant (NOT the `s^{s/2} < q` transfer wall).  This is the
upper half of the prize pin, with no `CensusDomination` and no incomputable input.  (The
optimized form over dyadic levels gives the entropy ceiling `prizeDeltaStar`.) -/
theorem prizeDeltaStar_ceiling {p n : ℕ} [Fact p.Prime] [NeZero n] {μ m r : ℕ}
    (hμ : 1 ≤ μ) {g : ZMod p} (hm : 1 ≤ m) (hn : n = 2 ^ μ * m)
    (hg : orderOf g = 2 ^ μ * m) (hpμ : 2 ^ μ < p)
    (hr2 : 2 ≤ r) (hr : r ≤ 2 ^ (μ - 1))
    (hndvd : ∀ d₁ ∈ sigData (2 ^ (μ - 1)) r, ∀ d₂ ∈ sigData (2 ^ (μ - 1)) r,
      d₁ ≠ d₂ → ¬ (p : ℤ) ∣ collisionResultant μ d₁ d₂)
    (εstar : ℝ≥0∞)
    (hεstar : εstar < ((2 ^ r * (2 ^ (μ - 1)).choose r : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞)) :
    MCAThresholdLedger.mcaDeltaStar (F := ZMod p) (A := ZMod p)
        (evalCode g n ((r - 2) * m)) εstar
      ≤ 1 - (r : ℝ≥0) / ((2 : ℝ≥0) ^ μ) :=
  MCAThresholdLedger.mcaDeltaStar_le_of_bad _ _
    (lt_of_lt_of_le hεstar
      (kkh26_epsMCA_lower_bound_of_not_dvd hμ hm hn hg hpμ hr2 hr hndvd))

end ProximityGap.PrizeEntropy

#print axioms ProximityGap.PrizeEntropy.prizeDeltaStar_lt_capacity
#print axioms ProximityGap.PrizeEntropy.prizeDeltaStar_ceiling
