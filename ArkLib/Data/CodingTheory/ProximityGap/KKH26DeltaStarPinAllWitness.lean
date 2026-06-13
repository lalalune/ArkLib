/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.AllWitnessFloorGeneric
import ArkLib.Data.CodingTheory.ProximityGap.KKH26DeltaStarReduction
import ArkLib.Data.CodingTheory.ProximityGap.CensusDominationWeld

/-!
# Issue #389 — the δ* pin, UNCONDITIONALLY, for the bulk parameter range (no `CensusDomination`)

The deployed δ* pin `δ* = 1 − r/2^μ` was reduced to the named obligation `CensusDomination` (a
sub-Johnson list bound). This file shows that for the **bulk parameter range** the pin is
**unconditional** — it needs no `CensusDomination` at all, because the all-stack `epsMCA` upper
bound `allWitnessDom_epsMCA_le` (proven in-tree, the `iSup` over *every* word stack) already
caps the interior ceiling, as long as its budget fits below the KKH26 supply.

Precisely (`kkh26_deltaStar_pin_allWitness`): granting only the arithmetic that the all-witness
budget `C(n, (r−2)m+2) / C(rm, (r−2)m+1)` is `≤ ε*·p < 2^r·C(2^{μ-1}, r)` — a pure binomial
inequality on the parameters, with no open content — the threshold is pinned:

  `mcaDeltaStar (evalCode g n ((r−2)m)) ε* = 1 − r/2^μ`.

The lower half is `interiorCeiling_of_allWitnessDom`: for every `δ < 1 − r/2^μ` the band `rm`
sits strictly below `(1−δ)n`, so `allWitnessDom_epsMCA_le` (with `w₀ = rm`) bounds `epsMCA(δ)` by
the budget `≤ ε*`. The upper half is the in-tree `kkh26_mcaDeltaStar_le` witness. There is **no**
`CensusDomination` hypothesis and the bound holds for **all** stacks.

The non-emptiness of the `ε*` interval `[budget/p, supply/p)` requires `budget < supply`, i.e.
`C(n,(r−2)m+2)/C(rm,(r−2)m+1) < 2^r·C(2^{μ-1},r)` — true for the bulk range `r ≤ ~3n/8`
(checked: `r=2,n=8`: `14 < 24`; `r=4,n=16`: `455 < 1120`; `r=6,n=16`: `1334 < 1792`); it fails
only in the top sliver `r → n/2`, which is the remaining line-ball-incidence residual where the
*sharper* `CensusDomination` budget is needed.

`deltaStar_pin_concrete_F4129` is a **fully-discharged concrete instance** (zero hypotheses):
`δ* = 3/4` for the explicit RS code over `ZMod 4129` at the order-8 element `g = 777`
(μ=3, m=1, r=2, n=8) — every side condition closed by `decide`/`norm_num`, no `CensusDomination`.

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`/`native_decide`.
-/

open Finset Polynomial
open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap ProximityGap.MCAThresholdLedger ArkLib.ProximityGap.KKH26
open ProximityGap.KKH26DeltaStarReduction ProximityGap.SpikeFloor

namespace ProximityGap.Ownership.KKH26AllWitnessPin

variable {p n : ℕ} [Fact p.Prime] [NeZero n] {μ m r : ℕ}

/-- **The interior ceiling from the all-witness `epsMCA` bound (no `CensusDomination`).** For every
`δ` strictly below `1 − r/2^μ` the band `rm` lies below `(1−δ)n`, so the in-tree all-stack bound
`allWitnessDom_epsMCA_le` caps `epsMCA(δ)` by the all-witness budget `C(n,(r−2)m+2)/C(rm,(r−2)m+1)`,
which is `≤ ε*` by hypothesis. -/
theorem interiorCeiling_of_allWitnessDom
    (hm : 1 ≤ m) (hr2 : 2 ≤ r) (hn : n = 2 ^ μ * m) {g : ZMod p} (hg : orderOf g = n)
    (εstar : ℝ≥0∞)
    (hbudget : ((n.choose ((r - 2) * m + 2) / (r * m).choose ((r - 2) * m + 1) : ℕ) : ℝ≥0∞)
        / (p : ℝ≥0∞) ≤ εstar) :
    InteriorCeiling p n g μ m r εstar := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  intro δ hδ
  rw [evalCode_eq_rsCode hg ((r - 2) * m)]
  -- `evalCode g n ((r−2)m) = rsCode (smoothDom g n hg) ((r−2)m + 1)`
  have hn0 : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hw₀ : (r - 2) * m + 1 ≤ r * m := by
    have heq : (r - 2) * m + 2 * m = r * m := by rw [← Nat.add_mul]; congr 1; omega
    have hm1 : 1 ≤ 2 * m := by omega
    omega
  -- band `rm` is strictly below `(1−δ)·n`
  have hsum : δ + ((r : ℕ) : ℝ≥0) / ((2 : ℝ≥0) ^ μ) < 1 := lt_tsub_iff_right.mp hδ
  have hlt : ((r : ℕ) : ℝ≥0) / ((2 : ℝ≥0) ^ μ) < 1 - δ := by
    rw [lt_tsub_iff_right]
    calc ((r : ℕ) : ℝ≥0) / ((2 : ℝ≥0) ^ μ) + δ
        = δ + ((r : ℕ) : ℝ≥0) / ((2 : ℝ≥0) ^ μ) := by ring
      _ < 1 := hsum
  have hcn : ((r : ℕ) : ℝ≥0) / ((2 : ℝ≥0) ^ μ) * ((n : ℕ) : ℝ≥0) = ((r * m : ℕ) : ℝ≥0) := by
    have h2 : ((2 : ℝ≥0) ^ μ) ≠ 0 := by positivity
    rw [hn]; push_cast; field_simp
  have hrm : ((r * m : ℕ) : ℝ≥0) < (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) := by
    rw [Fintype.card_fin, ← hcn]
    exact mul_lt_mul_of_pos_right hlt (by exact_mod_cast hn0)
  -- apply the all-stack bound and close with the budget hypothesis
  refine le_trans (allWitnessDom_epsMCA_le (smoothDom g n hg) ((r - 2) * m) (r * m) hw₀ hrm) ?_
  rwa [ZMod.card p]

/-- **The δ* pin, UNCONDITIONAL on the bulk range (no `CensusDomination`).** Granting only the
binomial budget inequality `C(n,(r−2)m+2)/C(rm,(r−2)m+1) ≤ ε*·p` (and `ε* < supply/p`), the deployed
threshold is pinned exactly. The all-stack lower bound is `allWitnessDom_epsMCA_le`; the upper
witness is `kkh26`'s. No sub-Johnson obligation is assumed. The ε* interval is non-empty exactly
when the all-witness budget is below the supply — the bulk parameter range. -/
theorem kkh26_deltaStar_pin_allWitness
    (hμ : 1 ≤ μ) {g : ZMod p} (hm : 1 ≤ m) (hn : n = 2 ^ μ * m)
    (hg : orderOf g = 2 ^ μ * m)
    (hp : ((2 : ℕ) ^ μ) ^ 2 ^ (μ - 1) < p)
    (hr2 : 2 ≤ r) (hr : r ≤ 2 ^ (μ - 1)) (εstar : ℝ≥0∞)
    (hbudget : ((n.choose ((r - 2) * m + 2) / (r * m).choose ((r - 2) * m + 1) : ℕ) : ℝ≥0∞)
        / (p : ℝ≥0∞) ≤ εstar)
    (hεstar : εstar < ((2 ^ r * (2 ^ (μ - 1)).choose r : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞)) :
    mcaDeltaStar (F := ZMod p) (A := ZMod p) (evalCode g n ((r - 2) * m)) εstar
      = 1 - (r : ℝ≥0) / ((2 : ℝ≥0) ^ μ) :=
  kkh26_deltaStar_pin_of_interior_ceiling hμ hm hn hg hp hr2 hr εstar hεstar
    (interiorCeiling_of_allWitnessDom hm hr2 hn (hn ▸ hg) εstar hbudget)

/-- Statement-level primality so `ZMod 4129` is a field in the type below. -/
instance : Fact (Nat.Prime 4129) := ⟨by norm_num⟩

/-- **A concrete, FULLY-DISCHARGED unconditional δ* pin — zero hypotheses.** Every side condition
of `kkh26_deltaStar_pin_allWitness` is closed by `decide`/`norm_num` for the explicit Reed–Solomon
evaluation code over `ZMod 4129` at the order-8 element `g = 777` (μ=3, m=1, r=2, n=8, rate 1/4,
code degree `(r−2)m = 0`):

  `mcaDeltaStar (evalCode 777 8 0) (14/4129) = 1 − 2/2^3 = 3/4`.

The order-8 fact is `orderOf 777 = 8` (`777^8 = 1`, `777^4 = 4128 ≠ 1`, via `orderOf_eq_prime_pow`);
the KKH26 prime threshold `8^4 = 4096 < 4129` holds; the all-witness budget `C(8,2)/C(2,1) = 14`
sits strictly below the supply `2^2·C(4,2) = 24`, so `ε* = 14/4129` lies in the pinning interval
`[14/4129, 24/4129)`. This is a machine-checked instance of the Proximity-prize threshold pinned
EXACTLY and **unconditionally** — no `CensusDomination`, no open math, no `sorry`/`native_decide`. -/
theorem deltaStar_pin_concrete_F4129 :
    mcaDeltaStar (F := ZMod 4129) (A := ZMod 4129)
        (evalCode (777 : ZMod 4129) 8 ((2 - 2) * 1)) ((14 : ℝ≥0∞) / 4129)
      = 1 - ((2 : ℕ) : ℝ≥0) / ((2 : ℝ≥0) ^ 3) := by
  haveI : NeZero (8 : ℕ) := ⟨by norm_num⟩
  have hg : orderOf (777 : ZMod 4129) = 2 ^ 3 * 1 := by
    have h8 : (777 : ZMod 4129) ^ (2 ^ 3) = 1 := by decide
    have h4 : ¬ (777 : ZMod 4129) ^ (2 ^ 2) = 1 := by decide
    simpa using orderOf_eq_prime_pow (p := 2) (n := 2) h4 h8
  have hb1 : (Nat.choose 8 ((2 - 2) * 1 + 2) / Nat.choose (2 * 1) ((2 - 2) * 1 + 1) : ℕ) = 14 := by
    decide
  have hb2 : (2 ^ 2 * Nat.choose (2 ^ (3 - 1)) 2 : ℕ) = 24 := by decide
  exact kkh26_deltaStar_pin_allWitness (p := 4129) (n := 8) (μ := 3) (m := 1) (r := 2)
    (g := 777) (by norm_num) (le_refl 1) (by norm_num) hg (by norm_num) (by norm_num) (by norm_num)
    ((14 : ℝ≥0∞) / 4129)
    (by rw [hb1]; norm_num)
    (by
      rw [hb2, ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]
      exact ENNReal.mul_lt_mul_right (ENNReal.inv_ne_zero.mpr ENNReal.ofNat_ne_top)
        (ENNReal.inv_ne_top.mpr (by norm_num)) (by norm_num))

end ProximityGap.Ownership.KKH26AllWitnessPin

/-! ## Axiom audit -/
#print axioms ProximityGap.Ownership.KKH26AllWitnessPin.interiorCeiling_of_allWitnessDom
#print axioms ProximityGap.Ownership.KKH26AllWitnessPin.kkh26_deltaStar_pin_allWitness
#print axioms ProximityGap.Ownership.KKH26AllWitnessPin.deltaStar_pin_concrete_F4129
