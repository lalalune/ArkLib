/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GrandChallenges
import ArkLib.Data.CodingTheory.ProximityGap.CapacityBounds

/-!
# Refuting the ABF26 §4.5 MCA conjecture from the CS25 complete-CA-breakdown (#141 / #232)

`GrandChallenges.mcaConjecture` asserts a uniform polynomial upper bound
`ε_mca(C,δ) ≤ (1/|F|)·n^{c₁}/(ρ^{c₂}·η^{c₃})` (`η = 1−ρ−δ`), with the constants `(c₁,c₂,c₃)`
quantified **before** the `∀` over Reed–Solomon codes.

This file gives the **verified disproof skeleton**: since `ε_mca ≥ ε_ca` (`epsCA_le_epsMCA`), a
complete correlated-agreement breakdown (`1 ≤ ε_ca`, i.e. CS25 Cor 1 / ABF26 Thm 4.17) at a radius
`δ < 1−ρ` where the conjecture's *own* polynomial bound is `< 1` contradicts the conjectured upper
bound on `ε_mca`.

* `CS25BreakdownBelowConjectureBound` — the precise condition: for **every** choice of the
  conjecture's constants there is an RS code + radius with `1 ≤ ε_ca` and conjecture-bound `< 1`.
* `not_mcaConjecture_of_cs25BreakdownBelowBound` — **`CS25BreakdownBelowConjectureBound → ¬ mcaConjecture`**,
  axiom-clean.
* `cs25BreakdownBelowBound_of_breakdownFamily` — reduces that condition to the existing in-repo CS25
  admit `rs_epsCA_breakdown_cs25` together with the *quantitative regime* `bound < 1` (large field,
  entropy band). Hence the only remaining gap to an **unconditional** in-Lean disproof of
  `mcaConjecture` is (a) porting CS25's `ε_ca = 1` lower bound (the `qEntropy ↔ RS-ball-count` bridge,
  flagged as the missing ingredient in `CapacityBounds`) and (b) the regime check `bound < 1`.

**Honest status.** This is *not* an unconditional disproof: the CS25 breakdown (`1 ≤ ε_ca`) is an
external admit, not yet ported. What is proven here, axiom-clean, is that the breakdown — a
literature-established result — **does** refute the conjecture, and exactly what quantitative form it
must take. The earlier `MCAThresholdLedger.candidate_uptocapacity_REFUTED` refutes only the *naive*
constant-bound up-to-capacity form (small-field `constCode`); this reduction targets the genuine
polynomial conjecture.
-/

open scoped NNReal ENNReal

namespace ProximityGap.GrandChallenges

/-- **The precise condition under which CS25's complete-CA-breakdown refutes `mcaConjecture`.**
For EVERY choice of the conjecture's polynomial constants `(c₁,c₂,c₃)` there is a Reed–Solomon code
and a radius `δ < 1 − ρ` at which correlated agreement breaks down (`1 ≤ ε_ca`) while the conjecture's
own bound is `< 1`. -/
def CS25BreakdownBelowConjectureBound : Prop :=
  ∀ c₁ c₂ c₃ : ℝ,
    ∃ (ιC : Type) (_ : Fintype ιC) (_ : Nonempty ιC) (_ : DecidableEq ιC)
      (FC : Type) (_ : Field FC) (_ : Fintype FC) (_ : DecidableEq FC)
      (domain : ιC ↪ FC) (k : ℕ) (δ : ℝ≥0),
      0 < k ∧
      (δ : ℝ) < 1 - (k : ℝ) / Fintype.card ιC ∧
      1 ≤ epsCA (F := FC) (A := FC) ((ReedSolomon.code domain k : Set (ιC → FC))) δ δ ∧
      mcaConjectureBound (Fintype.card ιC) (Fintype.card FC) k δ c₁ c₂ c₃ < 1

/-- **The ABF26 §4.5 MCA conjecture is FALSE given the CS25 breakdown reaches below its bound.**
Since `ε_mca ≥ ε_ca` (`epsCA_le_epsMCA`), a complete CA breakdown (`1 ≤ ε_ca`) at a radius where the
conjecture's polynomial bound is `< 1` immediately contradicts the conjectured upper bound on `ε_mca`.
This reduces the disproof of `mcaConjecture` to the (literature-established) CS25 near-capacity
breakdown in the large-field regime. Axiom-clean. -/
theorem not_mcaConjecture_of_cs25BreakdownBelowBound
    (H : CS25BreakdownBelowConjectureBound) : ¬ mcaConjecture := by
  rintro ⟨c₁, c₂, c₃, hconj⟩
  obtain ⟨ιC, hFι, hNι, hDι, FC, hFld, hFF, hDF, domain, k, δ, hk, hδ, hca, hbnd⟩ := H c₁ c₂ c₃
  letI := hFι; letI := hNι; letI := hDι; letI := hFld; letI := hFF; letI := hDF
  have hge := le_trans hca (epsCA_le_epsMCA _ δ)
  have hle := hconj domain k δ hk hδ
  have hlt : ENNReal.ofReal
      (mcaConjectureBound (Fintype.card ιC) (Fintype.card FC) k δ c₁ c₂ c₃) < 1 :=
    ENNReal.ofReal_lt_one.mpr hbnd
  exact absurd (lt_of_le_of_lt (le_trans hge hle) hlt) (lt_irrefl 1)

/-- Reduce `CS25BreakdownBelowConjectureBound` to the existing in-repo CS25 admit
`rs_epsCA_breakdown_cs25` (which yields `ε_ca = 1` in its entropy band) together with the quantitative
regime hypotheses (`δ < 1−ρ`, `0 < k`, `bound < 1`).  This isolates the remaining gap to an
unconditional disproof: porting CS25's `ε_ca = 1` lower bound plus checking the band sits below the
polynomial bound for a sufficiently large field. -/
theorem cs25BreakdownBelowBound_of_breakdownFamily
    (W : ∀ c₁ c₂ c₃ : ℝ,
        ∃ (ιC : Type) (_ : Fintype ιC) (_ : Nonempty ιC) (_ : DecidableEq ιC)
          (FC : Type) (_ : Field FC) (_ : Fintype FC) (_ : DecidableEq FC)
          (domain : ιC ↪ FC) (k : ℕ) (δ : ℝ≥0),
          0 < k ∧
          (δ : ℝ) < 1 - (k : ℝ) / Fintype.card ιC ∧
          epsCA (F := FC) (A := FC) ((ReedSolomon.code domain k : Set (ιC → FC))) δ δ = 1 ∧
          mcaConjectureBound (Fintype.card ιC) (Fintype.card FC) k δ c₁ c₂ c₃ < 1) :
    CS25BreakdownBelowConjectureBound := by
  intro c₁ c₂ c₃
  obtain ⟨ιC, hFι, hNι, hDι, FC, hFld, hFF, hDF, domain, k, δ, hk, hδ, hca1, hbnd⟩ := W c₁ c₂ c₃
  exact ⟨ιC, hFι, hNι, hDι, FC, hFld, hFF, hDF, domain, k, δ, hk, hδ, hca1.ge, hbnd⟩

end ProximityGap.GrandChallenges
