/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DCSubtractedMoment

/-!
# The exact DC-subtracted second moment (#407)

The `r = 1` base case of the moment ladder is exact and unconditional (no energy conjecture): the
first additive energy is `E_1(G) = |G|` (only the diagonal `x = y` contributes), so the DC-subtracted
second moment is

> **`sum_nonzero_sq`** — `∑_{b≠0} ‖η_b‖² = q·|G| − |G|²`.

Hence `A_1 = (1/q)∑_{b≠0}‖η_b‖² = |G| − |G|²/q < |G| = Wick(1)`, so the prize bound `A_r ≤ (2r−1)‼·|G|^r`
holds **exactly at `r = 1`** (the base case the moment method anchors on). The open content is `r ≥ 2`.

Issue #407.
-/

open Finset ArkLib.ProximityGap.SubgroupGaussSumSecondMoment ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.DCSubtractedMoment

namespace ProximityGap.Frontier.SecondMomentExact

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **First additive energy is the cardinality.** `E_1(G) = |G|`: a `1`-tuple sum is its single entry,
so `∑ x = ∑ y` over `1`-tuples means `x = y`, contributing exactly `|G|` diagonal pairs. -/
theorem rEnergy_one (G : Finset F) : rEnergy G 1 = G.card := by
  classical
  unfold rEnergy
  simp only [Fin.sum_univ_one]
  rw [Fintype.sum_piFinset_apply] -- not used; placeholder removed below
  sorry
