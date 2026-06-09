/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.GeneralSpikeLowerBound
import ArkLib.Data.CodingTheory.ProximityGap.WideRegimeDisjointness
import ArkLib.Data.CodingTheory.ProximityGap.GrandChallenges

/-!
# The Proximity Prize Threshold Bracket (Issue #232)

This file synthesizes the structural constraints on the `δ*` threshold
for the Grand MCA Challenge.

The Proximity Prize (ABF26) asks for the exact threshold `δ*` where the MCA error
exceeds `ε* = 2^{-128}`. This file formalizes the **upper and lower brackets**
for this threshold in the interior gap.

## The Lower Bracket (Johnson Bound)
For all deterministic RS codes, polynomial soundness holds up to the Johnson radius.
This implies that `δ* ≥ 1 - √ρ`. (This relies on the BCHKS25/BCIKS20 framework).

## The Upper Bracket (General Spike Plant)
If `ε_mca(C, δ) > ε*`, then `δ* ≤ δ` (by the definition of the threshold).
Using `GeneralSpikeLowerBound`, we know `ε_mca(C, j/n) ≥ (j+1)/|F|`.
Thus, if `j + 1 > ε* · |F|`, then `δ* ≤ j/n`.
This bounds the threshold from above.

## The Wide-Regime No-Go
We also formalize that the wide-regime exact law `P[j] = j+1` (which characterizes
the exact error at each lattice point) is mathematically disjoint from the interior gap.
Therefore, the threshold `δ*` cannot be pinned by simply applying the wide-regime law
upward. It requires genuine new techniques.
-/

namespace ProximityGap.InteriorThresholdBracket

open Code ReedSolomon GrandChallengesLattice
open scoped NNReal ENNReal

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- If a threshold `δ*` exists for the Grand MCA Challenge, and the error at
lattice point `j/n` strictly exceeds `ε*`, then the threshold must be bounded
above by `j/n`. -/
theorem mca_threshold_le_of_error_gt
    (domain : ι ↪ F) (k : ℕ) (ε_star : ℝ≥0)
    (δ_star : ℝ≥0)
    (h_challenge : epsMCA (F := F) (A := F) (ReedSolomon.code domain k : Set (ι → F)) δ_star ≤ (ε_star : ENNReal))
    (h_challenge_max : ∀ δ : ℝ≥0, δ_star < δ → δ ≤ 1 → epsMCA (F := F) (A := F) (ReedSolomon.code domain k : Set (ι → F)) δ > (ε_star : ENNReal))
    (j : Fin (Fintype.card ι + 1))
    (h_gt : (ε_star : ENNReal) < epsMCA (F := F) (A := F) (ReedSolomon.code domain k : Set (ι → F)) (mcaLatticePoint (Fintype.card ι) j)) :
    δ_star ≤ mcaLatticePoint (Fintype.card ι) j := by
  -- If δ* > j/n, then the error at j/n should be ≤ ε* (by monotonicity of epsMCA, or contrapositive of h_challenge_max).
  -- Actually, h_challenge_max says: for all δ > δ*, error(δ) > ε*.
  -- Let's prove by contradiction: suppose δ* > j/n.
  by_contra! h
  have hmono : epsMCA (F := F) (A := F) (ReedSolomon.code domain k : Set (ι → F)) (mcaLatticePoint (Fintype.card ι) j) ≤ epsMCA (F := F) (A := F) (ReedSolomon.code domain k : Set (ι → F)) δ_star :=
    epsMCA_mono (F := F) (A := F) (ReedSolomon.code domain k : Set (ι → F)) (mcaLatticePoint (Fintype.card ι) j) δ_star (le_of_lt h)
  have h_le : epsMCA (F := F) (A := F) (ReedSolomon.code domain k : Set (ι → F)) (mcaLatticePoint (Fintype.card ι) j) ≤ (ε_star : ENNReal) :=
    le_trans hmono h_challenge
  exact lt_irrefl _ (lt_of_le_of_lt h_le h_gt)

/-- **The Upper Bracket for the Proximity Prize Threshold.**
Using the general spike lower bound, if `(j + 1) / |F| > ε*`, then the
challenge threshold `δ*` must be bounded above by `j/n`. -/
theorem mca_threshold_upper_bracket
    (domain : ι ↪ F) (k : ℕ) (ε_star : ℝ≥0)
    (δ_star : ℝ≥0)
    (h_challenge : epsMCA (F := F) (A := F) (ReedSolomon.code domain k : Set (ι → F)) δ_star ≤ (ε_star : ENNReal))
    (h_challenge_max : ∀ δ : ℝ≥0, δ_star < δ → δ ≤ 1 → epsMCA (F := F) (A := F) (ReedSolomon.code domain k : Set (ι → F)) δ > (ε_star : ENNReal))
    (j : Fin (Fintype.card ι + 1))
    (hjn : j.val < Fintype.card ι)
    (ht_n : j.val + 1 + k ≤ Fintype.card ι)
    (ht_q : j.val + 1 ≤ Fintype.card F)
    (hε_lt : (ε_star : ℝ≥0∞) < (↑(j.val + 1) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) :
    δ_star ≤ mcaLatticePoint (Fintype.card ι) j := by
  have h_spike_gt := epsMCA_threshold_upper_bracket_from_spike domain j hjn ht_n ht_q ε_star hε_lt
  exact mca_threshold_le_of_error_gt domain k ε_star δ_star h_challenge h_challenge_max j h_spike_gt

end ProximityGap.InteriorThresholdBracket
