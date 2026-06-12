/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.WBPencilRationalReduction

/-!
# The below-UDR law from ONE named residual (#371, the WB capstone)

The WB programme's conditional capstone.  `WindowRationalBounded` names the single
remaining input: every doubly-WB-solvable stack has bad-scalar count ≤ `w + 3`.
The probe record behind it: the window adversary EXISTS (max `w+1` at `(13,6,1,2)`,
Möbius-symmetric, exhaustive over the invariant family) but stays well inside the
`w+3` budget; below the ladder reach the genuine-rational and polynomial branches
are PROVEN zero/one (WB-3a/WB-3b).

**`epsMCA_le_below_udr`** — under the Prop, for every radius `δ ≤ w/n` with
`w + k ≤ n`:  `ε_mca(RS, δ) ≤ (w+3)/q`.

At production shape this is `≤ (w+3)/q ≪ 2^{−128}` for every below-UDR radius —
the unconditional-modulo-one-Prop extension of the production floor from the ladder
reach `(1−ρ)/3` to the unique-decoding radius `(1−ρ)/2`.
-/

open Finset
open scoped NNReal ENNReal ProbabilityTheory

namespace ProximityGap.WBPencil

open ProximityGap.SpikeFloor

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
/-- **The named residual of the below-UDR law**: every doubly-WB-solvable stack has
at most `w + 3` bad scalars.  Probe record: window max `w+1` (Möbius-symmetric
extremal); below the ladder reach proven (WB-3a: 0, WB-3b: ≤ 1). -/
def WindowRationalBounded (dom : Fin n ↪ F) (k w : ℕ) (δ : ℝ≥0) : Prop :=
  ∀ u₀ u₁ : Fin n → F, WBSolvable dom k w u₀ → WBSolvable dom k w u₁ →
    (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
      ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ)).card
      ≤ w + 3

open Classical in
/-- **THE BELOW-UDR LAW** (conditional on exactly `WindowRationalBounded`): at every
radius `δ ≤ w/n` below the unique-decoding slack,
`ε_mca(RS, δ) ≤ (w+3)/q`. -/
theorem epsMCA_le_below_udr (dom : Fin n ↪ F) {k w : ℕ} (hk : 1 ≤ k)
    (hwk : w + k ≤ n) {δ : ℝ≥0} (hδn : δ * (Fintype.card (Fin n) : ℝ≥0) ≤ w)
    (hwin : WindowRationalBounded dom k w δ) :
    epsMCA (F := F) (A := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
      ≤ ((w + 3 : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  rw [epsMCA]
  refine iSup_le fun u => ?_
  rw [prob_uniform_eq_card_filter_div_card]
  refine ENNReal.div_le_div_right ?_ _
  by_cases h1 : WBSolvable dom k w (u 1)
  · by_cases h0 : WBSolvable dom k w (u 0)
    · -- doubly rational: the named residual
      exact_mod_cast hwin (u 0) (u 1) h0 h1
    · -- offset row far: swap + pencil
      have hswap := badScalars_card_swap_le
        (rsCode dom k : Submodule F (Fin n → F)) δ (u 0) (u 1)
      have hfar := badScalars_card_le_of_far_snd dom hk hwk hδn
        (u₀ := u 1) (u₁ := u 0) h0
      exact_mod_cast le_trans hswap (by omega)
  · -- direction row far: pencil directly
    have := badScalars_card_le_of_far_snd dom hk hwk hδn
      (u₀ := u 0) (u₁ := u 1) h1
    exact_mod_cast le_trans this (by omega)

open Classical in
/-- The threshold form: under the named residual at every below-UDR radius, the
threshold clears UDR-minus-one-band: `δ* ≥ δ` for every `δ ≤ w/n` with
`(w+3)/q ≤ ε*`.  At production (`ε* = 2^{−128}`, `q ≥ (w+3)·2^{128}`) this moves
the floor to the unique-decoding radius. -/
theorem le_mcaDeltaStar_below_udr (dom : Fin n ↪ F) {k w : ℕ} (hk : 1 ≤ k)
    (hwk : w + k ≤ n) {δ : ℝ≥0} (hδ1 : δ ≤ 1)
    (hδn : δ * (Fintype.card (Fin n) : ℝ≥0) ≤ w)
    (hwin : WindowRationalBounded dom k w δ)
    {εstar : ℝ≥0∞}
    (hbudget : ((w + 3 : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) εstar :=
  ProximityGap.MCAThresholdLedger.le_mcaDeltaStar_of_good _ _ hδ1
    (le_trans (epsMCA_le_below_udr dom hk hwk hδn hwin) hbudget)

end ProximityGap.WBPencil

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.WBPencil.epsMCA_le_below_udr
#print axioms ProximityGap.WBPencil.le_mcaDeltaStar_below_udr
