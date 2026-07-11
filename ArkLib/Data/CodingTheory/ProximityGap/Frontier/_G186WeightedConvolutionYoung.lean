/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G185CanonicalWeightedCompression

/-!
# G186: Young bound for the doubled weighted convolution

The G185 weighted profile is the convolution of the doubled-set counting measure with the ordinary
`s`-fold sum profile.  Finite Cauchy--Schwarz and translation invariance give

`sum_t B_s(t)^2 <= |G|^2 * addREnergy(s,G)`.

This connects the repetition-defect route back to the existing all-depth additive-energy ladder.

Issue #466.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G186WeightedConvolutionYoung

open scoped BigOperators
open ArkLib.ProximityGap.Frontier.G171ShiftedREnergyAutocorrelation

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

noncomputable def doubledConvolutionCount (G : Finset F) (s : ℕ) (t : F) : ℕ :=
  ∑ x ∈ G, rSumCount G s (t - (x + x))

theorem sum_rSumCount_shift_sq (G : Finset F) (s : ℕ) (c : F) :
    ∑ t : F, ((rSumCount G s (t - c) : ℕ) : ℝ) ^ 2 =
      ∑ t : F, ((rSumCount G s t : ℕ) : ℝ) ^ 2 := by
  exact Fintype.sum_equiv (Equiv.subRight c) _ _ fun _ => rfl

theorem doubledConvolutionCount_sq_le (G : Finset F) (s : ℕ) (t : F) :
    (doubledConvolutionCount G s t : ℝ) ^ 2 ≤
      (G.card : ℝ) * ∑ x ∈ G, ((rSumCount G s (t - (x + x)) : ℕ) : ℝ) ^ 2 := by
  unfold doubledConvolutionCount
  rw [Nat.cast_sum]
  exact sq_sum_le_card_mul_sum_sq
    (s := G) (f := fun x => ((rSumCount G s (t - (x + x)) : ℕ) : ℝ))

/-- **Weighted-convolution Young inequality.** -/
theorem doubledConvolution_energy_le (G : Finset F) (s : ℕ) :
    ∑ t : F, (doubledConvolutionCount G s t : ℝ) ^ 2 ≤
      (G.card : ℝ) ^ 2 * Finset.addREnergy s G := by
  calc
    ∑ t : F, (doubledConvolutionCount G s t : ℝ) ^ 2 ≤
        ∑ t : F, (G.card : ℝ) *
          ∑ x ∈ G, ((rSumCount G s (t - (x + x)) : ℕ) : ℝ) ^ 2 := by
      exact Finset.sum_le_sum fun t _ => doubledConvolutionCount_sq_le G s t
    _ = (G.card : ℝ) * ∑ x ∈ G,
        ∑ t : F, ((rSumCount G s (t - (x + x)) : ℕ) : ℝ) ^ 2 := by
      rw [← Finset.mul_sum]
      congr 1
      rw [Finset.sum_comm]
    _ = (G.card : ℝ) * ∑ _x ∈ G,
        ∑ t : F, ((rSumCount G s t : ℕ) : ℝ) ^ 2 := by
      apply congrArg
      apply Finset.sum_congr rfl
      intro x hx
      exact sum_rSumCount_shift_sq G s (x + x)
    _ = (G.card : ℝ) ^ 2 * Finset.addREnergy s G := by
      rw [addREnergy_eq_sum_rSumCount_sq]
      push_cast
      simp
      ring

#print axioms sum_rSumCount_shift_sq
#print axioms doubledConvolutionCount_sq_le
#print axioms doubledConvolution_energy_le

end ArkLib.ProximityGap.Frontier.G186WeightedConvolutionYoung
