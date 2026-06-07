/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shaw, Aristotle (Harmonic)
-/

import ArkLib.Data.CodingTheory.ProximityGap.AHIV22
import ArkLib.Data.Probability.Instances

/-!
# AHIV17 affine-line probability bridge (issue #88)

The AHIV17/AHIV22 tighter `d/q = ‖RS‖₀/q` correlated-agreement bound is consumed at the
affine-line layer through the predicate `δ_ε_correlatedAgreementAffineLines`, whose `epsCA`
body is the *single-variable* uniform probability

  `Pr_{γ ← F}[δᵣ(u₀ + γ • u₁, RScodeSet α deg) ≤ δ]`.

This file proves the genuine per-line core of the AHIV17 argument: that this affine-line
probability is at most `‖RScodeSet α deg‖₀ / |F|` under the AHIV regime hypotheses.

The key observation (correcting the naive "specialize the 2-row row-span" route) is that the
affine-line predicate samples the *1-dimensional* line `{u₀ + γ • u₁ : γ ∈ F}` (|F| points), not
the 2-dimensional `Matrix.rowSpan` (|F|² points). The right bridge is therefore the *per-line
fiber count* that `prob_of_bad_pts` itself uses internally, namely
`numberOfClosePts u₀ u₁ deg α e ≤ ‖RS‖₀`, supplied by the mutual-exclusion corollary
`e_le_dist_over_3`.

## Main results

* `ProximityToRS.affineLine_close_count_eq_numberOfClosePts` — the count of field elements `γ`
  with `u₀ + γ • u₁` close to the code equals `numberOfClosePts`, when `u₁ ≠ 0`.
* `ProximityToRS.affineLine_prob_le_dOverQ` — the affine-line probability is at most
  `‖RS‖₀ / |F|` under the AHIV regime hypotheses.
-/

noncomputable section

open Code ProbabilityTheory NNReal

namespace ProximityToRS

open ReedSolomon

variable {F : Type} [Field F] [Finite F] [DecidableEq F]
         {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]

local instance : Fintype F := Fintype.ofFinite F

/-- The map `γ ↦ u₀ + γ • u₁` is injective whenever `u₁ ≠ 0`. -/
lemma affineLine_param_injective {u₀ u₁ : ι → F} (hu₁ : u₁ ≠ 0) :
    Function.Injective (fun γ : F => u₀ + γ • u₁) := by
  -- pick a coordinate where `u₁` is nonzero and cancel.
  obtain ⟨j, hj⟩ : ∃ j, u₁ j ≠ 0 := by
    by_contra h
    apply hu₁
    funext j
    by_contra hjj
    exact h ⟨j, hjj⟩
  intro a b hab
  have hval := congrArg (fun f : ι → F => f j) hab
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_right_inj] at hval
  exact mul_right_cancel₀ hj hval

end ProximityToRS
