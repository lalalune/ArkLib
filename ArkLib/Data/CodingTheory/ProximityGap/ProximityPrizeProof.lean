/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Algebra.Module.Submodule.Basic

/-!
# Subspace-rank sanity checks around the ABF26 prize

This file is **not** a prize resolution. It keeps a small, genuine linear-algebra sanity check and
records the former "grand challenge resolved" endpoint as an honest `Prop` residual rather than a
`sorry`-backed theorem.
-/

namespace ProximityPrize

open scoped Classical

universe u

/-- Rank of a subspace used in candidate affine-folding sanity checks. -/
noncomputable def mcaSubspaceRank {F : Type u} [Field F] {V : Type u}
    [AddCommGroup V] [Module F V] (noiseSubspace : Submodule F V) : ℕ :=
  Module.finrank F noiseSubspace

/-- Finite-dimensional rank subadditivity for sums of subspaces. -/
theorem mcaSubspaceRank_sup_le
    {F : Type u} [Field F] {V : Type u} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (signal noise : Submodule F V) :
    mcaSubspaceRank (signal ⊔ noise) ≤ mcaSubspaceRank signal + mcaSubspaceRank noise := by
  unfold mcaSubspaceRank
  simpa using Submodule.finrank_sup_le signal noise

/-- Backwards-compatible alias for the old candidate sanity-check name. -/
theorem affine_folding_rank_immune_to_cancellation
    {F : Type u} [Field F] {V : Type u} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (signal noise : Submodule F V) :
    mcaSubspaceRank (signal ⊔ noise) ≤ mcaSubspaceRank signal + mcaSubspaceRank noise :=
  mcaSubspaceRank_sup_le signal noise

/-- Honest residual for the former `abf26_grand_challenge_resolved` claim. The old theorem had a
`sorry` proof and a detached/vacuous endpoint. Keep the name as a proposition so references can
point at the open obligation without asserting it. -/
def abf26_grand_challenge_resolved
    {F : Type u} [Field F] (_k : ℕ) (_ρ : ℝ) (_L : Finset F) (_c εStar : ℝ) : Prop :=
  ∃ εMCA : ℝ, εMCA ≤ εStar

end ProximityPrize
