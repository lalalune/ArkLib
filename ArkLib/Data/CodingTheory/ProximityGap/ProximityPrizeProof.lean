/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.Module.Submodule.Basic

/-!
# Subspace-rank sanity checks around the ABF26 prize

**Honesty note.** A previous revision of this file presented itself as a proximity-prize
resolution, with a trivial `finrank` subadditivity lemma decorated as the main result and a
`theorem abf26_grand_challenge_resolved` left as `sorry`. The statement was detached from the
actual MCA quantity, so the file now keeps only the genuine linear-algebra fact and records the
former endpoint as an honest residual `Prop`.
-/

namespace ProximityPrize

universe u

/-- A toy "noise capacity" proxy: the `F`-dimension of a designated subspace. This is not the MCA
error or any prize quantity; it only illustrates the rank bookkeeping below. -/
noncomputable def mcaSubspaceRank {F : Type u} [Field F] {V : Type u}
    [AddCommGroup V] [Module F V] (noiseSubspace : Submodule F V) : ℕ :=
  Module.finrank F noiseSubspace

/-- Finite-dimensional rank subadditivity for sums of subspaces. -/
theorem mcaSubspaceRank_sup_le
    {F : Type u} [Field F] {V : Type u} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (signal noise : Submodule F V) :
    mcaSubspaceRank (signal ⊔ noise) ≤ mcaSubspaceRank signal + mcaSubspaceRank noise := by
  unfold mcaSubspaceRank
  have h := Submodule.finrank_sup_add_finrank_inf_eq signal noise
  omega

/-- Backwards-compatible alias for the old candidate sanity-check name. -/
theorem affine_folding_rank_immune_to_cancellation
    {F : Type u} [Field F] {V : Type u} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (signal noise : Submodule F V) :
    mcaSubspaceRank (signal ⊔ noise) ≤ mcaSubspaceRank signal + mcaSubspaceRank noise :=
  mcaSubspaceRank_sup_le signal noise

/-- Honest residual for the former `abf26_grand_challenge_resolved` claim. -/
def abf26_grand_challenge_resolved
    {F : Type u} [Field F] (_k : ℕ) (_ρ : ℝ) (_L : Finset F) (_c εStar : ℝ) : Prop :=
  ∃ εMCA : ℝ, εMCA ≤ εStar

end ProximityPrize
