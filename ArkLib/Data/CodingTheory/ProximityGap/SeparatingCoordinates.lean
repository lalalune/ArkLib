/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib

/-!
# Few coordinates separate a low-dimensional subspace (issue #389, GG25 §4.3 toward B2)

The deterministic skeleton of the GG25 §4.3 / [KRSW23, Tam24] pruning argument toward
curve-decodability of subspace-design codes: a dimension-`r` subspace `H` of the coordinate space
`(ι → Fin s → F)` is **pinned down by `r` coordinates** — there is a set `S` of at most `r`
coordinates on which the only codeword of `H` that vanishes is `0`:

  `exists_separating_coords` : `∃ S, |S| ≤ r ∧ H ⊓ (⨅ i ∈ S, ker projᵢ) = ⊥`.

Equivalently the restriction map `H → (Fin s → F)^S` is injective. The proof is the standard
peeling induction on `finrank`: while `H ≠ ⊥`, pick a nonzero codeword and a coordinate `i₀` where
it does not vanish; `H ⊓ ker proj_{i₀}` is a *proper* subspace (so `finrank` drops), recurse, and
prepend `i₀`.

Combined with the design property (`SubspaceDesignFullVanish`: at most `τ(r)·n` coordinates fully
vanish on `H`), this is why *randomly* sampled coordinates separate a small subspace with good
probability — the separation mechanism subspace-design list-decoding rests on. Axiom-clean
`[propext, Classical.choice, Quot.sound]`.
-/

open Finset

namespace ProximityGap

variable {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F] {s : ℕ}

/-- **A dimension-`r` subspace is separated by `r` coordinates.** For `H ≤ (ι → Fin s → F)` with
`finrank H ≤ r`, some set `S` of at most `r` coordinates separates `H`: the only `c ∈ H` vanishing
on all of `S` is `0` (`H ⊓ ⨅_{i∈S} ker projᵢ = ⊥`). -/
theorem exists_separating_coords (r : ℕ) (H : Submodule F (ι → Fin s → F))
    (hr : Module.finrank F H ≤ r) :
    ∃ S : Finset ι, S.card ≤ r ∧
      H ⊓ (⨅ i ∈ S, LinearMap.ker
        (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)) = ⊥ := by
  classical
  induction r generalizing H with
  | zero =>
    refine ⟨∅, le_refl _, ?_⟩
    have hH : H = ⊥ := Submodule.finrank_eq_zero.mp (Nat.le_zero.mp hr)
    simp [hH]
  | succ k ih =>
    by_cases hH : H = ⊥
    · exact ⟨∅, Nat.zero_le _, by simp [hH]⟩
    · obtain ⟨c, hcH, hc0⟩ := H.exists_mem_ne_zero_of_ne_bot hH
      obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hc0
      set Ki : Submodule F (ι → Fin s → F) :=
        LinearMap.ker (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i₀) with hKi
      have hlt : H ⊓ Ki < H := by
        refine lt_of_le_of_ne inf_le_left (fun heq => ?_)
        have hcKi : c ∈ Ki := by
          rw [← heq] at hcH; exact (Submodule.mem_inf.mp hcH).2
        rw [hKi, LinearMap.mem_ker, LinearMap.proj_apply] at hcKi
        exact hi₀ hcKi
      have hdrop : Module.finrank F (H ⊓ Ki : Submodule F (ι → Fin s → F)) ≤ k := by
        have : Module.finrank F (H ⊓ Ki : Submodule F (ι → Fin s → F)) < Module.finrank F H :=
          Submodule.finrank_lt_finrank_of_lt hlt
        omega
      obtain ⟨S', hS'card, hS'sep⟩ := ih (H ⊓ Ki) hdrop
      refine ⟨insert i₀ S', (Finset.card_insert_le _ _).trans (Nat.succ_le_succ hS'card), ?_⟩
      rw [Finset.iInf_insert]
      rw [show H ⊓ (Ki ⊓ ⨅ i ∈ S', LinearMap.ker
            (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i))
          = (H ⊓ Ki) ⊓ ⨅ i ∈ S', LinearMap.ker
            (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i) by
        rw [← inf_assoc]]
      exact hS'sep

end ProximityGap

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms ProximityGap.exists_separating_coords
