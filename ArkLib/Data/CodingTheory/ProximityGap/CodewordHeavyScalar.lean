/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.ExplainableCoreExactCount

/-!
# The codeword heavy-scalar bound: the dual of the line-core partition

Issue #389. `LineCorePartition.lean` showed each `(k+m+1)`-core is explainable for at most one
scalar on the bad-scalar line `w_γ = u₀ + γ·u₁` (when `u₁` is far). This file proves the
**dual** incidence bound, from the side of a fixed codeword:

> **`codeword_heavy_scalar_card_le`** — for a fixed codeword `c` and a **nonvanishing**
> direction `u₁` (every `u₁ i ≠ 0` — true for `u₁ = xᵏ` on a smooth domain), the scalars `γ`
> for which `c` agrees with `w_γ` on at least `a` points number at most `⌊n/a⌋`.

The mechanism is that each domain point `i` agrees with `w_γ` at the **unique** scalar
`γᵢ = (c i − u₀ i)/u₁ i`; so the agreement sets of `c` across the line are the fibers of
`i ↦ γᵢ`, which **partition** the `n` domain points. A scalar can receive a heavy
(`≥ a`) fiber from `c` only `≤ n/a` times.

Together with `line_core_unique_scalar` this pins the full **bipartite incidence** between
codewords and scalars along the line: each core belongs to one scalar, and each codeword
feeds `≤ ⌊n/(k+m+1)⌋` scalars. This is the exact combinatorial skeleton on which any
per-scalar supply bound must rest — the structural content the extremal refutation
(`ExplainableCoreExactCount.lean`) showed combinatorics alone cannot supply, now made
precise from both sides.

## References

* Issue #389; `LineCorePartition.lean` (the core side), `ExplainableCoreExactCount.lean`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset
open scoped NNReal ENNReal

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
/-- The agreement set of a fixed `c` with the line word `w_γ` is the `γ`-fiber of the
pointwise slope `i ↦ (c i − u₀ i)/u₁ i` (when `u₁` is nonvanishing). -/
theorem agreeSet_line_eq_fiber (c u₀ u₁ : Fin n → F) (hu₁ : ∀ i, u₁ i ≠ 0) (γ : F) :
    agreeSet c (fun i => u₀ i + γ • u₁ i)
      = (Finset.univ : Finset (Fin n)).filter (fun i => (c i - u₀ i) / u₁ i = γ) := by
  ext i
  rw [agreeSet, Finset.mem_filter, Finset.mem_filter]
  constructor
  · rintro ⟨-, hi⟩
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [div_eq_iff (hu₁ i), smul_eq_mul] at *
    rw [show c i - u₀ i = γ * u₁ i from by rw [hi]; ring]
  · rintro ⟨-, hi⟩
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [div_eq_iff (hu₁ i)] at hi
    rw [smul_eq_mul, ← hi]; ring

open Classical in
/-- **The codeword heavy-scalar bound.** For a fixed codeword (indeed any word) `c` and a
nonvanishing direction `u₁`, the scalars `γ` whose line word `w_γ = u₀ + γ·u₁` agrees with
`c` on at least `a` points number at most `⌊n/a⌋`. -/
theorem codeword_heavy_scalar_card_le (a : ℕ) (ha : 1 ≤ a)
    (c u₀ u₁ : Fin n → F) (hu₁ : ∀ i, u₁ i ≠ 0) :
    ((Finset.univ : Finset F).filter
        (fun γ => a ≤ (agreeSet c (fun i => u₀ i + γ • u₁ i)).card)).card ≤ n / a := by
  classical
  set f : Fin n → F := fun i => (c i - u₀ i) / u₁ i with hf
  set H : Finset F := (Finset.univ : Finset F).filter
    (fun γ => a ≤ (agreeSet c (fun i => u₀ i + γ • u₁ i)).card) with hH
  -- rewrite the heavy condition in terms of fibers of f
  have hHfib : H = (Finset.univ : Finset F).filter
      (fun γ => a ≤ ((Finset.univ : Finset (Fin n)).filter (fun i => f i = γ)).card) := by
    rw [hH]
    refine Finset.filter_congr fun γ _ => ?_
    rw [agreeSet_line_eq_fiber c u₀ u₁ hu₁ γ]
  -- the fibers of f partition the n domain points
  have hpart : (Finset.univ : Finset (Fin n)).card
      = ∑ γ ∈ (Finset.univ : Finset F),
          ((Finset.univ : Finset (Fin n)).filter (fun i => f i = γ)).card :=
    Finset.card_eq_sum_card_fiberwise (fun i _ => Finset.mem_univ (f i))
  have hn : ∑ γ ∈ (Finset.univ : Finset F),
      ((Finset.univ : Finset (Fin n)).filter (fun i => f i = γ)).card = n := by
    rw [← hpart, Finset.card_univ, Fintype.card_fin]
  -- every γ ∈ H has a heavy fiber
  have hmem : ∀ γ ∈ H, a ≤ ((Finset.univ : Finset (Fin n)).filter
      (fun i => f i = γ)).card := by
    intro γ hγ
    rw [hHfib] at hγ
    exact (Finset.mem_filter.mp hγ).2
  -- |H|·a ≤ Σ_{γ∈H} fiber ≤ Σ_all fiber = n
  have hlb : H.card * a ≤ ∑ γ ∈ H,
      ((Finset.univ : Finset (Fin n)).filter (fun i => f i = γ)).card := by
    calc H.card * a = ∑ _γ ∈ H, a := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ γ ∈ H, ((Finset.univ : Finset (Fin n)).filter (fun i => f i = γ)).card :=
          Finset.sum_le_sum hmem
  have hub : ∑ γ ∈ H,
      ((Finset.univ : Finset (Fin n)).filter (fun i => f i = γ)).card ≤ n :=
    le_trans (Finset.sum_le_sum_of_subset
      (hHfib ▸ Finset.filter_subset _ _)) (le_of_eq hn)
  have hfin : H.card * a ≤ n := le_trans hlb hub
  exact (Nat.le_div_iff_mul_le ha).mpr hfin

/-! ## Source audit -/

#print axioms agreeSet_line_eq_fiber
#print axioms codeword_heavy_scalar_card_le

end ProximityGap.Ownership
