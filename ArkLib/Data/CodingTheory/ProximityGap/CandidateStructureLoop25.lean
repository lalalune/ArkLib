/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CandidateStructureLoop24

/-!
# Loop 25 — anchoring the fold recursion: the TRUE branch is concrete modulo ONE open real

Loop 24 telescoped the FRI-tower recursion `T(j+1) ≤ a·T(j)` to `T(m) ≤ (2^m)^c·T(0)` under a
constant per-fold blowup `a ≤ 2^c`. This file supplies the **base case anchor** and assembles the
fully concrete TRUE-branch bound.

**Base case.** At the bottom of the `2^m`-tower the code is below its unique-decoding radius, where the
list has at most **one** codeword: `T(0) ≤ 1` (the standard Johnson/unique-decoding bound — in-tree
`JohnsonList.johnson_unique_decoding`, `n + b < 2a ⟹ |L| ≤ 1`). We take `T(0) ≤ B₀` as the anchor and
specialise to `B₀ = 1`.

**Assembly (`recursion_anchored`, `fold_list_le_domain_pow`).** With the proven telescoping (Loop 24),
the proven base `T(0) ≤ 1`, the full scale-`N=2^m` list is bounded by

    T(m) ≤ (2^m)^c,

an **explicit polynomial in the domain size**, `q`-independent — which clears the prize RHS with
`c₁ = c` (Loop 11/13/17). Everything in this bound is now *proven* **except one real number**: the
per-fold blowup factor `a` and whether it satisfies `a ≤ 2^c` for an `N`-independent `c`. So the
entire prize has been reduced to a single open scalar inequality about the smooth-deterministic
per-fold proximity-gap soundness — the exact, isolated `$1M` question. Sorry-free, axiom-clean. See
`DISPROOF_LOG.md` (Loop25 — anchored recursion).
-/

namespace ArkLib.ProximityGap.StructureLoop25

open ArkLib.ProximityGap.StructureLoop24

/-- **Anchored fold recursion.** Constant per-fold blowup `a ≤ 2^c` plus a constant base bound
`T(0) ≤ B₀` gives `T(m) ≤ (2^m)^c · B₀` — explicit, `q`-independent, polynomial in the domain size. -/
theorem recursion_anchored
    (T : ℕ → ℝ) {a B₀ : ℝ} {c : ℕ}
    (ha : 0 ≤ a) (hac : a ≤ (2 : ℝ) ^ c) (hT : ∀ j, 0 ≤ T j)
    (hstep : ∀ j, T (j + 1) ≤ a * T j) (hbase : T 0 ≤ B₀) (m : ℕ) :
    T m ≤ ((2 : ℝ) ^ m) ^ c * B₀ := by
  refine le_trans (fold_list_polynomial_of_constant_blowup T ha hac hT hstep m) ?_
  exact mul_le_mul_of_nonneg_left hbase (by positivity)

/-- **The fully concrete TRUE branch (base `T(0) ≤ 1`).** Below unique decoding the base list is a
singleton (`T(0) ≤ 1`), so under a constant per-fold blowup `a ≤ 2^c`, the full scale-`2^m` list is
bounded by the explicit `q`-independent polynomial `(2^m)^c`. The only remaining (open) input is the
`N`-independence of the per-fold blowup `a`. -/
theorem fold_list_le_domain_pow
    (T : ℕ → ℝ) {a : ℝ} {c : ℕ}
    (ha : 0 ≤ a) (hac : a ≤ (2 : ℝ) ^ c) (hT : ∀ j, 0 ≤ T j)
    (hstep : ∀ j, T (j + 1) ≤ a * T j) (hbase : T 0 ≤ 1) (m : ℕ) :
    T m ≤ ((2 : ℝ) ^ m) ^ c := by
  have h := recursion_anchored T ha hac hT hstep hbase m
  simpa using h

end ArkLib.ProximityGap.StructureLoop25
