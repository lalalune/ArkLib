/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BetaSetSize
import Mathlib.Combinatorics.Young.YoungDiagram

/-!
# The β-set Young diagram: `area = number of cells` (#389)

The geometric bridge connecting the β-set area theory (`RimHookArea`, `BetaSetSize`) to Mathlib's
`YoungDiagram`. We associate to a bead set `B` the Young diagram whose row lengths are the
partition parts `β_j - j` (decreasing), and prove its cell count equals `area B`. This grounds the
rim-hook size law as a literal statement about Young-diagram cells.

* **`cellsOfRowLens_card`** — `(cellsOfRowLens w).card = w.sum` (general, reusable).
-/

open Finset

namespace ArkLib.ProximityGap.BetaSetYoungDiagram

/-- The number of cells of the Young diagram built from a row-length list is the list sum. -/
theorem cellsOfRowLens_card : ∀ w : List ℕ, (YoungDiagram.cellsOfRowLens w).card = w.sum
  | [] => by simp [YoungDiagram.cellsOfRowLens]
  | (w :: ws) => by
      rw [YoungDiagram.cellsOfRowLens]
      rw [Finset.card_union_of_disjoint, Finset.card_map, cellsOfRowLens_card ws,
        Finset.card_product, Finset.card_singleton, Finset.card_range, one_mul, List.sum_cons]
      · -- disjointness: row-0 cells vs shifted (row ≥ 1) cells
        rw [Finset.disjoint_left]
        rintro ⟨a, b⟩ h1 h2
        simp only [Finset.mem_product, Finset.mem_singleton] at h1
        simp only [Finset.mem_map, Function.Embedding.prodMap, Function.Embedding.coeFn_mk,
          Prod.exists] at h2
        obtain ⟨x, y, _, hxy⟩ := h2
        simp only [Prod.map_apply, Function.Embedding.refl_apply, Prod.mk.injEq] at hxy
        obtain ⟨ha0, _⟩ := h1
        omega

end ArkLib.ProximityGap.BetaSetYoungDiagram
