/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BetaSetYoungDiagram
import ArkLib.Data.CodingTheory.ProximityGap.BorderStrip

/-!
# Rim-hook removal yields a border strip (#389)

The capstone of the geometric James–Kerber bridge: a single abacus bead-move (rim-`n`-hook
removal) `B → B'` produces a skew shape `YD(B) / YD(B')` that is a **border strip** — contained,
`2×2`-free, and connected. We prove the row-length handle on `youngDiagramOfBeta` and then the
border-strip properties.
-/

open YoungDiagram Finset
open ArkLib.ProximityGap.BetaSetYoungDiagram ArkLib.ProximityGap.RimHookArea
open ArkLib.ProximityGap.BorderStrip

namespace ArkLib.ProximityGap.RimHookBorderStrip

variable {B : Finset ℕ} {n : ℕ}

/-- The `i`-th row length of `youngDiagramOfBeta` is the `i`-th part from the top:
`β_{n-1-i} - (n-1-i)` (with `β` the increasing enumeration of `B`). -/
theorem rowLen_youngDiagramOfBeta (h : B.card = n) (i : ℕ) (hi : i < n) :
    (youngDiagramOfBeta h).rowLen i
      = B.orderEmbOfFin h (Fin.rev ⟨i, hi⟩) - (n - 1 - i) := by
  have hlen : (List.ofFn (fun j : Fin n =>
      B.orderEmbOfFin h (Fin.rev j) - ((Fin.rev j : Fin n) : ℕ))).length = n :=
    List.length_ofFn
  have key := rowLen_ofRowLens
    (w := List.ofFn (fun j : Fin n =>
      B.orderEmbOfFin h (Fin.rev j) - ((Fin.rev j : Fin n) : ℕ)))
    (hw := by
      rw [List.sortedGE_ofFn_iff]
      exact (parts_monotone h).comp_antitone Fin.rev_anti)
    ⟨i, by rw [hlen]; exact hi⟩
  rw [youngDiagramOfBeta, key]
  simp only [List.getElem_ofFn, Fin.val_rev, Fin.getElem_fin]
  congr 1
  omega

/-- `μ ≤ ν` for Young diagrams iff every row of `μ` is no longer than the corresponding row of
`ν`. (One direction is `BorderStrip.rowLen_le_of_le`; the converse is membership-by-row.) -/
theorem le_iff_rowLen (μ ν : YoungDiagram) : μ ≤ ν ↔ ∀ i, μ.rowLen i ≤ ν.rowLen i := by
  constructor
  · intro h i; exact rowLen_le_of_le h i
  · intro h
    intro c hc
    obtain ⟨i, j⟩ := c
    rw [mem_iff_lt_rowLen] at hc ⊢
    exact lt_of_lt_of_le hc (h i)

end ArkLib.ProximityGap.RimHookBorderStrip
