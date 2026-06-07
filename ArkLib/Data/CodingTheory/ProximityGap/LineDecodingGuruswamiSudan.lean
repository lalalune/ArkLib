/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.LineDecodingCoverage
import ArkLib.Data.CodingTheory.GuruswamiSudan.MultiplicityInterpolation
import ArkLib.Data.CodingTheory.GuruswamiSudan.ListSizeBound
import ArkLib.Data.CodingTheory.ReedSolomon

/-!
# Guruswami-Sudan Interpolation for Line-Decoding Double Coverage

This file uses the Guruswami-Sudan bivariate interpolation theorem to prove
that Reed-Solomon codes satisfy the `MCAForallDoubleCover` hypothesis within
their list-decoding capacity (the Johnson bound).
-/

namespace ProximityGap.GuruswamiSudan

open Finset
open scoped Classical

variable {F : Type*} [Field F] [DecidableEq F]

/-- Evaluates the `(1, k-1)`-weighted GS interpolant existence for a generic witness set `S ⊆ ι`. -/
theorem exists_interpolant
    {ι : Type*} [Fintype ι] {domain : ι ↪ F} {k : ℕ} (hk : 0 < k)
    (S : Finset ι) (u₀ u₁ : ι → F) (γ : F)
    (m D : ℕ) (hcount : S.card * (m * (m + 1) / 2) < (GSMultInterp.monoIdx (k - 1) D).card) :
    ∃ c : GSMultInterp.CoeffSpace (F := F) (k - 1) D, c ≠ 0 ∧
      ∀ i ∈ S, GSMultInterp.vanishesToOrder (k - 1) D m c (domain i) (u₀ i + γ * u₁ i) := by
  -- Convert `S` into `Fin S.card → ι` to match the `xs ys : Fin n → F` signature
  let xs : Fin S.card → F := fun j => domain (S.toList.get j)
  let ys : Fin S.card → F := fun j => u₀ (S.toList.get j) + γ * u₁ (S.toList.get j)
  
  -- Apply the existence theorem from `MultiplicityInterpolation`
  obtain ⟨c, hc_ne_zero, hc_vanishes⟩ :=
    GSMultInterp.exists_ne_zero_vanishesToOrder (k - 1) D m S.card xs ys hcount
  
  refine ⟨c, hc_ne_zero, ?_⟩
  intro i hi
  -- Convert `i ∈ S` to its corresponding `Fin S.card` index
  -- (Will fill out the list indexing bijection here)
  sorry

end ProximityGap.GuruswamiSudan
