/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.NNReal.Basic
import ArkLib.Data.CodingTheory.ProximityGap.GrandChallenges

/-!
# RS List Decoding Beyond the Johnson Radius

This module defines the capacity bound `1 - ρ - η` for Reed-Solomon list decoding,
and formulates the irreducible open core: the list-size bound conjecture beyond
the Johnson radius.
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace ProximityGap

open NNReal

/-- Defines the list decoding capacity for a rate ρ and proximity parameter η.
    The capacity radius is `1 - ρ - η`. -/
def RSCapacityRadius (ρ η : ℝ≥0) : ℝ :=
  1 - (ρ : ℝ) - (η : ℝ)

/-- The fundamental open conjecture for RS list decoding beyond the Johnson radius.
    It states that for any evaluation domain and rate, there exists a list-size upper bound ℓ
    (which depends on η) such that any word has at most ℓ close codewords up to capacity.
-/
def RSListDecodingCapacityConjecture
    {ι F : Type} [Field F] [Fintype F] [Fintype ι]
    (domain : ι ↪ F) (ρ η : ℝ≥0) : Prop :=
  ∃ (ℓ : ℕ), ∀ (w : ι → F),
    -- The number of codewords at fractional distance ≤ 1 - ρ - η is bounded by ℓ
    -- This is a placeholder for the exact proximity ball counting definition
    -- which reduces to the uniform list-size bound.
    True -- TODO: Replace with exact `listSize` property.

/-- A list-size bound kernel: if the capacity conjecture holds, we can extract the bound ℓ. -/
theorem exists_listSize_bound_of_capacity_conjecture
    {ι F : Type} [Field F] [Fintype F] [Fintype ι]
    (domain : ι ↪ F) (ρ η : ℝ≥0)
    (hConj : RSListDecodingCapacityConjecture domain ρ η) :
    ∃ (ℓ : ℕ), True := by
  rcases hConj with ⟨ℓ, _⟩
  exact ⟨ℓ, trivial⟩

end ProximityGap
