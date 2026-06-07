/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.NNReal.Basic
import ArkLib.Data.CodingTheory.ListDecodability
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
    It states that for any evaluation domain and rate, there exists a list-size upper bound `ℓ`
    (which depends on `η`) such that any word `w` has at most `ℓ` codewords of the
    rate-`ρ` Reed-Solomon code within relative Hamming distance `RSCapacityRadius ρ η = 1 - ρ - η`.

    The list is `ListDecodable.closeCodewordsRel C w r` (the codewords of `C` in the relative
    Hamming ball of radius `r` around `w`); its `Set.ncard` is the genuine list size.  Replacing
    the former `True` placeholder, this is the real proximity-ball counting statement: it is the
    irreducible open core (capacity-radius list-decodability of Reed-Solomon codes) to which the
    GS prize bound reduces. -/
def RSListDecodingCapacityConjecture
    {ι F : Type} [Field F] [Fintype F] [Fintype ι]
    (domain : ι ↪ F) (ρ η : ℝ≥0) : Prop :=
  ∃ (ℓ : ℕ), ∀ (w : ι → F),
    (ListDecodable.closeCodewordsRel
        ((ReedSolomon.code (domain := domain) ⌊ρ * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F)))
        w (RSCapacityRadius ρ η)).ncard ≤ ℓ

/-- **The per-code capacity conjecture is unconditionally true — and that is exactly why it is
*not* the prize's genuine open core.**

For a *fixed* Reed–Solomon code (`ι`, `F` finite) the close-list `closeCodewordsRel C w r` is a
subset of the finite code `C`, so its `ncard` is bounded by `|C|` for *every* word `w`.  Taking
`ℓ := (RS code).ncard` discharges the existential outright.

The mathematically hard content of [ABF26]'s prize is therefore **not** this per-code statement
(a finiteness triviality) but the *uniform polynomial* bound `epsMCAgs_prizeBound_conjecture` /
`mcaConjectureBound`: a list size that is `poly(n)` with constants `c₁,c₂,c₃` shared across the
whole family of RS codes, up to capacity.  This lemma records that the de-vacuified
`RSListDecodingCapacityConjecture` is satisfiable for free, so any reduction *to it* (e.g.
`epsMCAgsPrizeUniformConjecture`) transfers no real proof debt: the debt lives entirely in the
uniform-constant bound. -/
theorem RSListDecodingCapacityConjecture_holds
    {ι F : Type} [Field F] [Fintype F] [Fintype ι]
    (domain : ι ↪ F) (ρ η : ℝ≥0) :
    RSListDecodingCapacityConjecture domain ρ η := by
  classical
  refine ⟨(ReedSolomon.code (domain := domain)
      ⌊ρ * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F)).ncard, fun w => ?_⟩
  exact Set.ncard_le_ncard (fun c hc => hc.1) (Set.toFinite _)

/-- A list-size bound kernel: if the capacity conjecture holds, we can extract the genuine
list-size bound `ℓ` — every word has at most `ℓ` codewords of the rate-`ρ` RS code within the
capacity radius.  (Previously concluded the vacuous `∃ ℓ, True`; now it exposes the real bound,
which is exactly the conjecture's content.) -/
theorem exists_listSize_bound_of_capacity_conjecture
    {ι F : Type} [Field F] [Fintype F] [Fintype ι]
    (domain : ι ↪ F) (ρ η : ℝ≥0)
    (hConj : RSListDecodingCapacityConjecture domain ρ η) :
    ∃ (ℓ : ℕ), ∀ (w : ι → F),
      (ListDecodable.closeCodewordsRel
          ((ReedSolomon.code (domain := domain) ⌊ρ * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F)))
          w (RSCapacityRadius ρ η)).ncard ≤ ℓ :=
  hConj

end ProximityGap
