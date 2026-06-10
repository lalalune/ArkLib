/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.GuruswamiSudan.GSCellProduction
import ArkLib.Data.CodingTheory.ProximityGap.Hab25JohnsonNumericBridge

/-!
# The K4 ⟹ `JohnsonNumericBound` seam

One theorem: a uniform K4 pinning input (every decoded cell on a single specialized
irreducible factor obeys the size-`T` bound, for every word stack) plus the closed-form
numeric comparison discharge the `JohnsonNumericBound` residual outright, through the
per-stack numeric count `bad_card_le_numeric` of `GSCellProduction.lean`.

This makes the remaining shape of the #302 Johnson MCA chain a single implication:

  K4 (BCIKS20 Steps 5–7 capture)  ⟹  `JohnsonNumericBound`  ⟹  WHIR pair MCA,

with the second arrow already in-tree (`Hab25WhirBridge.lean`). K4 is proven on the
unique-decoding window (`Hab25CaptureKernelUD.lean`); beyond it, it is the single
remaining deep input.

Axiom-clean: `[propext, Classical.choice, Quot.sound]`.
-/

set_option linter.unusedSectionVars false

namespace CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

open Polynomial Polynomial.Bivariate Finset
open GuruswamiSudan.OverRatFunc
open _root_.ProximityGap Code
open CodingTheory.ProximityGap.Hab25Core.Hab25Johnson
open scoped NNReal ENNReal

attribute [local instance] Classical.propDecidable

variable {F₀ : Type} [Field F₀] [Fintype F₀] [DecidableEq F₀]

/-- **K4 ⟹ `JohnsonNumericBound`.** A uniform K4 pinning input over all word stacks,
plus the numeric comparison for `N = (D/(k−1)+1)·T`, discharge the Hab25 numeric
residual through the per-stack count `bad_card_le_numeric`. -/
theorem johnsonNumericBound_of_K4 {n k m : ℕ} [NeZero n] (domain : Fin n ↪ F₀)
    (η δ : ℝ≥0) (T : ℕ)
    (hk1 : 1 < k) (hkn : k + 1 ≤ n) (hm : 1 ≤ m)
    (hδ1 : δ ≤ 1) (hδJ : (δ : ℝ) < gs_johnson k n m)
    (hT0 : n * (GuruswamiSudan.constraintIndices m).card * gs_degree_bound k n m ≤ T)
    (hK4 : ∀ (u : WordStack F₀ (Fin 2) (Fin n)) (E : Finset F₀) (P : F₀ → F₀[X])
      (R : (F₀[X])[X][Y]),
      Irreducible R →
      (∀ γ ∈ E, ∃ d : McaDecode domain k δ u γ, d.P = P γ) →
      (∀ γ ∈ E, (Polynomial.X - Polynomial.C (P γ)) ∣
        R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ))) →
      E.card ≤ T)
    (hNdiv : (((gs_degree_bound k n m / (k - 1) + 1) * T : ℕ) : ℝ) /
        (Fintype.card F₀ : ℝ) ≤ johnsonBoundReal domain k η δ) :
    JohnsonNumericBound domain k η δ :=
  JohnsonNumericBound.of_card_le_nat domain k η δ
    ((gs_degree_bound k n m / (k - 1) + 1) * T) hNdiv
    (fun u => bad_card_le_numeric domain u δ T hk1 hkn hm hδ1 hδJ hT0 (hK4 u))

end CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

/-! ## Axiom audit — kernel-clean. -/
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.johnsonNumericBound_of_K4
