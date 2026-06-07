/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.RSListDecodingBeyondJohnson
import ArkLib.Data.CodingTheory.ProximityGap.GrandChallenge141PrizeMath

/-!
# The Uniform epsMCAgsPrizeUniformConjecture

This module isolates the reduction from the mathematical open core
(RS list decoding beyond Johnson radius up to capacity) to the
`epsMCAgs_prizeBound_conjecture`. 
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace ProximityGap

open NNReal

/-- The uniform `epsMCAgsPrizeUniformConjecture` asserts that there are uniform
    constants (c₁, c₂, c₃) satisfying the GS prize bound for all rates if the
    list-decoding capacity conjecture holds. -/
def epsMCAgsPrizeUniformConjecture
    {ι F : Type} [Field F] [Fintype F] [Fintype ι]
    (domain : ι ↪ F) (m : ℕ) : Prop :=
  ∀ (j : Fin 4) (η : ℝ≥0),
    RSListDecodingCapacityConjecture domain (ProximityGap.prizeRates j) η →
    epsMCAgs_prizeBound_conjecture domain m

/-- Kernel reduction: A proof that the uniform conjecture follows from
    explicit list-size clearances across all rates and radii.
    (This formalizes the reduction bridge). -/
theorem epsMCAgsPrizeUniformConjecture_of_listSize_clears
    {ι F : Type} [Field F] [Fintype F] [Fintype ι] [DecidableEq F] [DecidableEq ι]
    [Nonempty ι]
    (domain : ι ↪ F) (m : ℕ)
    (ℓ : Fin 4 → ℝ≥0 → ℝ≥0 → (WordStack F (Fin 2) ι → Finset (ι → F)) → ℕ)
    (c₁ c₂ c₃ : ℝ)
    (hcov : ∀ (j : Fin 4) (η δ : ℝ≥0) (hη : 0 < η)
      (hδ : (δ : ℝ) ≤ RSCapacityRadius (ProximityGap.prizeRates j) η)
      (L : WordStack F (Fin 2) ι → Finset (ι → F)) (u : WordStack F (Fin 2) ι),
      PivotCovering (F := F)
        ((Code.ReedSolomon.code (domain := domain)
          ⌊(ProximityGap.prizeRates j : ℝ≥0) * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))) δ L u)
    (hsize : ∀ (j : Fin 4) (η δ : ℝ≥0) (hη : 0 < η)
      (hδ : (δ : ℝ) ≤ RSCapacityRadius (ProximityGap.prizeRates j) η)
      (L : WordStack F (Fin 2) ι → Finset (ι → F)) (u : WordStack F (Fin 2) ι),
      (L u).card ≤ ℓ j η δ L)
    (hclear : ∀ (j : Fin 4) (η δ : ℝ≥0) (hη : 0 < η)
      (hδ : (δ : ℝ) ≤ RSCapacityRadius (ProximityGap.prizeRates j) η)
      (L : WordStack F (Fin 2) ι → Finset (ι → F)),
      ((ℓ j η δ L : ENNReal) / (Fintype.card F : ENNReal)) ≤
        ENNReal.ofReal
          (epsMCAgsPrizeBound (Fintype.card F) m (ProximityGap.prizeRates j) η c₁ c₂ c₃)) :
    epsMCAgsPrizeUniformConjecture domain m := by
  intro j η hConj
  exact epsMCAgs_prizeBound_of_listSize_clears domain m ℓ c₁ c₂ c₃ hcov hsize hclear

end ProximityGap
