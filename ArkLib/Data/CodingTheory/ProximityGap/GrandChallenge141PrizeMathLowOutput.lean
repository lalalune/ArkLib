/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.GrandChallenge141PrizeMath

/-!
# Low-output Grand Challenge 1 prize wrappers

This companion module keeps the long `GrandChallenge141PrizeMath.lean` file stable while exposing
weaker consumers of its concrete-threshold bracket packages. The uniform GS prize hypothesis remains
explicit throughout; these declarations only forget threshold-equality and satisfy/maximality
payloads from already-proved wrappers.
-/

namespace ProximityGap

open NNReal Code
open scoped ProbabilityTheory BigOperators

namespace MCAGS

section PerInput

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

open scoped NNReal

/-- The all-rate uniform GS threshold package resolves the faithful prize lattice and preserves
only the lower lattice brackets.

This is the low-output projection of
`mcaPrizeLatticeResolved_with_threshold_and_lower_brackets_prize_allRates_of_uniformConjecture`:
it drops the concrete `τ j = mcaThreshold ...` witnesses while retaining the resolved lattice and
lower bounds. -/
theorem mcaPrizeLatticeResolved_with_lower_brackets_prize_allRates_of_uniformConjecture
    (domain : ι ↪ F) (m : ℕ)
    (hUniform : epsMCAgsPrizeUniformConjecture domain m) :
    ∃ c₁ c₂ c₃ : ℝ,
      ∀ (η δ : Fin 4 → ℝ≥0),
        (∀ j : Fin 4, 0 < η j) →
        (∀ j : Fin 4,
          (δ j : ℝ) ≤ 1 - (ProximityGap.prizeRates j : ℝ) - (η j : ℝ)) →
        (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1) →
        ∀ L : ∀ _ : Fin 4, WordStack F (Fin 2) ι → Finset (ι → F),
          (∀ j : Fin 4,
            FaithfulGSFamily (F := F)
              ((ReedSolomon.code (domain := domain)
                ⌊(ProximityGap.prizeRates j : ℝ≥0) * (Fintype.card ι : ℝ≥0)⌋₊ :
                  Set (ι → F))) (δ j) (L j)) →
          (∀ j : Fin 4,
            ENNReal.ofReal
                (epsMCAgsPrizeBound (Fintype.card F) m (ProximityGap.prizeRates j)
                  (η j) c₁ c₂ c₃)
              ≤ (epsStar : ENNReal)) →
          ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
            GrandChallengesLattice.mcaPrizeLatticeResolved domain τ ∧
              ∀ j : Fin 4,
                GrandChallengesLattice.latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤
                  τ j := by
  rcases
      mcaPrizeLatticeResolved_with_threshold_and_lower_brackets_prize_allRates_of_uniformConjecture
        domain m hUniform with
    ⟨c₁, c₂, c₃, hresolved⟩
  refine ⟨c₁, c₂, c₃, ?_⟩
  intro η δ hη hδ hδ_le_one L hfaithful hclear
  rcases hresolved η δ hη hδ hδ_le_one L hfaithful hclear with
    ⟨τ, hτ, hbrackets⟩
  refine ⟨τ, hτ, ?_⟩
  intro j
  rcases hbrackets j with ⟨_hne, _hτeq, hlower⟩
  exact hlower

/-- The all-rate uniform GS two-bracket package resolves the faithful prize lattice and preserves
only the lower and upper lattice brackets.

This is the low-output projection of
`mcaPrizeLatticeResolved_with_threshold_and_brackets_prize_allRates_of_uniformConjecture`: it drops
the concrete threshold-equality witnesses while retaining the resolved lattice and the two-sided
bracket data. -/
theorem mcaPrizeLatticeResolved_with_brackets_prize_allRates_of_uniformConjecture
    (domain : ι ↪ F) (m : ℕ)
    (hUniform : epsMCAgsPrizeUniformConjecture domain m) :
    ∃ c₁ c₂ c₃ : ℝ,
      ∀ (η δ : Fin 4 → ℝ≥0),
        (∀ j : Fin 4, 0 < η j) →
        (∀ j : Fin 4,
          (δ j : ℝ) ≤ 1 - (ProximityGap.prizeRates j : ℝ) - (η j : ℝ)) →
        (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1) →
        ∀ L : ∀ _ : Fin 4, WordStack F (Fin 2) ι → Finset (ι → F),
          (∀ j : Fin 4,
            FaithfulGSFamily (F := F)
              ((ReedSolomon.code (domain := domain)
                ⌊(ProximityGap.prizeRates j : ℝ≥0) * (Fintype.card ι : ℝ≥0)⌋₊ :
                  Set (ι → F))) (δ j) (L j)) →
          (∀ j : Fin 4,
            ENNReal.ofReal
                (epsMCAgsPrizeBound (Fintype.card F) m (ProximityGap.prizeRates j)
                  (η j) c₁ c₂ c₃)
              ≤ (epsStar : ENNReal)) →
          (whi : ∀ j : Fin 4,
            GrandChallenges.MCAUpperWitness
              ((ReedSolomon.code (domain := domain)
                ⌊(ProximityGap.prizeRates j : ℝ≥0) * (Fintype.card ι : ℝ≥0)⌋₊ :
                  Set (ι → F))) epsStar) →
          (hδhi : ∀ j : Fin 4, (whi j).δ ≤ 1) →
          ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
            GrandChallengesLattice.mcaPrizeLatticeResolved domain τ ∧
              (∀ j : Fin 4,
                GrandChallengesLattice.latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤
                  τ j) ∧
                ∀ j : Fin 4,
                  τ j <
                    GrandChallengesLattice.latticeIndexOf (ι := ι) (whi j).δ (hδhi j) := by
  rcases
      mcaPrizeLatticeResolved_with_threshold_and_brackets_prize_allRates_of_uniformConjecture
        domain m hUniform with
    ⟨c₁, c₂, c₃, hresolved⟩
  refine ⟨c₁, c₂, c₃, ?_⟩
  intro η δ hη hδ hδ_le_one L hfaithful hclear whi hδhi
  rcases hresolved η δ hη hδ hδ_le_one L hfaithful hclear whi hδhi with
    ⟨τ, hτ, hbrackets⟩
  refine ⟨τ, hτ, ?_, ?_⟩
  · intro j
    rcases hbrackets j with ⟨_hne, _hτeq, hlower, _hupper⟩
    exact hlower
  · intro j
    rcases hbrackets j with ⟨_hne, _hτeq, _hlower, hupper⟩
    exact hupper

/-- The uniform GS selected-threshold package resolves the faithful prize lattice and preserves
only the lower lattice brackets.

This is the low-output projection of
`exists_mcaPrizeLatticeResolved_with_spec_and_lower_brackets_of_uniformConjecture`: it drops the
selected-threshold satisfy/maximality spec while retaining the resolved lattice and lower bounds. -/
theorem exists_mcaPrizeLatticeResolved_with_lower_brackets_of_uniformConjecture
    (domain : ι ↪ F) (m : ℕ)
    (hUniform : epsMCAgsPrizeUniformConjecture domain m) :
    ∃ c₁ c₂ c₃ : ℝ,
      ∀ (η δ : Fin 4 → ℝ≥0),
        (∀ j : Fin 4, 0 < η j) →
        (∀ j : Fin 4,
          (δ j : ℝ) ≤ 1 - (ProximityGap.prizeRates j : ℝ) - (η j : ℝ)) →
        (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1) →
        ∀ L : ∀ _ : Fin 4, WordStack F (Fin 2) ι → Finset (ι → F),
          (∀ j : Fin 4,
            FaithfulGSFamily (F := F)
              ((ReedSolomon.code (domain := domain)
                ⌊(ProximityGap.prizeRates j : ℝ≥0) * (Fintype.card ι : ℝ≥0)⌋₊ :
                  Set (ι → F))) (δ j) (L j)) →
          (∀ j : Fin 4,
            ENNReal.ofReal
                (epsMCAgsPrizeBound (Fintype.card F) m (ProximityGap.prizeRates j)
                  (η j) c₁ c₂ c₃)
              ≤ (epsStar : ENNReal)) →
          ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
            GrandChallengesLattice.mcaPrizeLatticeResolved domain τ ∧
              ∀ j : Fin 4,
                GrandChallengesLattice.latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤
                  τ j := by
  rcases exists_mcaPrizeLatticeResolved_with_spec_and_lower_brackets_of_uniformConjecture
      domain m hUniform with ⟨c₁, c₂, c₃, hresolved⟩
  refine ⟨c₁, c₂, c₃, ?_⟩
  intro η δ hη hδ hδ_le_one L hfaithful hclear
  rcases hresolved η δ hη hδ hδ_le_one L hfaithful hclear with
    ⟨τ, hτ, _hspec, hlower⟩
  exact ⟨τ, hτ, hlower⟩

/-- The uniform GS selected-threshold two-bracket package resolves the faithful prize lattice and
preserves only the lower and upper lattice brackets.

This is the low-output projection of
`exists_mcaPrizeLatticeResolved_with_spec_and_brackets_of_uniformConjecture`: it drops the
selected-threshold satisfy/maximality spec while retaining the resolved lattice and two-sided
bracket data. -/
theorem exists_mcaPrizeLatticeResolved_with_brackets_of_uniformConjecture
    (domain : ι ↪ F) (m : ℕ)
    (hUniform : epsMCAgsPrizeUniformConjecture domain m) :
    ∃ c₁ c₂ c₃ : ℝ,
      ∀ (η δ : Fin 4 → ℝ≥0),
        (∀ j : Fin 4, 0 < η j) →
        (∀ j : Fin 4,
          (δ j : ℝ) ≤ 1 - (ProximityGap.prizeRates j : ℝ) - (η j : ℝ)) →
        (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1) →
        ∀ L : ∀ _ : Fin 4, WordStack F (Fin 2) ι → Finset (ι → F),
          (∀ j : Fin 4,
            FaithfulGSFamily (F := F)
              ((ReedSolomon.code (domain := domain)
                ⌊(ProximityGap.prizeRates j : ℝ≥0) * (Fintype.card ι : ℝ≥0)⌋₊ :
                  Set (ι → F))) (δ j) (L j)) →
          (∀ j : Fin 4,
            ENNReal.ofReal
                (epsMCAgsPrizeBound (Fintype.card F) m (ProximityGap.prizeRates j)
                  (η j) c₁ c₂ c₃)
              ≤ (epsStar : ENNReal)) →
          (whi : ∀ j : Fin 4,
            GrandChallenges.MCAUpperWitness
              ((ReedSolomon.code (domain := domain)
                ⌊(ProximityGap.prizeRates j : ℝ≥0) * (Fintype.card ι : ℝ≥0)⌋₊ :
                  Set (ι → F))) epsStar) →
          (hδhi : ∀ j : Fin 4, (whi j).δ ≤ 1) →
          ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
            GrandChallengesLattice.mcaPrizeLatticeResolved domain τ ∧
              (∀ j : Fin 4,
                GrandChallengesLattice.latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤
                  τ j) ∧
                ∀ j : Fin 4,
                  τ j <
                    GrandChallengesLattice.latticeIndexOf (ι := ι) (whi j).δ (hδhi j) := by
  rcases exists_mcaPrizeLatticeResolved_with_spec_and_brackets_of_uniformConjecture
      domain m hUniform with ⟨c₁, c₂, c₃, hresolved⟩
  refine ⟨c₁, c₂, c₃, ?_⟩
  intro η δ hη hδ hδ_le_one L hfaithful hclear whi hδhi
  rcases hresolved η δ hη hδ hδ_le_one L hfaithful hclear whi hδhi with
    ⟨τ, hτ, _hspec, hlower, hupper⟩
  exact ⟨τ, hτ, hlower, hupper⟩

end PerInput

/-! ## Source audit -/

set_option linter.style.longLine false in
#print axioms mcaPrizeLatticeResolved_with_lower_brackets_prize_allRates_of_uniformConjecture
set_option linter.style.longLine false in
#print axioms mcaPrizeLatticeResolved_with_brackets_prize_allRates_of_uniformConjecture
set_option linter.style.longLine false in
#print axioms exists_mcaPrizeLatticeResolved_with_lower_brackets_of_uniformConjecture
set_option linter.style.longLine false in
#print axioms exists_mcaPrizeLatticeResolved_with_brackets_of_uniformConjecture

end MCAGS

end ProximityGap
