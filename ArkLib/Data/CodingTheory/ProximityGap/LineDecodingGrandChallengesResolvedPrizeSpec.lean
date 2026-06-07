/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.LineDecodingGrandChallengesPrizeSpec

/-!
# Resolved selected-threshold prize specifications for repaired line-decoding data

This module packages the selected-threshold bracket wrappers from
`LineDecodingGrandChallengesPrizeSpec` with the faithful MCA lattice-resolution predicate.
-/

namespace ProximityGap

open scoped NNReal

namespace GrandChallengesLattice

open GrandChallenges

section LineDecodingResolvedPrizeSpec

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

private theorem exists_mcaPrizeLatticeResolved_with_spec_and_lower_brackets_of_spec_and_lower
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (h : ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
      (∀ j : Fin 4,
        let C : Set (ι → F) :=
          ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
        ∃ _ : mcaThresholdExists C epsStar,
          mcaSatisfies C epsStar (τ j) ∧
            ∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C epsStar i → i ≤ τ j) ∧
        ∀ j : Fin 4,
          latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤ τ j) :
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
      mcaPrizeLatticeResolved domain τ ∧
        (∀ j : Fin 4,
          let C : Set (ι → F) :=
            ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
          ∃ _ : mcaThresholdExists C epsStar,
            mcaSatisfies C epsStar (τ j) ∧
              ∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C epsStar i → i ≤ τ j) ∧
          ∀ j : Fin 4,
            latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤ τ j := by
  rcases h with ⟨τ, hspec, hlower⟩
  exact ⟨τ, (mcaPrizeLatticeResolved_iff domain τ).mpr hspec, hspec, hlower⟩

private theorem exists_mcaPrizeLatticeResolved_with_spec_and_brackets_of_spec_and_brackets
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (whi : ∀ j : Fin 4,
      GrandChallenges.MCAUpperWitness
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar)
    (hδhi : ∀ j : Fin 4, (whi j).δ ≤ 1)
    (h : ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
      (∀ j : Fin 4,
        let C : Set (ι → F) :=
          ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
        ∃ _ : mcaThresholdExists C epsStar,
          mcaSatisfies C epsStar (τ j) ∧
            ∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C epsStar i → i ≤ τ j) ∧
        (∀ j : Fin 4,
          latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤ τ j) ∧
          ∀ j : Fin 4, τ j < latticeIndexOf (ι := ι) (whi j).δ (hδhi j)) :
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
      mcaPrizeLatticeResolved domain τ ∧
        (∀ j : Fin 4,
          let C : Set (ι → F) :=
            ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
          ∃ _ : mcaThresholdExists C epsStar,
            mcaSatisfies C epsStar (τ j) ∧
              ∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C epsStar i → i ≤ τ j) ∧
          (∀ j : Fin 4,
            latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤ τ j) ∧
            ∀ j : Fin 4, τ j < latticeIndexOf (ι := ι) (whi j).δ (hδhi j) := by
  rcases h with ⟨τ, hspec, hlower, hupper⟩
  exact ⟨τ, (mcaPrizeLatticeResolved_iff domain τ).mpr hspec, hspec, hlower, hupper⟩

/-- Repaired double-cover data supplies a selected-threshold lattice resolution, the exact
threshold specification, and lower lattice brackets. -/
theorem exists_mcaPrizeLatticeResolved_with_spec_and_lower_brackets_ofDoubleCover
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hcov : ∀ j : Fin 4, MCAForallDoubleCover (F := F) (A := F)
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      (δ j)) :
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
      mcaPrizeLatticeResolved domain τ ∧
        (∀ j : Fin 4,
          let C : Set (ι → F) :=
            ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
          ∃ _ : mcaThresholdExists C epsStar,
            mcaSatisfies C epsStar (τ j) ∧
              ∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C epsStar i → i ≤ τ j) ∧
          ∀ j : Fin 4,
            latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤ τ j :=
  exists_mcaPrizeLatticeResolved_with_spec_and_lower_brackets_of_spec_and_lower
    domain δ hδ_le_one <|
      exists_mcaPrizeLatticeSpec_and_lower_brackets_ofDoubleCover
        domain δ hδ_le_one hcov

/-- Named bad-scalar double-cover obligations supply a selected-threshold lattice resolution, the
exact threshold specification, and lower lattice brackets. -/
theorem exists_mcaPrizeLatticeResolved_with_spec_and_lower_brackets_ofBadScalarDoubleCover
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hcov : ∀ j : Fin 4, ∀ (u : Code.WordStack F (Fin 2) ι) (γ : F),
      MCABadScalarDoubleCover (F := F) (A := F)
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) (u 0) (u 1) γ) :
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
      mcaPrizeLatticeResolved domain τ ∧
        (∀ j : Fin 4,
          let C : Set (ι → F) :=
            ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
          ∃ _ : mcaThresholdExists C epsStar,
            mcaSatisfies C epsStar (τ j) ∧
              ∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C epsStar i → i ≤ τ j) ∧
          ∀ j : Fin 4,
            latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤ τ j :=
  exists_mcaPrizeLatticeResolved_with_spec_and_lower_brackets_of_spec_and_lower
    domain δ hδ_le_one <|
      exists_mcaPrizeLatticeSpec_and_lower_brackets_ofBadScalarDoubleCover
        domain δ hδ_le_one hcov

/-- Zero bad-scalar counts supply a selected-threshold lattice resolution, the exact threshold
specification, and lower lattice brackets. -/
theorem exists_mcaPrizeLatticeResolved_with_spec_and_lower_brackets_of_mcaBadCount_zero
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hzero : ∀ j : Fin 4, ∀ u : Code.WordStack F (Fin 2) ι,
      mcaBadCount (F := F) (A := F)
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) (u 0) (u 1) = 0) :
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
      mcaPrizeLatticeResolved domain τ ∧
        (∀ j : Fin 4,
          let C : Set (ι → F) :=
            ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
          ∃ _ : mcaThresholdExists C epsStar,
            mcaSatisfies C epsStar (τ j) ∧
              ∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C epsStar i → i ≤ τ j) ∧
          ∀ j : Fin 4,
            latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤ τ j :=
  exists_mcaPrizeLatticeResolved_with_spec_and_lower_brackets_of_spec_and_lower
    domain δ hδ_le_one <|
      exists_mcaPrizeLatticeSpec_and_lower_brackets_of_mcaBadCount_zero
        domain δ hδ_le_one hzero

/-- Direct no-bad-event frontiers supply a selected-threshold lattice resolution, the exact
threshold specification, and lower lattice brackets. -/
theorem exists_mcaPrizeLatticeResolved_with_spec_and_lower_brackets_of_forall_not_mcaEvent
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hno : ∀ j : Fin 4, ∀ (u : Code.WordStack F (Fin 2) ι) (γ : F),
      ¬ mcaEvent (F := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) (u 0) (u 1) γ) :
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
      mcaPrizeLatticeResolved domain τ ∧
        (∀ j : Fin 4,
          let C : Set (ι → F) :=
            ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
          ∃ _ : mcaThresholdExists C epsStar,
            mcaSatisfies C epsStar (τ j) ∧
              ∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C epsStar i → i ≤ τ j) ∧
          ∀ j : Fin 4,
            latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤ τ j :=
  exists_mcaPrizeLatticeResolved_with_spec_and_lower_brackets_of_spec_and_lower
    domain δ hδ_le_one <|
      exists_mcaPrizeLatticeSpec_and_lower_brackets_of_forall_not_mcaEvent
        domain δ hδ_le_one hno

/-- Named bad-scalar double-cover obligations supply a selected-threshold lattice resolution, the
exact threshold specification, and two-sided lattice brackets. -/
theorem exists_mcaPrizeLatticeResolved_with_spec_and_brackets_ofBadScalarDoubleCover
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hcov : ∀ j : Fin 4, ∀ (u : Code.WordStack F (Fin 2) ι) (γ : F),
      MCABadScalarDoubleCover (F := F) (A := F)
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) (u 0) (u 1) γ)
    (whi : ∀ j : Fin 4,
      GrandChallenges.MCAUpperWitness
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar)
    (hδhi : ∀ j : Fin 4, (whi j).δ ≤ 1) :
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
      mcaPrizeLatticeResolved domain τ ∧
        (∀ j : Fin 4,
          let C : Set (ι → F) :=
            ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
          ∃ _ : mcaThresholdExists C epsStar,
            mcaSatisfies C epsStar (τ j) ∧
              ∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C epsStar i → i ≤ τ j) ∧
          (∀ j : Fin 4,
            latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤ τ j) ∧
            ∀ j : Fin 4, τ j < latticeIndexOf (ι := ι) (whi j).δ (hδhi j) :=
  exists_mcaPrizeLatticeResolved_with_spec_and_brackets_of_spec_and_brackets
    domain δ hδ_le_one whi hδhi <|
      exists_mcaPrizeLatticeSpec_and_brackets_ofBadScalarDoubleCover
        domain δ hδ_le_one hcov whi hδhi

/-- Zero bad-scalar counts supply a selected-threshold lattice resolution, the exact threshold
specification, and two-sided lattice brackets. -/
theorem exists_mcaPrizeLatticeResolved_with_spec_and_brackets_of_mcaBadCount_zero
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hzero : ∀ j : Fin 4, ∀ u : Code.WordStack F (Fin 2) ι,
      mcaBadCount (F := F) (A := F)
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) (u 0) (u 1) = 0)
    (whi : ∀ j : Fin 4,
      GrandChallenges.MCAUpperWitness
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar)
    (hδhi : ∀ j : Fin 4, (whi j).δ ≤ 1) :
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
      mcaPrizeLatticeResolved domain τ ∧
        (∀ j : Fin 4,
          let C : Set (ι → F) :=
            ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
          ∃ _ : mcaThresholdExists C epsStar,
            mcaSatisfies C epsStar (τ j) ∧
              ∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C epsStar i → i ≤ τ j) ∧
          (∀ j : Fin 4,
            latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤ τ j) ∧
            ∀ j : Fin 4, τ j < latticeIndexOf (ι := ι) (whi j).δ (hδhi j) :=
  exists_mcaPrizeLatticeResolved_with_spec_and_brackets_of_spec_and_brackets
    domain δ hδ_le_one whi hδhi <|
      exists_mcaPrizeLatticeSpec_and_brackets_of_mcaBadCount_zero
        domain δ hδ_le_one hzero whi hδhi

/-- Direct no-bad-event frontiers supply a selected-threshold lattice resolution, the exact
threshold specification, and two-sided lattice brackets. -/
theorem exists_mcaPrizeLatticeResolved_with_spec_and_brackets_of_forall_not_mcaEvent
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hno : ∀ j : Fin 4, ∀ (u : Code.WordStack F (Fin 2) ι) (γ : F),
      ¬ mcaEvent (F := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) (u 0) (u 1) γ)
    (whi : ∀ j : Fin 4,
      GrandChallenges.MCAUpperWitness
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar)
    (hδhi : ∀ j : Fin 4, (whi j).δ ≤ 1) :
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
      mcaPrizeLatticeResolved domain τ ∧
        (∀ j : Fin 4,
          let C : Set (ι → F) :=
            ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
          ∃ _ : mcaThresholdExists C epsStar,
            mcaSatisfies C epsStar (τ j) ∧
              ∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C epsStar i → i ≤ τ j) ∧
          (∀ j : Fin 4,
            latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤ τ j) ∧
            ∀ j : Fin 4, τ j < latticeIndexOf (ι := ι) (whi j).δ (hδhi j) :=
  exists_mcaPrizeLatticeResolved_with_spec_and_brackets_of_spec_and_brackets
    domain δ hδ_le_one whi hδhi <|
      exists_mcaPrizeLatticeSpec_and_brackets_of_forall_not_mcaEvent
        domain δ hδ_le_one hno whi hδhi

end LineDecodingResolvedPrizeSpec

set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.exists_mcaPrizeLatticeResolved_with_spec_and_lower_brackets_ofDoubleCover
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.exists_mcaPrizeLatticeResolved_with_spec_and_lower_brackets_ofBadScalarDoubleCover
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.exists_mcaPrizeLatticeResolved_with_spec_and_lower_brackets_of_mcaBadCount_zero
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.exists_mcaPrizeLatticeResolved_with_spec_and_lower_brackets_of_forall_not_mcaEvent
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.exists_mcaPrizeLatticeResolved_with_spec_and_brackets_ofBadScalarDoubleCover
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.exists_mcaPrizeLatticeResolved_with_spec_and_brackets_of_mcaBadCount_zero
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.exists_mcaPrizeLatticeResolved_with_spec_and_brackets_of_forall_not_mcaEvent

end GrandChallengesLattice

end ProximityGap
