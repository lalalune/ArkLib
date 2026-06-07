/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.GrandChallengesLatticePrizeSpec
import ArkLib.Data.CodingTheory.ProximityGap.LineDecodingGrandChallenges

/-!
# Prize-lattice specifications for repaired line-decoding data

This module packages the repaired line-decoding double-cover route with the faithful
satisfy/maximality specification for the four selected MCA prize lattice thresholds.
-/

namespace ProximityGap

open scoped NNReal

set_option linter.unusedDecidableInType false

namespace GrandChallengesLattice

open GrandChallenges

section LineDecodingPrizeSpec

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- Per-rate repaired double-cover data resolves the faithful MCA prize and exposes the
satisfy/maximality specification for the selected lattice thresholds.  This is the prize-spec
version of `exists_mcaPrizeLatticeResolved_ofDoubleCover`. -/
theorem exists_mcaPrizeLatticeResolved_with_spec_ofDoubleCover
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hcov : ∀ j : Fin 4, MCAForallDoubleCover (F := F) (A := F)
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      (δ j)) :
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
      mcaPrizeLatticeResolved domain τ ∧
        ∀ j : Fin 4,
          let C : Set (ι → F) :=
            ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
          ∃ _ : mcaThresholdExists C epsStar,
            mcaSatisfies C epsStar (τ j) ∧
              ∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C epsStar i → i ≤ τ j :=
  exists_mcaPrizeLatticeResolved_with_spec_of_lowerWitnesses domain fun j =>
    MCALowerWitness.ofDoubleCover
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      (δ j) epsStar (hδ_le_one j) (hcov j)

/-- Per-rate named bad-scalar double-cover obligations resolve the faithful MCA prize and expose
the satisfy/maximality specification for the selected lattice thresholds. This is the prize-spec
version of `exists_mcaPrizeLatticeResolved_ofBadScalarDoubleCover`. -/
theorem exists_mcaPrizeLatticeResolved_with_spec_ofBadScalarDoubleCover
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hcov : ∀ j : Fin 4, ∀ (u : Code.WordStack F (Fin 2) ι) (γ : F),
      MCABadScalarDoubleCover (F := F) (A := F)
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) (u 0) (u 1) γ) :
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
      mcaPrizeLatticeResolved domain τ ∧
        ∀ j : Fin 4,
          let C : Set (ι → F) :=
            ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
          ∃ _ : mcaThresholdExists C epsStar,
            mcaSatisfies C epsStar (τ j) ∧
              ∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C epsStar i → i ≤ τ j :=
  exists_mcaPrizeLatticeResolved_with_spec_of_lowerWitnesses domain fun j =>
    MCALowerWitness.ofBadScalarDoubleCover
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      (δ j) epsStar (hδ_le_one j) (hcov j)

/-- Per-rate zero bad-scalar counts resolve the faithful MCA prize and expose the
satisfy/maximality specification for the selected lattice thresholds. This is the prize-spec
version of the #140 count-frontier route. -/
theorem exists_mcaPrizeLatticeResolved_with_spec_of_mcaBadCount_zero
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hzero : ∀ j : Fin 4, ∀ u : Code.WordStack F (Fin 2) ι,
      mcaBadCount (F := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) (u 0) (u 1) = 0) :
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
      mcaPrizeLatticeResolved domain τ ∧
        ∀ j : Fin 4,
          let C : Set (ι → F) :=
            ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
          ∃ _ : mcaThresholdExists C epsStar,
            mcaSatisfies C epsStar (τ j) ∧
              ∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C epsStar i → i ≤ τ j :=
  exists_mcaPrizeLatticeResolved_with_spec_of_lowerWitnesses domain fun j =>
    MCALowerWitness.ofLe (hδ_le_one j) <| by
      rw [epsMCA_eq_zero_of_forall_mcaBadCount_eq_zero (F := F) (A := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) (hzero j)]
      simp

/-- Per-rate direct no-bad-event frontiers resolve the faithful MCA prize and expose the
satisfy/maximality specification for the selected lattice thresholds. -/
theorem exists_mcaPrizeLatticeResolved_with_spec_of_forall_not_mcaEvent
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hno : ∀ j : Fin 4, ∀ (u : Code.WordStack F (Fin 2) ι) (γ : F),
      ¬ mcaEvent (F := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) (u 0) (u 1) γ) :
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
      mcaPrizeLatticeResolved domain τ ∧
        ∀ j : Fin 4,
          let C : Set (ι → F) :=
            ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
          ∃ _ : mcaThresholdExists C epsStar,
            mcaSatisfies C epsStar (τ j) ∧
              ∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C epsStar i → i ≤ τ j :=
  exists_mcaPrizeLatticeResolved_with_spec_of_lowerWitnesses domain fun j =>
    MCALowerWitness.ofLe (hδ_le_one j) <| by
      rw [epsMCA_eq_zero_of_forall_not_mcaEvent (F := F) (A := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) (hno j)]
      simp

/-- Adjacent repaired double-cover frontiers resolve the four-rate MCA prize at the repaired
lower-frontier lattice indices and expose the satisfy/maximality specification for those concrete
thresholds. -/
theorem mcaPrizeLatticeResolved_with_spec_ofDoubleCover_and_adjacent_upperWitnesses
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hcov : ∀ j : Fin 4, MCAForallDoubleCover (F := F) (A := F)
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      (δ j))
    (whi : ∀ j : Fin 4,
      GrandChallenges.MCAUpperWitness
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar)
    (hδhi : ∀ j : Fin 4, (whi j).δ ≤ 1)
    (hadj : ∀ j : Fin 4,
      (latticeIndexOf (ι := ι) (whi j).δ (hδhi j)).val =
        (latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)).val + 1) :
    let τ : Fin 4 → Fin (Fintype.card ι + 1) :=
      fun j => latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)
    mcaPrizeLatticeResolved domain τ ∧
      ∀ j : Fin 4,
        let C : Set (ι → F) :=
          ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
        ∃ _ : mcaThresholdExists C epsStar,
          mcaSatisfies C epsStar (τ j) ∧
            ∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C epsStar i → i ≤ τ j := by
  let τ : Fin 4 → Fin (Fintype.card ι + 1) :=
    fun j => latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)
  have hτ : mcaPrizeLatticeResolved domain τ :=
    mcaPrizeLatticeResolved_ofDoubleCover_and_adjacent_upperWitnesses
      domain δ hδ_le_one hcov whi hδhi hadj
  exact ⟨hτ, (mcaPrizeLatticeResolved_iff domain τ).mp hτ⟩

/-- Adjacent named bad-scalar double-cover frontiers resolve the four-rate MCA prize at the repaired
lower-frontier lattice indices and expose the satisfy/maximality specification for those concrete
thresholds. -/
theorem mcaPrizeLatticeResolved_with_spec_ofBadScalarDoubleCover_and_adjacent_upperWitnesses
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
    (hδhi : ∀ j : Fin 4, (whi j).δ ≤ 1)
    (hadj : ∀ j : Fin 4,
      (latticeIndexOf (ι := ι) (whi j).δ (hδhi j)).val =
        (latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)).val + 1) :
    let τ : Fin 4 → Fin (Fintype.card ι + 1) :=
      fun j => latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)
    mcaPrizeLatticeResolved domain τ ∧
      ∀ j : Fin 4,
        let C : Set (ι → F) :=
          ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
        ∃ _ : mcaThresholdExists C epsStar,
          mcaSatisfies C epsStar (τ j) ∧
            ∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C epsStar i → i ≤ τ j := by
  let τ : Fin 4 → Fin (Fintype.card ι + 1) :=
    fun j => latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)
  have hτ : mcaPrizeLatticeResolved domain τ :=
    mcaPrizeLatticeResolved_ofBadScalarDoubleCover_and_adjacent_upperWitnesses
      domain δ hδ_le_one hcov whi hδhi hadj
  exact ⟨hτ, (mcaPrizeLatticeResolved_iff domain τ).mp hτ⟩

/-- Adjacent zero bad-scalar count frontiers resolve the four-rate MCA prize at the repaired
lower-frontier lattice indices and expose the satisfy/maximality specification for those concrete
thresholds. -/
theorem mcaPrizeLatticeResolved_with_spec_of_mcaBadCount_zero_and_adjacent_upperWitnesses
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hzero : ∀ j : Fin 4, ∀ u : Code.WordStack F (Fin 2) ι,
      mcaBadCount (F := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) (u 0) (u 1) = 0)
    (whi : ∀ j : Fin 4,
      GrandChallenges.MCAUpperWitness
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar)
    (hδhi : ∀ j : Fin 4, (whi j).δ ≤ 1)
    (hadj : ∀ j : Fin 4,
      (latticeIndexOf (ι := ι) (whi j).δ (hδhi j)).val =
        (latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)).val + 1) :
    let τ : Fin 4 → Fin (Fintype.card ι + 1) :=
      fun j => latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)
    mcaPrizeLatticeResolved domain τ ∧
      ∀ j : Fin 4,
        let C : Set (ι → F) :=
          ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
        ∃ _ : mcaThresholdExists C epsStar,
          mcaSatisfies C epsStar (τ j) ∧
            ∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C epsStar i → i ≤ τ j := by
  let τ : Fin 4 → Fin (Fintype.card ι + 1) :=
    fun j => latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)
  have hτ : mcaPrizeLatticeResolved domain τ :=
    mcaPrizeLatticeResolved_of_mcaBadCount_zero_and_adjacent_upperWitnesses
      domain δ hδ_le_one hzero whi hδhi hadj
  exact ⟨hτ, (mcaPrizeLatticeResolved_iff domain τ).mp hτ⟩

/-- Adjacent direct no-bad-event frontiers resolve the four-rate MCA prize at the repaired
lower-frontier lattice indices and expose the satisfy/maximality specification for those concrete
thresholds. -/
theorem mcaPrizeLatticeResolved_with_spec_of_forall_not_mcaEvent_and_adjacent_upperWitnesses
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
    (hδhi : ∀ j : Fin 4, (whi j).δ ≤ 1)
    (hadj : ∀ j : Fin 4,
      (latticeIndexOf (ι := ι) (whi j).δ (hδhi j)).val =
        (latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)).val + 1) :
    let τ : Fin 4 → Fin (Fintype.card ι + 1) :=
      fun j => latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)
    mcaPrizeLatticeResolved domain τ ∧
      ∀ j : Fin 4,
        let C : Set (ι → F) :=
          ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
        ∃ _ : mcaThresholdExists C epsStar,
          mcaSatisfies C epsStar (τ j) ∧
            ∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C epsStar i → i ≤ τ j := by
  let τ : Fin 4 → Fin (Fintype.card ι + 1) :=
    fun j => latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)
  have hτ : mcaPrizeLatticeResolved domain τ :=
    mcaPrizeLatticeResolved_of_forall_not_mcaEvent_and_adjacent_upperWitnesses
      domain δ hδ_le_one hno whi hδhi hadj
  exact ⟨hτ, (mcaPrizeLatticeResolved_iff domain τ).mp hτ⟩

end LineDecodingPrizeSpec

set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.exists_mcaPrizeLatticeResolved_with_spec_ofDoubleCover
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.exists_mcaPrizeLatticeResolved_with_spec_ofBadScalarDoubleCover
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.exists_mcaPrizeLatticeResolved_with_spec_of_mcaBadCount_zero
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.exists_mcaPrizeLatticeResolved_with_spec_of_forall_not_mcaEvent
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved_with_spec_ofDoubleCover_and_adjacent_upperWitnesses
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved_with_spec_ofBadScalarDoubleCover_and_adjacent_upperWitnesses
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved_with_spec_of_mcaBadCount_zero_and_adjacent_upperWitnesses
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved_with_spec_of_forall_not_mcaEvent_and_adjacent_upperWitnesses

end GrandChallengesLattice

end ProximityGap
