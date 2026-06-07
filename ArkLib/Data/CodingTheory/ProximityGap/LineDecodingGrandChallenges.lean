/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.LineDecodingCoverage
import ArkLib.Data.CodingTheory.ProximityGap.GrandChallengesLattice

/-!
# Grand Challenge adapters for the repaired line-decoding coverage theorem

`LineDecodingCoverage.lean` proves the corrected coverage-to-vanishing direction for ABF26
Theorem 4.21. This module exposes the consumer-facing Grand MCA Challenge adapters: the explicit
double-cover hypothesis gives a lower witness, and hence a faithful lattice-threshold witness,
without using the refuted black-box `lineDecodable_imp_epsMCA_le_target` surface.
-/

namespace ProximityGap

open scoped NNReal

set_option linter.unusedDecidableInType false

section LowerWitness

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **Grand-MCA lower witness from the repaired line-decoding coverage data.** Once the exposed
double-cover data is available, `epsMCA(C, δ) = 0`, hence any `ε_star` accepts radius `δ` as a
lower witness. -/
def GrandChallenges.MCALowerWitness.ofDoubleCover (C : Set (ι → F)) (δ ε_star : ℝ≥0)
    (hδ_le_one : δ ≤ 1)
    (hcov : MCAForallDoubleCover (F := F) (A := F) C δ) :
    GrandChallenges.MCALowerWitness C ε_star :=
  GrandChallenges.MCALowerWitness.ofLe hδ_le_one <| by
    rw [epsMCA_eq_zero_of_forall_double_cover C δ hcov]
    simp

/-- Grand-MCA lower witness from the named per-bad-scalar double-cover obligations. This is the
same repaired coverage path as `MCALowerWitness.ofDoubleCover`, but with the local GS extraction
target exposed directly. -/
def GrandChallenges.MCALowerWitness.ofBadScalarDoubleCover
    (C : Set (ι → F)) (δ ε_star : ℝ≥0)
    (hδ_le_one : δ ≤ 1)
    (hcov : ∀ (u : Code.WordStack F (Fin 2) ι) (γ : F),
      MCABadScalarDoubleCover (F := F) (A := F) C δ (u 0) (u 1) γ) :
    GrandChallenges.MCALowerWitness C ε_star :=
  GrandChallenges.MCALowerWitness.ofLe hδ_le_one <| by
    rw [epsMCA_eq_zero_of_badScalarDoubleCover C δ hcov]
    simp

/-- Grand-MCA lower witness from zero bad-scalar counts. This keeps the finite-count frontier as a
direct Grand Challenge lower-witness source, without assuming a double-cover package. -/
def GrandChallenges.MCALowerWitness.of_mcaBadCount_zero
    (C : Set (ι → F)) (δ ε_star : ℝ≥0)
    (hδ_le_one : δ ≤ 1)
    (hzero : ∀ u : Code.WordStack F (Fin 2) ι,
      mcaBadCount (F := F) C δ (u 0) (u 1) = 0) :
    GrandChallenges.MCALowerWitness C ε_star :=
  GrandChallenges.MCALowerWitness.ofLe hδ_le_one <| by
    rw [epsMCA_eq_zero_of_forall_mcaBadCount_eq_zero (F := F) (A := F) C δ hzero]
    simp

/-- Grand-MCA lower witness from a direct no-bad-event frontier. -/
def GrandChallenges.MCALowerWitness.of_forall_not_mcaEvent
    (C : Set (ι → F)) (δ ε_star : ℝ≥0)
    (hδ_le_one : δ ≤ 1)
    (hno : ∀ (u : Code.WordStack F (Fin 2) ι) (γ : F),
      ¬ mcaEvent (F := F) C δ (u 0) (u 1) γ) :
    GrandChallenges.MCALowerWitness C ε_star :=
  GrandChallenges.MCALowerWitness.ofLe hδ_le_one <| by
    rw [epsMCA_eq_zero_of_forall_not_mcaEvent (F := F) (A := F) C δ hno]
    simp

/-- Prize-rate specialization of repaired double-cover data.  At any ABF26 prize rate, an
explicit `MCAForallDoubleCover` hypothesis for the corresponding Reed-Solomon code gives a
one-sided MCA lower witness at `epsStar`. -/
theorem GrandChallenges.exists_prize_mcaLowerWitness_ofDoubleCover
    (domain : ι ↪ F) (j : Fin 4) (δ : ℝ≥0)
    (hδ_le_one : δ ≤ 1)
    (hcov : MCAForallDoubleCover (F := F) (A := F)
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F)) δ) :
    ∃ w : GrandChallenges.MCALowerWitness
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar,
      w.δ = δ := by
  refine ⟨GrandChallenges.MCALowerWitness.ofDoubleCover
    (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
    δ epsStar hδ_le_one hcov, rfl⟩

/-- Prize-rate specialization of the named per-bad-scalar double-cover surface. -/
theorem GrandChallenges.exists_prize_mcaLowerWitness_ofBadScalarDoubleCover
    (domain : ι ↪ F) (j : Fin 4) (δ : ℝ≥0)
    (hδ_le_one : δ ≤ 1)
    (hcov : ∀ (u : Code.WordStack F (Fin 2) ι) (γ : F),
      MCABadScalarDoubleCover (F := F) (A := F)
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        δ (u 0) (u 1) γ) :
    ∃ w : GrandChallenges.MCALowerWitness
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar,
      w.δ = δ := by
  refine ⟨GrandChallenges.MCALowerWitness.ofBadScalarDoubleCover
    (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
    δ epsStar hδ_le_one hcov, rfl⟩

/-- Prize-rate specialization of zero bad-scalar counts. -/
theorem GrandChallenges.exists_prize_mcaLowerWitness_of_mcaBadCount_zero
    (domain : ι ↪ F) (j : Fin 4) (δ : ℝ≥0)
    (hδ_le_one : δ ≤ 1)
    (hzero : ∀ u : Code.WordStack F (Fin 2) ι,
      mcaBadCount (F := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        δ (u 0) (u 1) = 0) :
    ∃ w : GrandChallenges.MCALowerWitness
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar,
      w.δ = δ := by
  refine ⟨GrandChallenges.MCALowerWitness.of_mcaBadCount_zero
    (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
    δ epsStar hδ_le_one hzero, rfl⟩

/-- Prize-rate specialization of direct no-bad-event frontiers. -/
theorem GrandChallenges.exists_prize_mcaLowerWitness_of_forall_not_mcaEvent
    (domain : ι ↪ F) (j : Fin 4) (δ : ℝ≥0)
    (hδ_le_one : δ ≤ 1)
    (hno : ∀ (u : Code.WordStack F (Fin 2) ι) (γ : F),
      ¬ mcaEvent (F := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        δ (u 0) (u 1) γ) :
    ∃ w : GrandChallenges.MCALowerWitness
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar,
      w.δ = δ := by
  refine ⟨GrandChallenges.MCALowerWitness.of_forall_not_mcaEvent
    (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
    δ epsStar hδ_le_one hno, rfl⟩

end LowerWitness

namespace GrandChallengesLattice

open GrandChallenges

section LatticeWitness

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- A repaired double-cover target makes the faithful MCA lattice threshold exist. This is the
line-decoding replacement path that avoids the refuted black-box target entirely. -/
theorem mcaThresholdExists_ofDoubleCover (C : Set (ι → F)) (δ ε_star : ℝ≥0)
    (hδ_le_one : δ ≤ 1)
    (hcov : MCAForallDoubleCover (F := F) (A := F) C δ) :
    mcaThresholdExists C ε_star :=
  mcaThresholdExists_of_MCALowerWitness C ε_star
    (MCALowerWitness.ofDoubleCover C δ ε_star hδ_le_one hcov)

/-- The faithful MCA threshold created from repaired double-cover data satisfies the MCA bound. -/
theorem mcaThreshold_spec_ofDoubleCover (C : Set (ι → F)) (δ ε_star : ℝ≥0)
    (hδ_le_one : δ ≤ 1)
    (hcov : MCAForallDoubleCover (F := F) (A := F) C δ) :
    let hne := mcaThresholdExists_ofDoubleCover C δ ε_star hδ_le_one hcov
    mcaSatisfies C ε_star (mcaThreshold C ε_star hne) :=
  mcaThreshold_spec C ε_star
    (mcaThresholdExists_ofDoubleCover C δ ε_star hδ_le_one hcov)

/-- A named per-bad-scalar double-cover target makes the faithful MCA lattice threshold exist. -/
theorem mcaThresholdExists_ofBadScalarDoubleCover (C : Set (ι → F)) (δ ε_star : ℝ≥0)
    (hδ_le_one : δ ≤ 1)
    (hcov : ∀ (u : Code.WordStack F (Fin 2) ι) (γ : F),
      MCABadScalarDoubleCover (F := F) (A := F) C δ (u 0) (u 1) γ) :
    mcaThresholdExists C ε_star :=
  mcaThresholdExists_of_MCALowerWitness C ε_star
    (MCALowerWitness.ofBadScalarDoubleCover C δ ε_star hδ_le_one hcov)

/-- The faithful MCA threshold created from named per-bad-scalar double-cover data satisfies the
MCA bound. -/
theorem mcaThreshold_spec_ofBadScalarDoubleCover (C : Set (ι → F)) (δ ε_star : ℝ≥0)
    (hδ_le_one : δ ≤ 1)
    (hcov : ∀ (u : Code.WordStack F (Fin 2) ι) (γ : F),
      MCABadScalarDoubleCover (F := F) (A := F) C δ (u 0) (u 1) γ) :
    let hne := mcaThresholdExists_ofBadScalarDoubleCover C δ ε_star hδ_le_one hcov
    mcaSatisfies C ε_star (mcaThreshold C ε_star hne) :=
  mcaThreshold_spec C ε_star
    (mcaThresholdExists_ofBadScalarDoubleCover C δ ε_star hδ_le_one hcov)

/-- Zero bad-scalar counts make the faithful MCA lattice threshold exist. -/
theorem mcaThresholdExists_of_mcaBadCount_zero (C : Set (ι → F)) (δ ε_star : ℝ≥0)
    (hδ_le_one : δ ≤ 1)
    (hzero : ∀ u : Code.WordStack F (Fin 2) ι,
      mcaBadCount (F := F) C δ (u 0) (u 1) = 0) :
    mcaThresholdExists C ε_star :=
  mcaThresholdExists_of_MCALowerWitness C ε_star
    (MCALowerWitness.of_mcaBadCount_zero C δ ε_star hδ_le_one hzero)

/-- The faithful MCA threshold created from zero bad-scalar counts satisfies the MCA bound. -/
theorem mcaThreshold_spec_of_mcaBadCount_zero (C : Set (ι → F)) (δ ε_star : ℝ≥0)
    (hδ_le_one : δ ≤ 1)
    (hzero : ∀ u : Code.WordStack F (Fin 2) ι,
      mcaBadCount (F := F) C δ (u 0) (u 1) = 0) :
    let hne := mcaThresholdExists_of_mcaBadCount_zero C δ ε_star hδ_le_one hzero
    mcaSatisfies C ε_star (mcaThreshold C ε_star hne) :=
  mcaThreshold_spec C ε_star
    (mcaThresholdExists_of_mcaBadCount_zero C δ ε_star hδ_le_one hzero)

/-- A direct no-bad-event frontier makes the faithful MCA lattice threshold exist. -/
theorem mcaThresholdExists_of_forall_not_mcaEvent (C : Set (ι → F)) (δ ε_star : ℝ≥0)
    (hδ_le_one : δ ≤ 1)
    (hno : ∀ (u : Code.WordStack F (Fin 2) ι) (γ : F),
      ¬ mcaEvent (F := F) C δ (u 0) (u 1) γ) :
    mcaThresholdExists C ε_star :=
  mcaThresholdExists_of_MCALowerWitness C ε_star
    (MCALowerWitness.of_forall_not_mcaEvent C δ ε_star hδ_le_one hno)

/-- The faithful MCA threshold created from a no-bad-event frontier satisfies the MCA bound. -/
theorem mcaThreshold_spec_of_forall_not_mcaEvent (C : Set (ι → F)) (δ ε_star : ℝ≥0)
    (hδ_le_one : δ ≤ 1)
    (hno : ∀ (u : Code.WordStack F (Fin 2) ι) (γ : F),
      ¬ mcaEvent (F := F) C δ (u 0) (u 1) γ) :
    let hne := mcaThresholdExists_of_forall_not_mcaEvent C δ ε_star hδ_le_one hno
    mcaSatisfies C ε_star (mcaThreshold C ε_star hne) :=
  mcaThreshold_spec C ε_star
    (mcaThresholdExists_of_forall_not_mcaEvent C δ ε_star hδ_le_one hno)

/-- Per-rate repaired double-cover data resolves the faithful MCA lattice prize existentially.
This is the prize-facing aggregation of the #140 repaired coverage theorem through the existing
lower-witness lattice front door. -/
theorem exists_mcaPrizeLatticeResolved_ofDoubleCover
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hcov : ∀ j : Fin 4, MCAForallDoubleCover (F := F) (A := F)
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      (δ j)) :
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1), mcaPrizeLatticeResolved domain τ :=
  exists_mcaPrizeLatticeResolved_of_lowerWitnesses domain fun j =>
    GrandChallenges.MCALowerWitness.ofDoubleCover
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      (δ j) epsStar (hδ_le_one j) (hcov j)

/-- Per-rate named per-bad-scalar double-cover obligations resolve the faithful MCA lattice prize
existentially. -/
theorem exists_mcaPrizeLatticeResolved_ofBadScalarDoubleCover
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hcov : ∀ j : Fin 4, ∀ (u : Code.WordStack F (Fin 2) ι) (γ : F),
      MCABadScalarDoubleCover (F := F) (A := F)
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) (u 0) (u 1) γ) :
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1), mcaPrizeLatticeResolved domain τ :=
  exists_mcaPrizeLatticeResolved_of_lowerWitnesses domain fun j =>
    GrandChallenges.MCALowerWitness.ofBadScalarDoubleCover
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      (δ j) epsStar (hδ_le_one j) (hcov j)

/-- Per-rate zero bad-scalar counts resolve the faithful MCA lattice prize existentially. -/
theorem exists_mcaPrizeLatticeResolved_of_mcaBadCount_zero
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hzero : ∀ j : Fin 4, ∀ u : Code.WordStack F (Fin 2) ι,
      mcaBadCount (F := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) (u 0) (u 1) = 0) :
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1), mcaPrizeLatticeResolved domain τ :=
  exists_mcaPrizeLatticeResolved_of_lowerWitnesses domain fun j =>
    GrandChallenges.MCALowerWitness.of_mcaBadCount_zero
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      (δ j) epsStar (hδ_le_one j) (hzero j)

/-- Per-rate direct no-bad-event frontiers resolve the faithful MCA lattice prize
existentially. -/
theorem exists_mcaPrizeLatticeResolved_of_forall_not_mcaEvent
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hno : ∀ j : Fin 4, ∀ (u : Code.WordStack F (Fin 2) ι) (γ : F),
      ¬ mcaEvent (F := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) (u 0) (u 1) γ) :
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1), mcaPrizeLatticeResolved domain τ :=
  exists_mcaPrizeLatticeResolved_of_lowerWitnesses domain fun j =>
    GrandChallenges.MCALowerWitness.of_forall_not_mcaEvent
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      (δ j) epsStar (hδ_le_one j) (hno j)

end LatticeWitness

end GrandChallengesLattice

#print axioms ProximityGap.GrandChallenges.MCALowerWitness.ofDoubleCover
#print axioms ProximityGap.GrandChallenges.MCALowerWitness.ofBadScalarDoubleCover
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallenges.MCALowerWitness.of_mcaBadCount_zero
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallenges.MCALowerWitness.of_forall_not_mcaEvent
#print axioms ProximityGap.GrandChallenges.exists_prize_mcaLowerWitness_ofDoubleCover
#print axioms ProximityGap.GrandChallenges.exists_prize_mcaLowerWitness_ofBadScalarDoubleCover
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallenges.exists_prize_mcaLowerWitness_of_mcaBadCount_zero
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallenges.exists_prize_mcaLowerWitness_of_forall_not_mcaEvent
#print axioms ProximityGap.GrandChallengesLattice.mcaThresholdExists_ofDoubleCover
#print axioms ProximityGap.GrandChallengesLattice.mcaThreshold_spec_ofDoubleCover
#print axioms ProximityGap.GrandChallengesLattice.mcaThresholdExists_ofBadScalarDoubleCover
#print axioms ProximityGap.GrandChallengesLattice.mcaThreshold_spec_ofBadScalarDoubleCover
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaThresholdExists_of_mcaBadCount_zero
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaThreshold_spec_of_mcaBadCount_zero
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaThresholdExists_of_forall_not_mcaEvent
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaThreshold_spec_of_forall_not_mcaEvent
#print axioms ProximityGap.GrandChallengesLattice.exists_mcaPrizeLatticeResolved_ofDoubleCover
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.exists_mcaPrizeLatticeResolved_ofBadScalarDoubleCover
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.exists_mcaPrizeLatticeResolved_of_mcaBadCount_zero
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.exists_mcaPrizeLatticeResolved_of_forall_not_mcaEvent

end ProximityGap
