/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.GrandChallengesLattice

/-!
# Prize-lattice specification adapters

This lightweight module keeps the long faithful-lattice file from growing while exposing the
checked satisfy/maximality specification of the conjectural four-rate MCA prize aggregation.
-/

namespace ProximityGap

open scoped NNReal

namespace GrandChallengesLattice

open GrandChallenges

section PrizeSpec

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- Project per-rate threshold existence from a concrete faithful MCA prize-lattice resolution. -/
theorem mcaPrizeLatticeResolved.thresholdExists
    (domain : ι ↪ F) {τ : Fin 4 → Fin (Fintype.card ι + 1)}
    (hτ : mcaPrizeLatticeResolved domain τ) (j : Fin 4) :
    mcaThresholdExists
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      epsStar := by
  rcases (mcaPrizeLatticeResolved_iff domain τ).mp hτ j with ⟨hne, _⟩
  exact hne

/-- Project the per-rate satisfy fact from a concrete faithful MCA prize-lattice resolution. -/
theorem mcaPrizeLatticeResolved.satisfies
    (domain : ι ↪ F) {τ : Fin 4 → Fin (Fintype.card ι + 1)}
    (hτ : mcaPrizeLatticeResolved domain τ) (j : Fin 4) :
    mcaSatisfies
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      epsStar (τ j) := by
  rcases (mcaPrizeLatticeResolved_iff domain τ).mp hτ j with ⟨_, hsatisfies, _⟩
  exact hsatisfies

/-- Project the per-rate maximality fact from a concrete faithful MCA prize-lattice resolution. -/
theorem mcaPrizeLatticeResolved.maximal
    (domain : ι ↪ F) {τ : Fin 4 → Fin (Fintype.card ι + 1)}
    (hτ : mcaPrizeLatticeResolved domain τ) (j : Fin 4)
    (i : Fin (Fintype.card ι + 1))
    (hi : mcaSatisfies
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      epsStar i) :
    i ≤ τ j := by
  rcases (mcaPrizeLatticeResolved_iff domain τ).mp hτ j with ⟨_, _, hmax⟩
  exact hmax i hi

/-- Per-rate lower MCA witnesses resolve the faithful MCA prize and expose the
satisfy/maximality specification for the selected lattice thresholds. -/
theorem exists_mcaPrizeLatticeResolved_with_spec_of_lowerWitnesses
    (domain : ι ↪ F)
    (w : ∀ j : Fin 4,
      MCALowerWitness
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar) :
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
      mcaPrizeLatticeResolved domain τ ∧
        ∀ j : Fin 4,
          let C : Set (ι → F) :=
            ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
          ∃ _ : mcaThresholdExists C epsStar,
            mcaSatisfies C epsStar (τ j) ∧
              ∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C epsStar i → i ≤ τ j := by
  rcases exists_mcaPrizeLatticeResolved_of_lowerWitnesses domain w with ⟨τ, hτ⟩
  exact ⟨τ, hτ, (mcaPrizeLatticeResolved_iff domain τ).mp hτ⟩

end PrizeSpec

set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved.thresholdExists
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved.satisfies
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved.maximal
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.exists_mcaPrizeLatticeResolved_with_spec_of_lowerWitnesses
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.exists_mcaPrizeLatticeResolved_with_spec_of_ignoredSource_mcaConjecture

end GrandChallengesLattice

end ProximityGap
