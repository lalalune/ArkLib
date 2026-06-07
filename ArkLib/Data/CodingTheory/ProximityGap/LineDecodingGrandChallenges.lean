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

end LatticeWitness

end GrandChallengesLattice

#print axioms ProximityGap.GrandChallenges.MCALowerWitness.ofDoubleCover
#print axioms ProximityGap.GrandChallengesLattice.mcaThresholdExists_ofDoubleCover
#print axioms ProximityGap.GrandChallengesLattice.mcaThreshold_spec_ofDoubleCover

end ProximityGap
