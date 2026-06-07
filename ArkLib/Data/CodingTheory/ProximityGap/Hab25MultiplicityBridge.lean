/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.Hab25Multiplicity
import ArkLib.Data.CodingTheory.ProximityGap.Hab25Core

/-!
# Hab25/BCHKS25 Johnson bridge from S11 cardinality scaling

`Hab25Multiplicity.lean` proves the S11 integer-to-probability scaling edge:
a uniform per-stack bound on the number of bad scalars gives an `epsMCA` probability bound
of the form `ENNReal.ofReal (B / |F|)`.

This file wires that proven scaling theorem into the named Hab25/BCHKS25 Johnson surfaces.
The bridge is intentionally conditional on the remaining real-arithmetic/numerator comparison
`B / |F| ≤ johnsonBoundReal domain k η δ`; it does **not** prove the m-multiplicity
interpolation/counting theorem. Its purpose is to give future cardinality bounds a direct,
non-vacuous route into both the Hab25 numeric inequality and the public T4.12 front door.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace ProximityGap

open Classical NNReal Code Finset
open scoped ProbabilityTheory BigOperators ENNReal

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **S11 scaling ⟹ Hab25/BCHKS25 Johnson numeric shape.** If every word-stack has at most
`N` bad scalars and the integer numerator is bounded by a real `B` whose scaled value
`B / |F|` is at most `johnsonBoundReal`, then the Reed-Solomon code satisfies the exact
Johnson numeric inequality consumed by the Hab25 and BCHKS25 front doors.

This is a bridge from a cardinality statement to the named probability statement; the hard
work remains proving the per-stack cardinality bound and the real numerator comparison. -/
theorem epsMCA_rs_le_johnsonBoundReal_of_card_le
    (domain : ι ↪ F) (k : ℕ) (η δ : ℝ≥0) (N : ℕ) (B : ℝ)
    (hB : 0 ≤ B) (hNB : (N : ℝ) ≤ B)
    (hBdiv :
      B / (Fintype.card F : ℝ) ≤
        CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.johnsonBoundReal domain k η δ)
    (hN : ∀ u : WordStack F (Fin 2) ι,
      (Finset.filter
        (fun γ : F =>
          mcaEvent ((ReedSolomon.code domain k : Set (ι → F))) δ (u 0) (u 1) γ)
        Finset.univ).card ≤ N) :
    epsMCA (F := F) (A := F) ((ReedSolomon.code domain k : Set (ι → F))) δ ≤
      ENNReal.ofReal
        (CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.johnsonBoundReal domain k η δ) := by
  exact le_trans
    (epsMCA_le_ofReal_div_of_card_le
      (F := F) (A := F) ((ReedSolomon.code domain k : Set (ι → F))) δ N B hB hNB hN)
    (ENNReal.ofReal_le_ofReal hBdiv)

/-- **S11 cardinality bridge into the public BCHKS25/Hab25 T4.12 front door.** This packages
`epsMCA_rs_le_johnsonBoundReal_of_card_le` through
`rs_epsMCA_johnson_range_bchks25_of_bound`, so a future proof of the bad-scalar cardinality
bound can discharge the public CapacityBounds statement after supplying only the remaining
real arithmetic comparison. -/
theorem rs_epsMCA_johnson_range_bchks25_of_card_le
    (domain : ι ↪ F) (k : ℕ) (η δ : ℝ≥0) (hη : 0 < η)
    (hδ : CodingTheory.rs_epsMCA_johnson_range_condition domain k η δ)
    (N : ℕ) (B : ℝ)
    (hB : 0 ≤ B) (hNB : (N : ℝ) ≤ B)
    (hBdiv :
      B / (Fintype.card F : ℝ) ≤
        CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.johnsonBoundReal domain k η δ)
    (hN : ∀ u : WordStack F (Fin 2) ι,
      (Finset.filter
        (fun γ : F =>
          mcaEvent ((ReedSolomon.code domain k : Set (ι → F))) δ (u 0) (u 1) γ)
        Finset.univ).card ≤ N) :
    CodingTheory.rs_epsMCA_johnson_range_bchks25 domain k η δ hη hδ :=
  CodingTheory.rs_epsMCA_johnson_range_bchks25_of_bound domain k η δ hη hδ
    (by
      simpa [CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.johnsonBoundReal] using
        epsMCA_rs_le_johnsonBoundReal_of_card_le domain k η δ N B hB hNB hBdiv hN)

end ProximityGap

#print axioms ProximityGap.epsMCA_rs_le_johnsonBoundReal_of_card_le
#print axioms ProximityGap.rs_epsMCA_johnson_range_bchks25_of_card_le
