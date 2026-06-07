/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.Hab25Johnson
import ArkLib.Data.CodingTheory.ProximityGap.Hab25AlgebraicBridge
import ArkLib.Data.CodingTheory.ProximityGap.Hab25MultiplicityBridge

/-!
# Hab25 Johnson numeric residual from S11 cardinality scaling

This file provides the final lightweight adapter from the proven S11 scaling bridge into the
opened Hab25 residual bundle's `JohnsonNumericBound` field. It does not prove the
m-multiplicity bad-scalar count; it only states the exact way that future cardinality bound,
together with the remaining real numerator comparison, discharges the named numeric residual.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

open _root_.ProximityGap
open Classical NNReal Code Finset
open scoped ProbabilityTheory BigOperators ENNReal

variable {ι₀ : Type} [Fintype ι₀] [Nonempty ι₀] [DecidableEq ι₀]
variable {F₀ : Type} [Field F₀] [Fintype F₀] [DecidableEq F₀]

/-- **Constructor for the Hab25 numeric residual from cardinality data.** A uniform bound
`N` on the bad-scalar set of every word-stack, plus real arithmetic
`(N : ℝ) ≤ B` and `B / |F| ≤ johnsonBoundReal`, gives the exact `JohnsonNumericBound`
field consumed by `Hab25JohnsonResiduals`.

This is pure plumbing from the proven S11 scaling theorem into the opened residual bundle:
the hard theorem remains the m-multiplicity proof of the per-stack bad-scalar cardinality
bound and the closed-form numerator comparison. -/
theorem JohnsonNumericBound.of_card_le
    (domain : ι₀ ↪ F₀) (k : ℕ) (η δ : ℝ≥0) (N : ℕ) (B : ℝ)
    (hB : 0 ≤ B) (hNB : (N : ℝ) ≤ B)
    (hBdiv : B / (Fintype.card F₀ : ℝ) ≤
      CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.johnsonBoundReal domain k η δ)
    (hN : ∀ u : WordStack F₀ (Fin 2) ι₀,
      (Finset.filter
        (fun γ : F₀ =>
          mcaEvent ((ReedSolomon.code domain k : Set (ι₀ → F₀))) δ (u 0) (u 1) γ)
        Finset.univ).card ≤ N) :
    JohnsonNumericBound domain k η δ := by
  simpa [JohnsonNumericBound] using
    _root_.ProximityGap.epsMCA_rs_le_johnsonBoundReal_of_card_le
      domain k η δ N B hB hNB hBdiv hN

/-- **Constructor for the Hab25 numeric residual from algebraic covers.** If every stack's
actual bad-scalar set is covered by the `Edis` field of Hab25 algebraic data, and the proven
integer endgame bound `ell * n` is uniformly bounded by `N`, then the S11 scaling bridge gives
the exact `JohnsonNumericBound`.

The hard theorem remains producing the per-stack GS-over-`F(Z)` algebraic covers and the
closed-form numerator comparison. -/
theorem JohnsonNumericBound.of_algebraic_cover
    (domain : ι₀ ↪ F₀) (k : ℕ) (η δ : ℝ≥0) (N : ℕ) (B : ℝ)
    (hη : 0 < η)
    (hδ : CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.InJohnsonRange domain k η δ)
    (hB : 0 ≤ B) (hNB : (N : ℝ) ≤ B)
    (hBdiv : B / (Fintype.card F₀ : ℝ) ≤
      CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.johnsonBoundReal domain k η δ)
    (hAlg : ∀ u : WordStack F₀ (Fin 2) ι₀,
      ∃ A : Hab25JohnsonAlgebraicData domain k η δ hη hδ,
        _root_.ProximityGap.hab25McaBadScalars domain k δ u ⊆ A.Edis ∧
          A.ℓ * Fintype.card ι₀ ≤ N) :
    JohnsonNumericBound domain k η δ := by
  simpa [JohnsonNumericBound] using
    _root_.ProximityGap.epsMCA_rs_le_johnsonBoundReal_of_algebraic_cover
      domain k η δ N B hη hδ hB hNB hBdiv hAlg

/-- **Full Hab25 residual bundle from algebraic data plus S11 count data.** If the
GS-over-`F(Z)` algebraic datum has already been supplied, then a uniform bad-scalar count
bound and the remaining real numerator comparison produce the complete
`Hab25JohnsonResiduals` bundle.

This is only residual packaging: it does not prove the GS algebraic datum, the per-stack
cardinality theorem, or the closed-form numerator comparison. -/
def Hab25JohnsonResiduals.ofAlgebraicData_card_le
    {domain : ι₀ ↪ F₀} {k : ℕ} {η δ : ℝ≥0}
    {hη : 0 < η}
    {hδ : CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.InJohnsonRange domain k η δ}
    (A : Hab25JohnsonAlgebraicData domain k η δ hη hδ)
    (N : ℕ) (B : ℝ)
    (hB : 0 ≤ B) (hNB : (N : ℝ) ≤ B)
    (hBdiv : B / (Fintype.card F₀ : ℝ) ≤
      CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.johnsonBoundReal domain k η δ)
    (hN : ∀ u : WordStack F₀ (Fin 2) ι₀,
      (Finset.filter
        (fun γ : F₀ =>
          mcaEvent ((ReedSolomon.code domain k : Set (ι₀ → F₀))) δ (u 0) (u 1) γ)
        Finset.univ).card ≤ N) :
    Hab25JohnsonResiduals domain k η δ hη hδ :=
  Hab25JohnsonResiduals.ofAlgebraicData A
    (JohnsonNumericBound.of_card_le domain k η δ N B hB hNB hBdiv hN)

/-- **Full Hab25 residual bundle from algebraic data plus per-stack algebraic covers.** This
combines an already-supplied GS-over-`F(Z)` datum with the algebraic-cover-to-S11 bridge:
per-stack covers of the actual bad scalars, a uniform `ell * n ≤ N` bound, and the remaining
real numerator comparison produce the complete `Hab25JohnsonResiduals` bundle.

This is only the final packaging edge for future GS-cover proofs; it does not construct the
covers or prove the closed-form numerator comparison. -/
def Hab25JohnsonResiduals.ofAlgebraicData_algebraic_cover
    {domain : ι₀ ↪ F₀} {k : ℕ} {η δ : ℝ≥0}
    {hη : 0 < η}
    {hδ : CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.InJohnsonRange domain k η δ}
    (A : Hab25JohnsonAlgebraicData domain k η δ hη hδ)
    (N : ℕ) (B : ℝ)
    (hB : 0 ≤ B) (hNB : (N : ℝ) ≤ B)
    (hBdiv : B / (Fintype.card F₀ : ℝ) ≤
      CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.johnsonBoundReal domain k η δ)
    (hAlg : ∀ u : WordStack F₀ (Fin 2) ι₀,
      ∃ A' : Hab25JohnsonAlgebraicData domain k η δ hη hδ,
        _root_.ProximityGap.hab25McaBadScalars domain k δ u ⊆ A'.Edis ∧
          A'.ℓ * Fintype.card ι₀ ≤ N) :
    Hab25JohnsonResiduals domain k η δ hη hδ :=
  Hab25JohnsonResiduals.ofAlgebraicData A
    (JohnsonNumericBound.of_algebraic_cover
      domain k η δ N B hη hδ hB hNB hBdiv hAlg)

/-- **Hab25 Johnson bound from algebraic data plus S11 count data.** This is the direct
consumer-facing form of `Hab25JohnsonResiduals.ofAlgebraicData_card_le`: once an algebraic datum,
uniform bad-scalar cardinality bound, and numerator comparison are supplied, the Johnson-range
`ε_mca` bound follows. -/
theorem mca_johnson_of_algebraicData_card_le
    {domain : ι₀ ↪ F₀} {k : ℕ} {η δ : ℝ≥0}
    {hη : 0 < η}
    {hδ : CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.InJohnsonRange domain k η δ}
    (A : Hab25JohnsonAlgebraicData domain k η δ hη hδ)
    (N : ℕ) (B : ℝ)
    (hB : 0 ≤ B) (hNB : (N : ℝ) ≤ B)
    (hBdiv : B / (Fintype.card F₀ : ℝ) ≤
      CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.johnsonBoundReal domain k η δ)
    (hN : ∀ u : WordStack F₀ (Fin 2) ι₀,
      (Finset.filter
        (fun γ : F₀ =>
          mcaEvent ((ReedSolomon.code domain k : Set (ι₀ → F₀))) δ (u 0) (u 1) γ)
        Finset.univ).card ≤ N) :
    epsMCA (F := F₀) (A := F₀) ((ReedSolomon.code domain k : Set (ι₀ → F₀))) δ ≤
      ENNReal.ofReal
        (CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.johnsonBoundReal domain k η δ) :=
  mca_johnson_of_residuals domain k η δ hη hδ
    (Hab25JohnsonResiduals.ofAlgebraicData_card_le A N B hB hNB hBdiv hN)

/-- **Hab25 Johnson bound from per-stack algebraic covers.** This composes the algebraic-cover
residual constructor with `mca_johnson_of_residuals`, exposing the final `ε_mca` bound directly
from the future GS-over-`F(Z)` cover target plus the remaining numerator comparison. -/
theorem mca_johnson_of_algebraicData_algebraic_cover
    {domain : ι₀ ↪ F₀} {k : ℕ} {η δ : ℝ≥0}
    {hη : 0 < η}
    {hδ : CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.InJohnsonRange domain k η δ}
    (A : Hab25JohnsonAlgebraicData domain k η δ hη hδ)
    (N : ℕ) (B : ℝ)
    (hB : 0 ≤ B) (hNB : (N : ℝ) ≤ B)
    (hBdiv : B / (Fintype.card F₀ : ℝ) ≤
      CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.johnsonBoundReal domain k η δ)
    (hAlg : ∀ u : WordStack F₀ (Fin 2) ι₀,
      ∃ A' : Hab25JohnsonAlgebraicData domain k η δ hη hδ,
        _root_.ProximityGap.hab25McaBadScalars domain k δ u ⊆ A'.Edis ∧
          A'.ℓ * Fintype.card ι₀ ≤ N) :
    epsMCA (F := F₀) (A := F₀) ((ReedSolomon.code domain k : Set (ι₀ → F₀))) δ ≤
      ENNReal.ofReal
        (CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.johnsonBoundReal domain k η δ) :=
  mca_johnson_of_residuals domain k η δ hη hδ
    (Hab25JohnsonResiduals.ofAlgebraicData_algebraic_cover A N B hB hNB hBdiv hAlg)

end CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.JohnsonNumericBound.of_card_le
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.JohnsonNumericBound.of_algebraic_cover
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.Hab25JohnsonResiduals.ofAlgebraicData_card_le
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.Hab25JohnsonResiduals.ofAlgebraicData_algebraic_cover
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.mca_johnson_of_algebraicData_card_le
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.mca_johnson_of_algebraicData_algebraic_cover
