/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Katerina Hristova, František Silváši, Julian Sutherland,
         Ilia Vlasov, Chung Thai Nguyen
-/

import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.Prelude
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.ErrorBound
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AffineLines.UniqueDecoding
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.Curves
import ArkLib.Data.CodingTheory.ProximityGap.BoundaryCardResidual
import ArkLib.ToMathlib.BoundaryDischarge
import ArkLib.ToMathlib.KeystoneStrictResidual

/-!
# BCIKS20 Theorem 1.4 — correlated agreement of Reed-Solomon codes over affine lines

This file assembles the main correlated-agreement theorem of [BCIKS20] over affine lines from
the unique-decoding and curve ingredients. `RS_correlatedAgreement_affineLines` (and its strict /
positive variants `RS_correlatedAgreement_affineLines_strict`,
`RS_correlatedAgreement_affineLines_strict_pos`) cover the regime up to the relevant bound, while
the `..._johnson_of_betaRec...` results extend the conclusion into the Johnson regime, conditional
on the recursive `β`-construction and the documented lattice residual.
-/

namespace ProximityGap

open NNReal Finset Function ProbabilityTheory Finset Code
open scoped BigOperators LinearCode

universe u v w k l

section CoreResults
variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
         {F : Type} [Field F] [Fintype F] [DecidableEq F]

omit [DecidableEq ι] in
/-- Theorem 1.4 (Main Theorem — Correlated agreement over lines) in [BCIKS20].
Take a Reed-Solomon code of length `ι` and degree `deg`, a proximity-error parameter
pair `(δ, ε)` and two words `u₀` and `u₁`, such that the probability that a random affine
line passing through `u₀` and `u₁` is `δ`-close to Reed-Solomon code is at most `ε`.
Then, the words `u₀` and `u₁` have correlated agreement.

This is the `k = 1` affine-line specialization of the curves keystone
`correlatedAgreement_affine_curves`. Following that keystone, the two list-decoding
residuals are threaded as explicit hypotheses, specialized to `k = 1`:
* `hStrictCoeff` is the [BCIKS20] §5 strict Johnson-branch coefficient-polynomial
  extraction obligation (`StrictCoeffPolysResidual`);
* `hBoundaryCard` is the [BCIKS20] §6.2 closed square-root boundary assembly
  obligation (`BoundaryCardResidual`). -/
theorem RS_correlatedAgreement_affineLines {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    -- Match the curves theorem: at `deg = 0`, the Johnson-branch error bound
    -- can make the list-decoding branch too weak for this statement.
    [NeZero deg]
    -- [BCIKS20] §5: strict Johnson-branch coefficient-polynomial extraction residual,
    -- specialized to the `k = 1` affine line.
    (hStrictCoeff : StrictCoeffPolysResidual (k := 1) (deg := deg) (domain := domain) (δ := δ))
    -- [BCIKS20] §6.2: closed square-root boundary assembly residual,
    -- specialized to the `k = 1` affine line.
    (hBoundaryCard : BoundaryCardResidual (k := 1) (deg := deg) (domain := domain) (δ := δ))
    (hδ : δ ≤ 1 - (ReedSolomon.sqrtRate deg domain)) :
  δ_ε_correlatedAgreementAffineLines (A := F) (F := F) (ι := ι)
    (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) := by
  -- Do casing analysis on `hδ`
  by_cases hδ_uniqueDecodingRegime :
    δ ≤ Code.relativeUniqueDecodingRadius (ι := ι) (F := F) (C := ReedSolomon.code domain deg)
  · exact RS_correlatedAgreement_affineLines_uniqueDecodingRegime (hδ := hδ_uniqueDecodingRegime)
  · classical
    have hcurves := correlatedAgreement_affine_curves (k := 1) (deg := deg)
      (domain := domain) (δ := δ) hStrictCoeff hBoundaryCard hδ
    unfold δ_ε_correlatedAgreementAffineLines
    intro u hprob
    unfold δ_ε_correlatedAgreementCurves at hcurves
    exact hcurves u (by
      simpa [one_mul, Fin.sum_univ_two] using hprob)

omit [DecidableEq ι] in
/-- Strict square-root-radius affine-line capstone. In the strict range, the closed-boundary
residual branch of the curves theorem is impossible, so only the strict coefficient-polynomial
extraction residual is needed. -/
theorem RS_correlatedAgreement_affineLines_strict {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    [NeZero deg]
    (hStrictCoeff : StrictCoeffPolysResidual (k := 1) (deg := deg) (domain := domain) (δ := δ))
    (hδ : δ < 1 - ReedSolomon.sqrtRate deg domain) :
  δ_ε_correlatedAgreementAffineLines (A := F) (F := F) (ι := ι)
    (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) := by
  classical
  have hcurves := correlatedAgreement_affine_curves_of_strict_coeff_polys
    (k := 1) (deg := deg) (domain := domain) (δ := δ) hδ
    (fun hk u hprob hJ P hP => hStrictCoeff hk u hprob hJ hδ P hP)
  unfold δ_ε_correlatedAgreementAffineLines
  intro u hprob
  unfold δ_ε_correlatedAgreementCurves at hcurves
  exact hcurves u (by
    simpa [one_mul, Fin.sum_univ_two] using hprob)

omit [DecidableEq ι] in
/-- Strict positive-radius affine-line capstone. This is the positive-`δ` API form used by
the BCIKS20 proximity-gap statements; the current proof only needs the strict square-root
upper bound, so the positivity hypothesis is retained as a harmless interface adapter. -/
theorem RS_correlatedAgreement_affineLines_strict_pos {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    [NeZero deg]
    (_hδ_pos : 0 < δ)
    (hStrictCoeff : StrictCoeffPolysResidual (k := 1) (deg := deg) (domain := domain) (δ := δ))
    (hδ : δ < 1 - ReedSolomon.sqrtRate deg domain) :
  δ_ε_correlatedAgreementAffineLines (A := F) (F := F) (ι := ι)
    (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) :=
  RS_correlatedAgreement_affineLines_strict (ι := ι) (F := F) (deg := deg)
    (domain := domain) (δ := δ) hStrictCoeff hδ

omit [DecidableEq ι] in
/-- Strict square-root-radius affine-line capstone with the §5 Johnson branch supplied by the
verified `betaRec` capsule. This is the affine-line public front door corresponding to
`KeystoneStrictResidual.correlatedAgreement_affine_curves_johnson_of_betaRec_strict`. -/
theorem RS_correlatedAgreement_affineLines_johnson_of_betaRec_strict
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hδ : δ < 1 - ReedSolomon.sqrtRate deg domain)
    (hInput : ∀ (_hk : 0 < 1) (u : WordStack F (Fin 2) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          (((1 : ℕ) : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      δ < 1 - ReedSolomon.sqrtRate deg domain →
      ArkLib.KeystoneStrictResidual.BetaCurveInput
        (k := 1) (deg := deg) (domain := domain) (δ := δ) u) :
  δ_ε_correlatedAgreementAffineLines (A := F) (F := F) (ι := ι)
    (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) :=
  RS_correlatedAgreement_affineLines_strict (ι := ι) (F := F) (deg := deg)
    (domain := domain) (δ := δ)
    (ArkLib.KeystoneStrictResidual.strictCoeffPolysResidual_of_betaRec
      (k := 1) (deg := deg) (domain := domain) (δ := δ) hInput)
    hδ

omit [DecidableEq ι] in
/-- Closed-boundary affine-line capstone with the strict Johnson branch supplied by the verified
`betaRec` capsule and the square-root boundary branch supplied by explicit boundary cardinality
and coefficient-polynomial data. -/
theorem RS_correlatedAgreement_affineLines_johnson_of_betaRec
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain)
    (hInput : ∀ (_hk : 0 < 1) (u : WordStack F (Fin 2) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          (((1 : ℕ) : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      δ < 1 - ReedSolomon.sqrtRate deg domain →
      ArkLib.KeystoneStrictResidual.BetaCurveInput
        (k := 1) (deg := deg) (domain := domain) (δ := δ) u)
    (hBoundaryData : ∀ (_hk : 0 < 1) (u : WordStack F (Fin 2) ι),
      δ = 1 - ReedSolomon.sqrtRate deg domain →
      0 < (RS_goodCoeffsCurve (k := 1) (deg := deg) (domain := domain) u δ).card →
      ((RS_goodCoeffsCurve (k := 1) (deg := deg) (domain := domain) u δ).card > 1) ∧
      ((RS_goodCoeffsCurve (k := 1) (deg := deg) (domain := domain) u δ).card ≥
        (Fintype.card ι + 1) * 1) ∧
      (∀ P : F → Polynomial F,
        (∀ z ∈ RS_goodCoeffsCurve (k := 1) (deg := deg) (domain := domain) u δ,
          (P z).natDegree < deg ∧
            δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • u t,
              (P z).eval ∘ domain) ≤ δ) →
          ∃ B : ℕ → Polynomial F,
            (∀ j < deg, (B j).natDegree < 2) ∧
              ∀ z ∈ RS_goodCoeffsCurve (k := 1) (deg := deg) (domain := domain) u δ,
                ∀ j < deg, (P z).coeff j = (B j).eval z)) :
  δ_ε_correlatedAgreementAffineLines (A := F) (F := F) (ι := ι)
    (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) :=
  RS_correlatedAgreement_affineLines (ι := ι) (F := F) (deg := deg)
    (domain := domain) (δ := δ)
    (ArkLib.KeystoneStrictResidual.strictCoeffPolysResidual_of_betaRec
      (k := 1) (deg := deg) (domain := domain) (δ := δ) hInput)
    (ArkLib.BoundaryDischarge.boundaryCardResidual_of_boundary_cards_and_coeffPolys
      (k := 1) (deg := deg) (domain := domain) (δ := δ) hBoundaryData)
    hδ

omit [DecidableEq ι] in
/-- Closed-boundary affine-line capstone with the strict Johnson branch supplied by the verified
`betaRec` capsule and the square-root boundary reduced by the quantization split in
`BoundaryCardResidual.lean`.

Compared with `RS_correlatedAgreement_affineLines_johnson_of_betaRec`, this consumes the smaller
boundary surface:
* a strict-subradius positive-good-set producer for the non-lattice boundary levels;
* the isolated lattice residual `BoundaryCardLatticeResidual` for the exact `1/n` boundary points.
-/
theorem RS_correlatedAgreement_affineLines_johnson_of_betaRec_lattice_residual
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain)
    (hInput : ∀ (_hk : 0 < 1) (u : WordStack F (Fin 2) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          (((1 : ℕ) : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      δ < 1 - ReedSolomon.sqrtRate deg domain →
      ArkLib.KeystoneStrictResidual.BetaCurveInput
        (k := 1) (deg := deg) (domain := domain) (δ := δ) u)
    (hStrictBoundary : ∀ (u : WordStack F (Fin 2) ι) (δ' : ℝ≥0),
      δ' < δ →
      Nat.floor (δ' * Fintype.card ι) = Nat.floor (δ * Fintype.card ι) →
      0 < (RS_goodCoeffsCurve (k := 1) (deg := deg) (domain := domain) u δ').card →
      jointAgreement (C := ReedSolomon.code domain deg) (δ := δ') (W := u))
    (hLattice :
      ArkLib.BoundaryCardResidual.BoundaryCardLatticeResidual
        (k := 1) (deg := deg) (domain := domain) (δ := δ)) :
  δ_ε_correlatedAgreementAffineLines (A := F) (F := F) (ι := ι)
    (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) :=
  RS_correlatedAgreement_affineLines (ι := ι) (F := F) (deg := deg)
    (domain := domain) (δ := δ)
    (ArkLib.KeystoneStrictResidual.strictCoeffPolysResidual_of_betaRec
      (k := 1) (deg := deg) (domain := domain) (δ := δ) hInput)
    (ArkLib.BoundaryCardResidual.boundaryCardResidual_of_lattice_residual
      (k := 1) (deg := deg) (domain := domain) (δ := δ) hLattice hStrictBoundary)
    hδ

end CoreResults

end ProximityGap
