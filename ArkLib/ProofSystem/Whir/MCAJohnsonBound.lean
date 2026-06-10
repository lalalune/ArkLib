/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Whir.MCAConjecturePairReduction
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.RemainingCore
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.LocalSeriesProducer

/-!
# Final Johnson MCA Bound Discharge

This file bridges the raw Guruswami-Sudan components into the literal
`mca_johnson_bound_CONJECTURE`. It is the formal composition of the
`MCAConjecturePairReduction` limits with the `RawGSCargo`.
-/

namespace MutualCorrAgreement

/-- The final literal discharge of the Johnson MCA bound conjecture from the explicit raw GS
cargo core. This theorem closes the pipeline, pinning the conjecture onto the known mathematical
boundaries. -/
theorem mca_johnson_bound_CONJECTURE_holds_of_rawGSCargo
    {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (α : F) (φ : ι ↪ F) (m : ℕ) [ReedSolomon.Smooth φ] (exp : Fin 2 ↪ ℕ)
    (hexp0 : exp 0 = 0) (hexp1 : exp 1 = 1)
    (hk : 2 ^ m ≤ Fintype.card ι) (L : ℕ)
    (hL : ∀ δ : ℝ≥0, 0 < δ →
      (δ : ℝ) < 1 - Real.sqrt ((2 ^ m : ℝ) / (Fintype.card ι : ℝ)) →
      (L : ℝ) ≤ (hab25M (Fintype.card ι) (2 ^ m)
          (min (1 - Real.sqrt ((2 ^ m : ℝ) / (Fintype.card ι : ℝ)) - (δ : ℝ))
            (Real.sqrt ((2 ^ m : ℝ) / (Fintype.card ι : ℝ)) / 20)).toNNReal + 1/2) /
        hab25RhoPlus (Fintype.card ι) (2 ^ m) ^ ((1 : ℝ) / 2))
    (hInput : ∀ δ : ℝ≥0, 0 < δ →
      (δ : ℝ) < 1 - Real.sqrt ((2 ^ m : ℝ) / (Fintype.card ι : ℝ)) →
      ∀ (_hk : 0 < 1) (u' : Code.WordStack F (Fin 2) ι),
        Pr_{
          let z ← $ᵖ F}[δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • u' t,
            ReedSolomon.code φ (2 ^ m)) ≤ δ] >
            (((1 : ℕ) : ENNReal) *
              (_root_.ProximityGap.errorBound δ (2 ^ m) φ : ENNReal)) →
        (1 - (LinearCode.rate (ReedSolomon.code φ (2 ^ m)) : ℝ≥0)) / 2 < δ →
        δ < 1 - ReedSolomon.sqrtRate (2 ^ m) φ →
        ∀ P' : F → F[X],
          (∀ z ∈ _root_.ProximityGap.RS_goodCoeffsCurve
              (k := 1) (deg := 2 ^ m) (domain := φ) u' δ,
            (P' z).natDegree < 2 ^ m ∧
              δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • u' t, (P' z).eval ∘ φ) ≤ δ) →
          ArkLib.RawGS304.RawGSCargo
            (k := 1) (deg := 2 ^ m) (domain := φ) (δ := δ) u' P') :
    mca_johnson_bound_CONJECTURE α φ m (Fin 2) exp := by
  have hkpos : NeZero (2 ^ m) := ⟨by positivity⟩
  refine mca_johnson_bound_CONJECTURE_pair_of_claim1_cells α φ m exp hexp0 hexp1 hk L hL ?_
  intro δ hδ0 hδB u
  exact hsteps57_of_rawGSCargo_cell_card_gt φ (hInput δ hδ0 hδB) u

end MutualCorrAgreement
