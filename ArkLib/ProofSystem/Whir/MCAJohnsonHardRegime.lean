import ArkLib.ProofSystem.Whir.MCAJohnsonTrivialRegime

/-! # MCA conjecture: reduction to the hard regime only

The full `hasMutualCorrAgreement` follows from a bound on the proximity-condition
probability *only in the regime where `errStar δ < 1`* — the trivial regime
(`errStar δ ≥ 1`) is discharged automatically by `Pr ≤ 1`. This isolates the
ENTIRE remaining mathematical content of the MCA Johnson conjecture to the
large-field/small-error regime, which the Guruswami–Sudan list-correlated-
agreement at the `(1−δ)` Johnson radius (`rs_epsMCA_johnson_range_bchks25`, the
curve keystone) supplies via the `mca_affineLine_of_epsMCA_bound` reduction. -/

namespace MCAJohnson

open MutualCorrAgreement ProbabilityTheory PMF Generator
open scoped NNReal ENNReal

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
  {ι : Type} [Fintype ι] [Nonempty ι]

/-- **MCA from the hard regime.** If the proximity-condition probability is
bounded by `errStar δ` whenever `errStar δ < 1`, then mutual correlated agreement
holds in full — the `errStar δ ≥ 1` cases are free (`Pr ≤ 1 ≤ errStar δ`). Thus
the complete conjecture reduces to its large-field content. -/
theorem mca_of_hard_regime
    (Gen : ProximityGenerator ι F) [Fintype Gen.parℓ]
    (BStar : ℝ) (errStar : ℝ → ENNReal)
    (hhard : ∀ (f : Gen.parℓ → ι → F) (δ : ℝ≥0), (0 < δ ∧ δ < 1 - BStar) →
      errStar δ < 1 →
      haveI := Gen.Gen_nonempty
      Pr_{
        let r ← $ᵖ Gen.Gen}[MutualCorrAgreement.proximityCondition f δ r Gen.C] ≤ errStar δ) :
    hasMutualCorrAgreement Gen BStar errStar := by
  intro f δ hδ
  by_cases h : errStar (δ : ℝ) < 1
  · exact hhard f δ hδ h
  · exact le_trans (PMF.coe_le_one _ _) (not_lt.mp h)

end MCAJohnson
