import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2Close
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AlphaWeight
import ArkLib.Data.CodingTheory.ProximityGap.LineDecodingCoverage



open Polynomial Polynomial.Bivariate BCIKS20AppendixA
open scoped NNReal

-- The following three were previously fabricated `axiom`s that *asserted* open BCIKS20
-- Appendix-A obligations as proven, laundering the proximity axiom audit with false "closed"
-- claims. Two of them are in fact PROVABLY FALSE as stated (for non-monic `H`), so asserting
-- them as axioms made the development unsound. They are now honest non-asserting `def : Prop`
-- named open residuals (route (c) of #111), matching the `RestrictedFaaDiBrunoMatchResidual`
-- discipline in `P2MatchProof.lean`. They are NOT proven and must never be asserted.

/-- **OPEN residual — NOT asserted.** The P2 restricted Faà-di-Bruno match. Provably FALSE for
non-monic `H` (the un-cleared obstruction, `BCIKS20.AlphaWeightClearedObstruction` /
`keystone_at_zero_FALSE`); the genuine statement is the cleared/nominal form. Tracking #139/#140. -/
def restrictedFaaDiBrunoMatch_residual {F : Type} [Field F] {H : F[X][Y]} [Fact (Irreducible H)]
    [Fact (0 < H.natDegree)]
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) : Prop :=
  BCIKS20.HenselNumerator.RestrictedFaaDiBrunoMatch H x₀ R hHyp

/-- **OPEN residual — NOT asserted.** P1 weight-1 invariant. Provably FALSE for non-monic `H`
(`BCIKS20.AlphaWeightClearedObstruction.not_alphaGenuineRegularWeightLe`); the genuine statement is
the cleared form (`alphaWeight_zero_cleared_fixed`). Tracking #139. -/
def alphaGenuineRegularWeightLe_residual {F : Type} [Field F] {H : F[X][Y]} [Fact (Irreducible H)]
    [Fact (0 < H.natDegree)]
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) (D : ℕ) :
    Prop :=
  BCIKS20.HenselNumerator.AlphaWeight.AlphaGenuineRegularWeightLe H x₀ R hHyp hH D

/-- **OPEN residual — NOT asserted.** The unconstrained black-box T4.21 form, formally REFUTED in
`LineDecodingRefutation.lean`. Tracking #141; never assert it. -/
def mcaForallDoubleCover_residual {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]
    (C : Set (ι → A)) (δ : ℝ≥0) : Prop :=
  ProximityGap.MCAForallDoubleCover (F := F) (A := A) C δ
