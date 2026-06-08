import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2Assembly
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2KeystoneReindex
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2FubiniReabsorb

namespace BCIKS20.HenselNumerator

open scoped BigOperators
open Finset Polynomial Polynomial.Bivariate ArkLib.PowerSeriesComposition
open BCIKS20AppendixA ProximityPrize.BCIKS20.GammaGenuine

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

noncomputable def clearedRepresentativeFaaDiBrunoSum (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ) : 𝕃 H :=
  ∑ ab ∈ Finset.antidiagonal (t + 1),
    ∑ lam ∈ (Finset.univ : Finset (Nat.Partition ab.2)).filter
              (fun lam => (t + 1) ∉ lam.parts),
      lam.parts.countPerms
        • (embeddingOf𝒪Into𝕃 H
            (Ideal.Quotient.mk (Ideal.span {H_tilde' H})
              (hasseCoeffRepr𝒪_cleared H x₀ R ab.1 lam.parts.card R.natDegree))
            / (liftToFunctionField (H := H) H.leadingCoeff) ^ R.natDegree
            * (lam.parts.map
                (fun j => PowerSeries.coeff j (βHenselAssembled H x₀ R hHyp))).prod)

/-- The final bridge theorem that ties the double sum to the non-monic Newton-Hensel root
    using the global cleared-representative resummation, fully discharging the non-monic obstruction. -/
theorem globalClearedRepresentativeResummationMatch (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ) :
    restrictedFaaDiBrunoSum H x₀ R hHyp t
      = clearedRepresentativeFaaDiBrunoSum H x₀ R hHyp t := by
  rw [restrictedFaaDiBrunoSum_eq_hasseDoubleSum]
  unfold clearedRepresentativeFaaDiBrunoSum
  refine Finset.sum_congr rfl (fun ab _ => ?_)
  refine Finset.sum_congr rfl (fun lam _ => ?_)
  have h_le : Bivariate.natDegreeY
      (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX ab.1 (hasseDerivY lam.parts.card R))) ≤ R.natDegree := by
    refine le_trans (hasseCoeffRepr𝒪_natDegreeY_le x₀ R ab.1 lam.parts.card) ?_
    exact le_trans (Nat.sub_le _ _) (Bivariate.natDegreeY_le_natDegree R)
  have h_emb := embeddingOf𝒪Into𝕃_hasseCoeffRepr𝒪_cleared x₀ R ab.1 lam.parts.card R.natDegree h_le
  -- h_emb : embedding = W^k * hasseEvalAtRoot
  have hw : liftToFunctionField (H := H) H.leadingCoeff ≠ 0 := liftToFunctionField_leadingCoeff_ne_zero (H := H)
  rw [h_emb]
  rw [mul_div_assoc]
  rw [div_self (pow_ne_zero _ hw)]
  rw [mul_one]

end BCIKS20.HenselNumerator
