import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2FubiniReabsorb
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2ClearedGap
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2Close

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

end BCIKS20.HenselNumerator
