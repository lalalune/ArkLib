import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2Assembly

open scoped BigOperators
open Finset Polynomial Polynomial.Bivariate ArkLib.PowerSeriesComposition BCIKS20AppendixA ProximityPrize.BCIKS20.GammaGenuine

namespace BCIKS20.HenselNumerator

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- **SUB-LEMMA E — the clean bridge from `hasseEvalAtRoot` to the embedded cleared
representative.**  Inverting the `W`-clearing embedding identity
`embeddingOf𝒪Into𝕃_hasseCoeffRepr𝒪_cleared`: dividing by `W^{natDegreeY p}` (nonzero, since
`W = liftToFunctionField H.leadingCoeff ≠ 0`) exhibits the `Y↦T/W` evaluation
`hasseEvalAtRoot` as the embedded cleared `𝒪`-representative scaled down by the cleared
`W`-power. -/
lemma hasseEvalAtRoot_eq_embedding_cleared_div (x₀ : F) (R : F[X][X][Y]) (i1 m : ℕ) :
    hasseEvalAtRoot H x₀ R i1 m
      = embeddingOf𝒪Into𝕃 H
          (Ideal.Quotient.mk (Ideal.span {H_tilde' H})
            (hasseCoeffRepr𝒪_cleared H x₀ R i1 m) : 𝒪 H)
        / liftToFunctionField (H := H) H.leadingCoeff
            ^ Bivariate.natDegreeY
                (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX i1 (hasseDerivY m R))) := by
  rw [embeddingOf𝒪Into𝕃_hasseCoeffRepr𝒪_cleared]
  rw [mul_comm,
      mul_div_assoc,
      div_self (pow_ne_zero _ (liftToFunctionField_leadingCoeff_ne_zero (H := H))),
      mul_one]

#print axioms hasseEvalAtRoot_eq_embedding_cleared_div

end BCIKS20.HenselNumerator
