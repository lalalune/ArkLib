import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2Assembly

open scoped BigOperators
open Finset Polynomial Polynomial.Bivariate ArkLib.PowerSeriesComposition
open BCIKS20AppendixA ProximityPrize.BCIKS20.GammaGenuine

namespace BCIKS20.HenselNumerator

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

-- ========================================================================
-- BRIDGE 1 (CORRECTED).  The prompt's statement
--   emb(mk p) = W^N · hasseEvalAtRoot
-- is FALSE: emb(mk p) = liftBivariate p = eval₂ T p (Y↦T), whereas
--   W^N · hasseEvalAtRoot = W^N · eval₂(T/W) p = liftBivariate (cleared)
-- and  liftBivariate p ≠ liftBivariate cleared  (they differ in EACH Y-degree:
-- the coeff_i term gets weight 1 in `p` but W^{N-i} in `cleared`).
-- Concretely (probe, verified): liftBivariate (C a) = liftToFF a, but the cleared
-- constant term liftBivariate (C (a·W)) = liftToFF a · W.  So bridge1 is off by the
-- per-degree W-rescaling unless every Y-degree i equals N (impossible for deg>0 p).
--
-- The TRUE bridge (what is actually closeable, mirroring the cleared bridge route) is:
theorem bridge1_true (x₀ : F) (R : F[X][X][Y]) (i1 m : ℕ) :
    embeddingOf𝒪Into𝕃 H (hasseCoeffRepr𝒪 H x₀ R i1 m)
      = liftBivariate (H := H)
          (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX i1 (hasseDerivY m R))) := by
  rw [hasseCoeffRepr𝒪, embeddingOf𝒪Into𝕃_mk]

-- and the genuine W-clearing bridge (the cleared representative, already proven in-tree as
-- embeddingOf𝒪Into𝕃_hasseCoeffRepr𝒪_cleared) is what carries the W^N · hasseEvalAtRoot:
theorem bridge1_cleared (x₀ : F) (R : F[X][X][Y]) (i1 m : ℕ) :
    embeddingOf𝒪Into𝕃 H
        (Ideal.Quotient.mk (Ideal.span {H_tilde' H})
          (hasseCoeffRepr𝒪_cleared H x₀ R i1 m) : 𝒪 H)
      = liftToFunctionField (H:=H) H.leadingCoeff
          ^ (Bivariate.natDegreeY
              (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX i1 (hasseDerivY m R))))
        * hasseEvalAtRoot H x₀ R i1 m :=
  embeddingOf𝒪Into𝕃_hasseCoeffRepr𝒪_cleared H x₀ R i1 m

end BCIKS20.HenselNumerator

#print axioms BCIKS20.HenselNumerator.bridge1_true
#print axioms BCIKS20.HenselNumerator.bridge1_cleared
