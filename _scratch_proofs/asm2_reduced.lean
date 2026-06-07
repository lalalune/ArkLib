import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2Assembly

open scoped BigOperators
open Finset Polynomial Polynomial.Bivariate ArkLib.PowerSeriesComposition
open BCIKS20AppendixA ProximityPrize.BCIKS20.GammaGenuine

namespace BCIKS20.HenselNumerator

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

-- After STEP0-STEP7 (cancelling the common countPerms·∏_l emb(βHensel l) and using
-- partitionPowerClear / embed_W𝒪 / prefactor_eq_countPerms), the per-(i1,lam) residual
-- of the keystone reduces (W,ξ exponent arithmetic with c+i1 = t+1, card = sigmaLambda) to:
--
--     hasseEvalAtRoot(i1,card) · ξ · W^{t+2}  =  liftBivariate p · W^{t+δ+card}
--
-- i.e. (dividing) it needs  liftBivariate p  to be a clean W/ξ multiple of  hasseEvalAtRoot.
-- But  liftBivariate p = eval₂ T p  and  hasseEvalAtRoot = eval₂(T/W) p, and these are NOT
-- related by any global power of W (they differ PER Y-degree).  The honest relation is only
-- the cleared one:  W^N · hasseEvalAtRoot = liftBivariate (cleared p) ≠ liftBivariate p.
--
-- Hence the per-term route cannot close: it would require the FALSE bridge1
--   liftBivariate p = W^N · hasseEvalAtRoot.
-- The keystone, as B_coeff is currently defined with the BARE hasseCoeffRepr𝒪 = mk p
-- (rather than the cleared representative), is not closeable by per-(i1,lam) algebra.
--
-- Demonstration that the needed relation is genuinely the cleared one (TRUE), and that the
-- bare one would be required but is FALSE:

-- TRUE (cleared):  W^N · hasseEvalAtRoot = liftBivariate cleared
example (x₀ : F) (R : F[X][X][Y]) (i1 m : ℕ) :
    liftToFunctionField (H:=H) H.leadingCoeff
        ^ (Bivariate.natDegreeY
            (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX i1 (hasseDerivY m R))))
      * hasseEvalAtRoot H x₀ R i1 m
      = liftBivariate (H := H) (hasseCoeffRepr𝒪_cleared H x₀ R i1 m) := by
  rw [← embeddingOf𝒪Into𝕃_mk, embeddingOf𝒪Into𝕃_hasseCoeffRepr𝒪_cleared]

-- The bare B_coeff embedding is liftBivariate p (NOT the cleared one):
example (x₀ : F) (R : F[X][X][Y]) (i1 m : ℕ) :
    embeddingOf𝒪Into𝕃 H (hasseCoeffRepr𝒪 H x₀ R i1 m)
      = liftBivariate (H := H)
          (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX i1 (hasseDerivY m R))) := by
  rw [hasseCoeffRepr𝒪, embeddingOf𝒪Into𝕃_mk]

end BCIKS20.HenselNumerator
