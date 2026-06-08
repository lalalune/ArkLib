import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.ClearedFaaDiBrunoProof
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2FubiniReabsorb
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2ClearedGap

namespace BCIKS20.HenselNumerator
variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

theorem globalClearedRepresentativeResummation (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ) :
    (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 2)
      * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t + 1)
      * restrictedFaaDiBrunoSum H x₀ R hHyp t
    = - ClaimA2.ζ R x₀ H * embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp (t + 1)) := by
  sorry
end BCIKS20.HenselNumerator
