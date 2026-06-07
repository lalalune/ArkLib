import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2Close
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2MatchRoot

namespace BCIKS20.HenselNumerator

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- Mathematical residual for the P2 restricted Faà-di-Bruno match.
This is the single open step required to close the lift identity for P2.
It states that the restricted Faà-di-Bruno sum matches the assembled series coefficient.
See GitHub Issue #139 for the mathematical resolution of the cleared/uncleared gap. -/
axiom restrictedFaaDiBrunoMatch_residual (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) : RestrictedFaaDiBrunoMatch H x₀ R hHyp

/-- Discharges the full P2 closed goal using the open mathematical residual. -/
theorem P2_closed_of_residual (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) :
    (Polynomial.eval (βHenselAssembled H x₀ R hHyp) (Q x₀ R H) = 0)
    ∧ (∀ t : ℕ, embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp t)
        = αGenuine H x₀ R hHyp t
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1)) :=
  P2_closed H x₀ R hHyp (restrictedFaaDiBrunoMatch_residual H x₀ R hHyp)

end BCIKS20.HenselNumerator
