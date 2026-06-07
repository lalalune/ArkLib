import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AlphaWeight

open Polynomial Polynomial.Bivariate
open BCIKS20AppendixA
open ProximityPrize.BCIKS20.GammaGenuine

namespace BCIKS20.HenselNumerator
namespace AlphaWeight

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- CANDIDATE A: general-`t` `Dvd`-form of the genuine clearing residual, from the proven
bridge `βHensel_eq_alpha_mul_of_lift`. Names the clearing divisibility
`W𝒪^{t+1}·ξ^{2t−1} ∣ βHensel t` in `𝒪`, the genuine residual content (without the weight side). -/
theorem clearingProduct_dvd_βHensel_of_alpha (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) (t : ℕ) {a : 𝒪 H}
    (ha : embeddingOf𝒪Into𝕃 H a = αGenuine H x₀ R hHyp t)
    (hlift_t :
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp t)
        = αGenuine H x₀ R hHyp t
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1)) :
    ((W𝒪 H) ^ (t + 1) * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * t - 1)) ∣ βHensel H x₀ R hHyp t := by
  refine ⟨a, ?_⟩
  rw [βHensel_eq_alpha_mul_of_lift H x₀ R hHyp hH t ha hlift_t]
  ring

end AlphaWeight
end BCIKS20.HenselNumerator
