/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AlphaWeight

/-!
# The 𝒪-clearing product is a non-zero-divisor (BCIKS20 A.4, issue #138)

The (A.4) lift normalizes `βHensel … t` by the **clearing product** `W^{t+1}·ξ^{2t-1} ∈ 𝒪 H`.
For the `DivWeightLe`/`AlphaGenuineRegularWeightLe` quotient `a` to be well-defined and unique, this
clearing product must be a non-zero-divisor.

* `embeddingOf𝒪Into𝕃_clearingProduct` — the `Y↦T` embedding of the clearing product is the genuine
  `𝕃`-denominator `(lift lc)^{t+1}·(embed ξ)^{2t-1}` (the `den` of `den_ne_zero`). A one-line
  `map_*` rewrite on top of the proven `embeddingOf𝒪Into𝕃_W𝒪` (the #138 sibling of #139's
  `embeddingOf𝒪Into𝕃_hasseCoeffRepr𝒪_uncleared`).
* `clearingProduct_ne_zero` — hence the clearing product is nonzero in `𝒪 H`: its embedding equals
  the nonzero denominator (`den_ne_zero`), and `embeddingOf𝒪Into𝕃` sends `0 ↦ 0`.
-/

open Polynomial Polynomial.Bivariate
open BCIKS20AppendixA
open ProximityPrize.BCIKS20.GammaGenuine

namespace BCIKS20.HenselNumerator.AlphaWeight

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- The `Y↦T` embedding of the (A.4) clearing product `W^{t+1}·ξ^{2t-1}` is the genuine
`𝕃`-denominator `(lift lc)^{t+1}·(embed ξ)^{2t-1}`. -/
theorem embeddingOf𝒪Into𝕃_clearingProduct (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ) :
    embeddingOf𝒪Into𝕃 H ((W𝒪 H) ^ (t + 1) * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * t - 1))
      = (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1)
          * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1) := by
  rw [map_mul, map_pow, map_pow, embeddingOf𝒪Into𝕃_W𝒪]

/-- The (A.4) clearing product is a non-zero-divisor in `𝒪 H` (its embedding is the nonzero
denominator), so the `DivWeightLe` quotient is well-defined. -/
theorem clearingProduct_ne_zero (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ) :
    ((W𝒪 H) ^ (t + 1) * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * t - 1)) ≠ 0 := by
  intro hzero
  have hden := den_ne_zero H x₀ R hHyp t
  apply hden
  rw [← embeddingOf𝒪Into𝕃_clearingProduct H x₀ R hHyp t, hzero, map_zero]

end BCIKS20.HenselNumerator.AlphaWeight

#print axioms BCIKS20.HenselNumerator.AlphaWeight.embeddingOf𝒪Into𝕃_clearingProduct
#print axioms BCIKS20.HenselNumerator.AlphaWeight.clearingProduct_ne_zero
