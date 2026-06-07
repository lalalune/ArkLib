import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2Assembly

open scoped BigOperators
open Finset Polynomial Polynomial.Bivariate ArkLib.PowerSeriesComposition
open BCIKS20AppendixA ProximityPrize.BCIKS20.GammaGenuine

namespace BCIKS20.HenselNumerator

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

set_option linter.unusedSectionVars false

-- ===== BRIDGE 1 (HONEST form) =====
-- The prompt's stated bridge1 (emb(hasseCoeffRepr𝒪) = W^N · hasseEvalAtRoot) is FALSE
-- for the un-cleared representative: emb(hasseCoeffRepr𝒪) = liftBivariate p = eval₂ T p,
-- whereas W^N·hasseEvalAtRoot = W^N·eval₂(T/W) p = ∑ lift(p.coeff i)·T^i·W^(N-i), which differs
-- per-term by W^(N-i). The W^N·hasseEvalAtRoot form holds ONLY for the cleared representative
-- (already proven: embeddingOf𝒪Into𝕃_hasseCoeffRepr𝒪_cleared). Below is the TRUE bridge.
theorem bridge1_honest (x₀ : F) (R : F[X][X][Y]) (i1 m : ℕ) :
    embeddingOf𝒪Into𝕃 H (hasseCoeffRepr𝒪 H x₀ R i1 m)
      = liftBivariate (H := H)
          (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX i1 (hasseDerivY m R))) := by
  rw [hasseCoeffRepr𝒪, embeddingOf𝒪Into𝕃_mk]

-- Equivalent eval₂ form, for assembly use.
theorem bridge1_eval₂ (x₀ : F) (R : F[X][X][Y]) (i1 m : ℕ) :
    embeddingOf𝒪Into𝕃 H (hasseCoeffRepr𝒪 H x₀ R i1 m)
      = Polynomial.eval₂ liftToFunctionField (functionFieldT (H := H))
          (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX i1 (hasseDerivY m R))) := by
  rw [bridge1_honest, liftBivariate_eq_eval₂_functionFieldT]

end BCIKS20.HenselNumerator
