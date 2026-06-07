import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2Reabsorb

open scoped BigOperators
open Finset Polynomial Polynomial.Bivariate ArkLib.PowerSeriesComposition
open BCIKS20AppendixA ProximityPrize.BCIKS20.GammaGenuine

namespace BCIKS20.HenselNumerator

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

-- The crux bridge needed for EVERY order: embed(B_coeff i1 λ) in terms of hasseEvalAtRoot.
-- B_coeff = prefactor • hasseCoeffRepr𝒪. 
-- hasseCoeffRepr𝒪 i1 m = mk (evalX(C x₀)(Δ_X^{i1} Δ_Y^m R)).
-- embeddingOf𝒪Into𝕃 (mk p) = liftBivariate p = eval₂ lift (T/W) p  (the un-cleared form!).
-- hasseEvalAtRoot i1 m = eval₂ lift (T/W) (evalX(C x₀)(Δ_X^{i1} Δ_Y^m R)) -- SAME!
-- So embed(hasseCoeffRepr𝒪 i1 m) = hasseEvalAtRoot i1 m  directly (no W-clearing needed for embed!).
-- The "cleared" form was only for the WEIGHT bound. For embedding equality it's direct.

theorem embed_hasseCoeffRepr𝒪 (x₀ : F) (R : F[X][X][Y]) (i1 m : ℕ) :
    embeddingOf𝒪Into𝕃 H (hasseCoeffRepr𝒪 H x₀ R i1 m) = hasseEvalAtRoot H x₀ R i1 m := by
  unfold hasseCoeffRepr𝒪 hasseEvalAtRoot
  rw [embeddingOf𝒪Into𝕃_mk, liftBivariate_eq_eval₂_functionFieldT]
  rfl

theorem embed_B_coeff (x₀ : F) (R : F[X][X][Y]) (i1 : ℕ) {m : ℕ} (lam : Nat.Partition m) :
    embeddingOf𝒪Into𝕃 H (B_coeff H x₀ R i1 lam)
      = (prefactor R.natDegree i1 lam : 𝕃 H) * hasseEvalAtRoot H x₀ R i1 (sigmaLambda lam) := by
  unfold B_coeff
  rw [map_nsmul, embed_hasseCoeffRepr𝒪, nsmul_eq_mul]

#check @embed_B_coeff

end BCIKS20.HenselNumerator
