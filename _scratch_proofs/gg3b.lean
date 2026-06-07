import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2Assembly
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2Reabsorb
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2Vanish

/-! Probe the structural shape of the per-order partition match for a real attempt. -/

noncomputable section

open scoped BigOperators
open Finset
open Polynomial Polynomial.Bivariate
open ArkLib.PowerSeriesComposition
open BCIKS20AppendixA
open ProximityPrize.BCIKS20.GammaGenuine

namespace BCIKS20.HenselNumerator

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

-- Goal surface: RestrictedFaaDiBrunoPartitionMatchAt unfolds to LHS = RHS.
-- LHS = restrictedFaaDiBrunoPartitionForm (over Y-degree i, X-Taylor ab, partition λ⊢ab.2)
-- RHS = restrictedMatchRecursionPartitionForm = ζ·(recSum/den)
--   recSum over (i1, λ⊢t+1-i1), den = W^{t+2}·ξ^{2(t+1)-1}.

set_option maxHeartbeats 1000000 in
example (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ) :
    RestrictedFaaDiBrunoPartitionMatchAt H x₀ R hHyp t ↔
    (restrictedFaaDiBrunoPartitionForm H x₀ R hHyp t
      = restrictedMatchRecursionPartitionForm H x₀ R hHyp t) := Iff.rfl

-- Check the recursion-side denominator-cleared form: multiply both sides by den.
-- We want to show LHS·den = ζ·recSum  (since den ≠ 0).
-- den ≠ 0 is den_ne_zero (t+1 - 1 = t? no: den uses t+1). Let's confirm den_ne_zero shape.
#check @den_ne_zero
#check @embeddingOf𝒪Into𝕃_hasseCoeffRepr𝒪_cleared
#check @hasseCoeffRepr𝒪_cleared
#check @B_coeff
#check @hasseCoeffRepr𝒪
#check @prefactor_eq_countPerms
#check @ClaimA2.embeddingOf𝒪Into𝕃_ξ
#check @hasseEvalAtRoot_eq_binomReindex
#check @partitionProd_mul

-- The B_coeff embedding: B_coeff = prefactor • hasseCoeffRepr𝒪. Its embedding?
example (x₀ : F) (R : F[X][X][Y]) (i1 m : ℕ) (lam : Nat.Partition m) :
    embeddingOf𝒪Into𝕃 H (B_coeff H x₀ R i1 lam)
      = (lam.parts.countPerms : 𝕃 H) * embeddingOf𝒪Into𝕃 H (hasseCoeffRepr𝒪 H x₀ R i1 (sigmaLambda lam)) := by
  rw [B_coeff, prefactor_eq_countPerms, nsmul_eq_mul, map_mul, map_natCast]

end BCIKS20.HenselNumerator
