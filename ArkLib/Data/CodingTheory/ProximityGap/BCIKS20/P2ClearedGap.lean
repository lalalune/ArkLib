/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2Reabsorb

/-!
# BCIKS20 Appendix A.4 — order-zero P2 obstruction as a cleared/uncleared gap

`P2Reabsorb` reduces the fixed order-zero partition residual to the un-cleared representative
over `W ^ R.natDegree`. This companion pins that target to the proven cleared-representative
bridge `hasseEvalAtRoot_mul_W_pow_eq_embedding_cleared`.

The result isolates the remaining order-zero content as equality, in `𝕃`, between the image of
the un-cleared `hasseCoeffRepr𝒪` representative and the image of the cleared representative,
under the explicit degree match plus the same cancellation hypotheses.
-/

namespace BCIKS20.HenselNumerator

open scoped BigOperators
open Polynomial Polynomial.Bivariate
open BCIKS20AppendixA
open ProximityPrize.BCIKS20.GammaGenuine

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- The fixed order-zero normalized P2 residual is equivalent to equality of the un-cleared
iterated-Hasse representative and the proven cleared representative after embedding into `𝕃`.

The hypotheses keep the actual arithmetic obligations explicit: the legitimate `ζ` and `W`
cancellations, plus the Y-degree match between the cleared representative exponent and
`R.natDegree`. This theorem packages the obstruction; it does not prove the cleared/uncleared
embedding equality or the degree match. -/
theorem t0_residual_iff_uncleared_emb_eq_cleared_emb
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree) (hζ : ClaimA2.ζ R x₀ H ≠ 0)
    (hdeg : Bivariate.natDegreeY
        (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 (hasseDerivY 0 R))) = R.natDegree) :
    RestrictedFaaDiBrunoPartitionMatchAt H x₀ R hHyp 0 ↔
      embeddingOf𝒪Into𝕃 H (hasseCoeffRepr𝒪 H x₀ R 1 0)
        = embeddingOf𝒪Into𝕃 H
            (Ideal.Quotient.mk (Ideal.span {H_tilde' H})
              (hasseCoeffRepr𝒪_cleared H x₀ R 1 0)) := by
  rw [restrictedPartitionMatchAt_zero_iff_unclearedHasseCoeff_div_W_natDegree
      H x₀ R hHyp hd hζ]
  have hW : liftToFunctionField (H := H) H.leadingCoeff ≠ 0 :=
    liftToFunctionField_leadingCoeff_ne_zero (H := H)
  have hbridge :
      hasseEvalAtRoot H x₀ R 1 0
          * liftToFunctionField (H := H) H.leadingCoeff ^ R.natDegree
        = embeddingOf𝒪Into𝕃 H
            (Ideal.Quotient.mk (Ideal.span {H_tilde' H})
              (hasseCoeffRepr𝒪_cleared H x₀ R 1 0)) := by
    rw [← hdeg]
    exact hasseEvalAtRoot_mul_W_pow_eq_embedding_cleared H x₀ R 1 0
  constructor
  · intro h
    rw [← hbridge, h, div_mul_cancel₀ _ (pow_ne_zero _ hW)]
  · intro h
    rw [h, ← hbridge, mul_div_assoc, div_self (pow_ne_zero _ hW), mul_one]

end BCIKS20.HenselNumerator

#print axioms BCIKS20.HenselNumerator.t0_residual_iff_uncleared_emb_eq_cleared_emb
