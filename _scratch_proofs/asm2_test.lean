import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2Assembly

open scoped BigOperators
open Finset Polynomial Polynomial.Bivariate ArkLib.PowerSeriesComposition
open BCIKS20AppendixA ProximityPrize.BCIKS20.GammaGenuine

namespace BCIKS20.HenselNumerator

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

-- DECISIVE counterexample-by-instance: specialize to a deg-1-in-Y polynomial p = C a + C b * X
-- (a,b : F[X]).  liftBivariate p = liftToFF a + liftToFF b * T.
-- W^1 * eval₂(T/W) p = W*(liftToFF a + liftToFF b * (T/W)) = W*liftToFF a + liftToFF b * T.
-- These are equal iff liftToFF a = W * liftToFF a, i.e. (W-1)*liftToFF a = 0.
-- For generic a (e.g. a = 1) and W ≠ 1, this fails.  Encode the gap directly:
example (a b : F[X]) :
    liftBivariate (H := H) (Polynomial.C a + Polynomial.C b * Polynomial.X)
      = liftToFunctionField (H := H) a + liftToFunctionField (H := H) b * functionFieldT (H := H) := by
  rw [map_add, map_mul, liftBivariate_C, liftBivariate_C, liftBivariate_X]

example (a b : F[X]) :
    liftToFunctionField (H := H) H.leadingCoeff ^ 1 *
        Polynomial.eval₂ liftToFunctionField
          (functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff)
          (Polynomial.C a + Polynomial.C b * Polynomial.X)
      = liftToFunctionField (H := H) H.leadingCoeff * liftToFunctionField (H := H) a
          + liftToFunctionField (H := H) b * functionFieldT (H := H) := by
  rw [Polynomial.eval₂_add, Polynomial.eval₂_C, Polynomial.eval₂_mul, Polynomial.eval₂_C,
      Polynomial.eval₂_X, pow_one]
  have hW : liftToFunctionField (H := H) H.leadingCoeff ≠ 0 :=
    liftToFunctionField_leadingCoeff_ne_zero (H := H)
  field_simp

-- CONCLUSION: liftBivariate p has constant term  liftToFF a,
--   but  W·eval₂(T/W) p  has constant term  W·liftToFF a.
-- Since emb(mk p) = liftBivariate p and W^N·hasseEvalAtRoot = W·eval₂(T/W) p (N=1 here),
-- bridge1 (emb(mk p) = W^N·hasseEvalAtRoot) is FALSE whenever the Y-constant coeff a ≠ 0
-- and W ≠ 1 — i.e. generically.  The genuine bridge needs the CLEARED representative.

end BCIKS20.HenselNumerator
