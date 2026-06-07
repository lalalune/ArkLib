import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2Assembly
open Finset Polynomial Polynomial.Bivariate ArkLib.PowerSeriesComposition
open BCIKS20AppendixA ProximityPrize.BCIKS20.GammaGenuine
namespace BCIKS20.HenselNumerator
variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
-- liftBivariate (X+1) = T + 1 (eval₂ T form)
example : liftBivariate (H:=H) (Polynomial.X + 1)
    = functionFieldT (H:=H) + 1 := by
  rw [liftBivariate_eq_eval₂_functionFieldT]
  simp [Polynomial.eval₂_add, Polynomial.eval₂_X, Polynomial.eval₂_one]
-- W * hasseEvalAtRoot-analogue eval₂(T/W)(X+1) = T + W (cleared form), ≠ T+1 unless W=1
example : liftToFunctionField (H:=H) H.leadingCoeff *
    Polynomial.eval₂ liftToFunctionField (functionFieldT (H:=H) / liftToFunctionField (H:=H) H.leadingCoeff) (Polynomial.X + 1)
    = functionFieldT (H:=H) + liftToFunctionField (H:=H) H.leadingCoeff := by
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_X, Polynomial.eval₂_one, mul_add, mul_one]
  rw [mul_div_cancel₀ _ (liftToFunctionField_leadingCoeff_ne_zero (H:=H))]
end BCIKS20.HenselNumerator
