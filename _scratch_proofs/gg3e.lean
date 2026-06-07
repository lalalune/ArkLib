import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2Assembly
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2Reabsorb
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2Vanish

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

-- Probe: can the Y-degree reabsorption be stated cleanly per (i1, m)?
-- LHS-per-(i1,m): ∑_{i ∈ range(degQ+1)} L_i · C(i,m) · α₀^{i-m}
--   where L_i = lift((Δ_X^{i1} R)|x₀).coeff i, α₀ = T/W.
-- RHS object: hasseEvalAtRoot i1 m = ∑_j C(j,m)·lift((Δ_X^{i1}R)|x₀.coeff j)·(T/W)^{j-m}.
-- These match IF the ranges agree.  hasseEvalAtRoot_eq_binomReindex gives the j-range as
-- map (addRight m) (range (natDegreeY(Δ_X^{i1}(Δ_Y^m R))|x₀ + 1)).
-- The LHS uses range(degQ + 1).  natDegreeY differences are absorbed by zero coeffs.
-- So the per-(i1,m) Y-degree reabsorption is: ∑_{i∈range(degQ+1)} L_i·C(i,m)·α₀^{i-m} = hasseEvalAtRoot i1 m.
-- This is a finite-sum-range extension question (extra terms vanish since coeff beyond degree = 0).

-- Test the cleanest case m=0: hasseEvalAtRoot i1 0 = ∑_i L_i · α₀^i  (eval at α₀).
example (x₀ : F) (R : F[X][X][Y]) (i1 : ℕ) :
    hasseEvalAtRoot H x₀ R i1 0
      = Polynomial.eval₂ liftToFunctionField
          (functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff)
          (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX i1 R)) := by
  unfold hasseEvalAtRoot
  simp only [hasseDerivY]
  rw [Polynomial.hasseDeriv_zero]
  rfl

end BCIKS20.HenselNumerator
