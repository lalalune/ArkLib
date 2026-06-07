import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2Assembly

open scoped BigOperators
open Finset Polynomial Polynomial.Bivariate ArkLib.PowerSeriesComposition
open BCIKS20AppendixA ProximityPrize.BCIKS20.GammaGenuine

namespace BCIKS20.HenselNumerator

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

-- P₁.natDegree ≤ R.natDegree where P₁ = evalX(C x₀)(hasseDerivX i1 R)
example (x₀ : F) (R : F[X][X][Y]) (i1 : ℕ) :
    (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX i1 R)).natDegree ≤ R.natDegree := by
  -- natDegree of an F[X][Y] poly = natDegreeY
  have h1 : Bivariate.natDegreeY (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX i1 R))
      ≤ Bivariate.natDegreeY R := by
    refine (evalX_natDegreeY_le (Polynomial.C x₀) _).trans ?_
    exact hasseDerivX_natDegreeY_le i1 R
  -- natDegreeY = natDegree (definitionally? check)
  simpa [Bivariate.natDegreeY] using h1

end BCIKS20.HenselNumerator
