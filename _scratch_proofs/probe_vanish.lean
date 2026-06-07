import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2Assembly

open scoped BigOperators
open Finset Polynomial Polynomial.Bivariate ArkLib.PowerSeriesComposition
open BCIKS20AppendixA ProximityPrize.BCIKS20.GammaGenuine

namespace BCIKS20.HenselNumerator

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

-- Vanishing fact A: f i = 0 for i > R.natDegree  (via P₁ degree)
example (x₀ : F) (R : F[X][X][Y]) (i1 s i : ℕ) (hi : R.natDegree < i) :
    (i.choose s) • (liftToFunctionField (H:=H)
        ((Bivariate.evalX (Polynomial.C x₀) (hasseDerivX i1 R)).coeff i) * (α₀ H) ^ (i - s)) = 0 := by
  have hP1 : (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX i1 R)).natDegree ≤ R.natDegree := by
    have h1 : Bivariate.natDegreeY (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX i1 R))
        ≤ Bivariate.natDegreeY R :=
      (evalX_natDegreeY_le (Polynomial.C x₀) _).trans (hasseDerivX_natDegreeY_le i1 R)
    simpa [Bivariate.natDegreeY] using h1
  have hcoeff : (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX i1 R)).coeff i = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  simp [hcoeff]

-- Vanishing fact B: f i = 0 for i > M+s
example (x₀ : F) (R : F[X][X][Y]) (i1 s i : ℕ)
    (hi : (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX i1 (hasseDerivY s R))).natDegree + s < i) :
    (i.choose s) • (liftToFunctionField (H:=H)
        ((Bivariate.evalX (Polynomial.C x₀) (hasseDerivX i1 R)).coeff i) * (α₀ H) ^ (i - s)) = 0 := by
  have hs : s ≤ i := by omega
  have hcomm := evalX_hasseDeriv_Y_coeff x₀ R i1 s (i - s)
  rw [Nat.sub_add_cancel hs] at hcomm
  have hMcoeff : (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX i1 (hasseDerivY s R))).coeff (i - s) = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  rw [hMcoeff] at hcomm
  -- hcomm : 0 = i.choose s • (evalX..hasseDerivX i1 R).coeff i
  -- Goal: i.choose s • (lift(P₁.coeff i) * α₀^(i-s)) = 0
  rw [← smul_mul_assoc, ← map_nsmul (liftToFunctionField (H := H)), ← hcomm, map_zero, zero_mul]

end BCIKS20.HenselNumerator
