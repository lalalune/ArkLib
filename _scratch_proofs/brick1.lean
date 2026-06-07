import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2BijectionApply

open scoped BigOperators
open Finset Polynomial Polynomial.Bivariate ArkLib.PowerSeriesComposition
open BCIKS20AppendixA ProximityPrize.BCIKS20.GammaGenuine

namespace BCIKS20.HenselNumerator

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

-- BRICK 1: the outer Y-degree i-sum (with α₀^{i-s} and C(i,s) weights) collapses to hasseEvalAtRoot i1 s.
-- This is the α₀-Taylor resummation, the bridge from the Faà-di-Bruno LHS into B_coeff/hasseEvalAtRoot.
example (x₀ : F) (R : F[X][X][Y]) (i1 s : ℕ) :
    hasseEvalAtRoot H x₀ R i1 s
      = ∑ i ∈ Finset.range
            ((Bivariate.evalX (Polynomial.C x₀)
                (hasseDerivX i1 (hasseDerivY s R))).natDegree + 1 + s),
          (i.choose s)
            • (liftToFunctionField (H := H)
                  ((Bivariate.evalX (Polynomial.C x₀) (hasseDerivX i1 R)).coeff i)
                * (α₀ H) ^ (i - s)) := by
  rw [hasseEvalAtRoot_eq_taylorSum, α₀]
  symm
  set M := (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX i1 (hasseDerivY s R))).natDegree with hM
  -- targetSum (range M+1+s) = taylorSum (range M+1): drop i<s terms, reindex i = s + j
  rw [Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive _ (Nat.zero_le s) (by omega : s ≤ M + 1 + s),
      Finset.sum_eq_zero (s := Finset.Ico 0 s) (fun i hi => by
        rw [Finset.mem_Ico] at hi
        rw [Nat.choose_eq_zero_of_lt hi.2, zero_smul]),
      zero_add, Finset.sum_Ico_eq_sum_range]
  apply Finset.sum_congr (by rw [Nat.add_sub_cancel])
  intro j _
  rw [Nat.add_sub_cancel_left, Nat.add_comm s j]

end BCIKS20.HenselNumerator
