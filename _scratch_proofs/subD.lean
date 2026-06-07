import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2Assembly

open scoped BigOperators
open Finset Polynomial Polynomial.Bivariate ArkLib.PowerSeriesComposition BCIKS20AppendixA ProximityPrize.BCIKS20.GammaGenuine

namespace BCIKS20.HenselNumerator

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

theorem antidiag_reindex {M : Type*} [AddCommMonoid M] (t : ℕ) (f : ℕ × ℕ → M) :
  ∑ ab ∈ Finset.antidiagonal (t + 1), f ab
  = ∑ i1 ∈ Finset.range (t + 2), f (i1, t + 1 - i1) := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

end BCIKS20.HenselNumerator
