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

-- Reindex antidiagonal(n) -> range(n+1) via ab.1.  Mathlib: Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk
example (t : ℕ) (g : ℕ × ℕ → 𝕃 H) :
    ∑ ab ∈ Finset.antidiagonal (t+1), g ab = ∑ k ∈ Finset.range (t+2), g (k, t+1-k) := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

-- So the LHS partition form can be reindexed by i1 = ab.1.  Now both sides range over
-- i1 ∈ range(t+2) and partitions of (t+1-i1).  Good.
-- Confirm the filters match: LHS has λ⊢ab.2 with |λ|≤i AND (t+1)∉λ; RHS has λ⊢(t+1-i1) with (t+1)∉λ.
-- The |λ|≤i condition is the Y-degree bound, reabsorbed via hasseEvalAtRoot sum over i.

end BCIKS20.HenselNumerator
