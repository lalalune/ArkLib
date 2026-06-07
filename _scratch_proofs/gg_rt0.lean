import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2Close

open scoped BigOperators
open Finset Polynomial Polynomial.Bivariate ArkLib.PowerSeriesComposition
open BCIKS20AppendixA ProximityPrize.BCIKS20.GammaGenuine
open ProximityPrize.HenselSeriesCoeff

namespace BCIKS20.HenselNumerator

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

-- At t=0: restrictedFaaDiBrunoSum sums over i ∈ range (deg+1), ab ∈ antidiagonal 1 = {(0,1),(1,0)},
-- m ∈ image valueMultiset of finsuppAntidiag (range i) ab.2, with (1 ∉ m) guard.
-- For ab=(0,1): ab.2=1, m has sum 1, so m contains a 1 ⟹ killed by (1∉m) guard (if 1∈m).
--   Actually valueMultiset of a finsupp summing to 1 into range i parts: one part is 1. So 1∈m ⟹ killed.
-- For ab=(1,0): ab.2=0, m has sum 0 = all zeros, card = i. 1∉m always. countPerms(replicate i 0)=1.
--   prod = (coeff 0 βHA)^i = α₀^i.  factor: lift((evalX (Δ_X^1 R)).coeff i).
-- So restricted_0 = ∑ i, lift((evalX (Δ_X^1 R)).coeff i) · α₀^i  (the (1,0) terms only).
-- This is exactly eval₂-like: ∑ i coeff_i(Δ_X R at x₀) α₀^i = derivative-eval = relates to ζ!

-- Let me just check it typechecks and see the unfolded form for ab in antidiagonal 1.
example : (Finset.antidiagonal 1 : Finset (ℕ × ℕ)) = {(0,1),(1,0)} := by decide

end BCIKS20.HenselNumerator
