import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2Assembly

open scoped BigOperators
open Finset Polynomial Polynomial.Bivariate ArkLib.PowerSeriesComposition
open BCIKS20AppendixA ProximityPrize.BCIKS20.GammaGenuine

namespace BCIKS20.HenselNumerator

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

-- Inspect: partitions of 0 and 1.
-- Nat.Partition 0: unique (empty parts). card = 0.
-- Nat.Partition 1: unique = indiscrete 1 (one part {1}). card = 1.
example : Fintype.card (Nat.Partition 0) = 1 := by decide
example : Fintype.card (Nat.Partition 1) = 1 := by decide

-- At t=0, ab ∈ {(0,1),(1,0)}.
-- ab=(0,1): λ ⊢ 1, |λ|≤i, (1∉λ). The only λ⊢1 is indiscrete{1}, which HAS part 1, so (1∉λ) FALSE.
--   ⟹ filter EMPTY ⟹ inner sum = 0. So ab=(0,1) contributes 0.
-- ab=(1,0): λ ⊢ 0, |λ|≤i, (1∉λ). only λ=empty (card 0 ≤ i always, 1∉empty TRUE).
--   term: (C(i,0)*countPerms empty) • (α₀^{i-0} * (empty.map ...).prod)
--        = (1 * 1) • (α₀^i * 1) = α₀^i.
--   factor: lift((evalX(Δ_X^1 R)).coeff i).
-- So LHS_0 = ∑ i ∈ range(deg+1), lift((evalX(Δ_X^1 R)).coeff i) * α₀^i.

-- This is exactly eval₂ lift α₀ (evalX(C x₀)(Δ_X^1 R)) ... = hasseEvalAtRoot at (i1=1, m=0) essentially!
-- Actually hasseEvalAtRoot H x₀ R 1 0 = eval₂ lift (T/W) (evalX(C x₀)(Δ_X^1 (Δ_Y^0 R)))
--   = eval₂ lift α₀ (evalX(C x₀)(Δ_X^1 R)).   And α₀ = T/W.   YES.
-- And the RHS at t=0 has i1∈{0,1}, i1=0 excluded (only λ=indiscrete{1} which is filtered out),
--   i1=1: λ⊢0 empty. term W^0·ξ^0·embed(B_coeff 1 ∅)·embed(β₀). B_coeff 1 ∅ = prefactor·hasseCoeffRepr.

#check @hasseEvalAtRoot_eq_taylorSum
#check @restrictedFaaDiBrunoPartitionForm

end BCIKS20.HenselNumerator
