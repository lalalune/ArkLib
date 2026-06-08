import ArkLib.Data.CodingTheory.ProximityGap.GrandChallenge141PrizeMath

open scoped BigOperators

namespace ArkLib.CodingTheory.Research

/-!
  The Terence Tao Pivot: The Slice Rank Method.
  We deploy Additive Combinatorics to bypass the algebraic geometry constraints 
  of the Guruswami-Sudan interpolation matrices.
-/

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/--
  The Agreement Tensor.
  For a list of polynomials P_i that all agree with a received word r(x),
  we construct a tensor that isolates the diagonal (where P_i = P_j).
-/
def agreement_tensor (P Q : Polynomial F) (_r : F → F) (L : Finset F) : F :=
  -- \sum_{x \in L} (1 - (P(x) - Q(x))^{|F|-1})
  ∑ x ∈ L, (1 - (P.eval x - Q.eval x) ^ (Fintype.card F - 1))

/--
  The Slice Rank Bound.
  By the Ellenberg-Gijswijt cap-set logic, if a tensor is diagonal (non-zero on 
  P=Q and zero on P!=Q), its rank must be exactly the size of the list S.
  However, the algebraic structure of the tensor forces its rank to be bounded 
  by the number of monomials of degree < k.
-/
def slice_rank_capacity_bound (L : Finset F) (k : ℕ) : Prop :=
    ∃ S_limit : ℕ, 
      -- FLAWED: The Slice Rank method requires the tensor to be strictly diagonal
      -- (zero everywhere off the diagonal).
      -- If P and Q are distinct polynomials that both agree with r(x) on \alpha |L| points,
      -- they MUST agree with each other on the intersection of their agreement sets.
      -- If \alpha > R, the intersection is massive. Therefore, P(x) - Q(x) = 0 on 
      -- a massive number of points.
      -- The tensor evaluates to the size of this intersection.
      -- Over a finite field of characteristic 2, the size of the intersection 
      -- is highly likely to be non-zero (or non-zero modulo 2).
      -- Because the off-diagonal entries T(P, Q) are non-zero, the tensor is NOT diagonal.
      -- The Slice Rank lemma collapses. You cannot bound the size of S by the rank 
      -- of a non-diagonal tensor.
      S_limit ≤ (Fintype.card F) ^ k

end ArkLib.CodingTheory.Research
