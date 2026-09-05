# A balanced pair-cover target that would exceed the MCA budget

This is a proved conditional construction with an unresolved polynomial
existence requirement. It constructs actual MCA witnesses on the unchanged
evaluation domain if the stated three codewords exist. It is not a proof
that they exist, an unsafe-radius certificate, or a prize solution.

## Exact sufficient input

Let Omega be a set of n distinct nonzero elements of a field K, with
`n=1 mod 3` and `|K|>=n+2` (an infinite K also suffices). Put

```text
s=(2n+1)/3,    a=(n-1)/3,    c=(n+2)/3.
```

Let the Reed--Solomon code consist of polynomials of degree less than k,
where `k>=2` and `s-1>=k`. Suppose three polynomials

```text
f_A=0,    f_B,    f_C,    degree(f_i)<=k-2
```

have exactly two equal values at every point of Omega. In particular,
there is no point where all three values coincide. Suppose their three
pair-agreement regions partition Omega with cardinalities

```text
|AB|=a,    |AC|=a,    |BC|=c.
```

Then there is a received pair `(u0,u1)` with at least **n+1 distinct
MCA-bad scalars at agreement s**, including the no-joint-explanation clause.

These polynomial and domain conditions are substantive. No arbitrary
numeric region profile or unspecified syzygy degree can substitute for them.

## Explicit construction and no-joint proof

Initially let r(x) be the repeated value at x and set
`u0(x)=r(x), u1(x)=x*r(x)`. The cores on which each local pair
`(f_i,X*f_i)` explains `(u0,u1)` have sizes `s-1,s,s`, respectively.
Both members of each local pair have degree less than k.

At each x, the odd codeword f_i differs from r(x). The scalar `-1/x`
makes the codeword `(1-X/x)*f_i` explain the received combination on
that core plus x. The residual at x is nonzero. Any joint codeword pair
explaining the same support must equal `(f_i,X*f_i)` by uniqueness on
the at least k core points, which contradicts that residual.

To obtain one more scalar, choose `xi` in BC. Write
`v=f_B(xi)=f_C(xi)`, which is nonzero since `f_A=0` and exactly two values
coincide. Remove xi from the B and C cores. All three cores now have
size s-1 and avoid xi; their local codeword explanations remain valid.

Choose distinct `lambda,mu` outside the n-element set
`{-1/x : x in Omega}`. Replace the received pair only at xi by

```text
b = v*(1+mu*xi)/(mu-lambda),
a = -lambda*b,
(u0(xi),u1(xi))=(a,b).
```

The residual against A is nonzero because b is nonzero, and its unique
cancellation scalar is lambda. The residual against B (equivalently C)
has nonzero second component

```text
b-xi*v = v*(1+lambda*xi)/(mu-lambda),
```

and cancels at mu. Each supplies an MCA witness on its shortened core
plus xi, of size s, with the same polynomial-uniqueness proof of the
no-joint clause.

All n-1 old witnesses at other coordinates survive: their shortened
cores avoid the changed point and still have size s-1. Thus the bad
scalars include n-1 distinct values `-1/x` and the two new values
lambda and mu. No evaluation point or code parameter was changed.

The construction and preservation of the no-joint clause received an
independent mathematical review. They are not Lean formalized.

## Production relevance and the first finite check

For the repository's `n=2^30`, `k=2^29` prime-field instance,
`floor(P/2^128)=n`; see
[`_PrizeShapePrimeP30.lean`](../../ArkLib/Data/CodingTheory/ProximityGap/Frontier/_PrizeShapePrimeP30.lean).
Consequently an actual triple satisfying these hypotheses would give an
unsafe-radius certificate at agreement `(2n+1)/3`, exceeding the exact
numerator budget. Even that certificate would not alone determine the
largest safe radius required by the grand challenge.

The new support geometry differs from the preceding
[three-core construction](astra_mca_lift_three_core-2026-09-04.md): it
has no triple or private region and no coordinates where all three
codewords coincide. That is why its one-coordinate modification can
cross n instead of stopping below n.

The first bounded existence check uses `n=16,k=8` over F65537. For
partitions of the smooth domain into root sets of sizes 5,5,6, let their
monic vanishing polynomials be A,B,C. The needed degree-at-most-six
relation has the form

```text
A*(a1*X+a0) + B*(b1*X+b0) + lambda*C = 0.
```

Every candidate must also satisfy the exactly-two-agree condition on all
16 domain points. A small-field result in either direction must not be
extrapolated to the production field or domain. Power-map lifting alone
would also preserve the unequal proportions 5:5:6, so it does not give
the balanced production cardinalities automatically.

The [completed exhaustive check](astra_mca_paircover_search-2026-09-04.md)
finds no such syzygy over F65537 in all 378378 normalized partitions.
Independent Gaussian elimination gives rank five for every original matrix.
Reduction of nonzero minors also excludes this exact mu16 construction in
characteristic zero. Neither result excludes the target triple for the
production field and domain; that existence question remains open.
