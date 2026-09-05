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

The [same exhaustive search in the production prime](astra_mca_paircover_production-2026-09-04.md)
also finds no degree-six mu16 seed. Separately, the
[four-coset obstruction](astra_mca_paircover_four_cosets-2026-09-04.md)
rules out all partitions assigning three whole quarter-domain cosets to
the three pair regions, however the fourth coset is split. Its minimum
syzygy product degree is exactly n/2 in every admissible characteristic.
This includes a recursively balanced production partition, but does not
cover arbitrary partitions.

## Positive control on different evaluation domains

The polynomial hypotheses can hold on other domains. This supplies a check
of the conversion without assuming a seed exists on the production subgroup.
Let h be even and at least six, and suppose the field contains a primitive
hth root of unity and has at least `3h` elements. Choose distinct nonzero hth powers
`tA,tB,tC`. Set

```text
n=3h-2,    k=n/2,
f_A=0,    f_B=X^h-tA,
f_C=alpha*(X^h-tB),    alpha=(tA-tC)/(tB-tC).
```

Here alpha is neither zero nor one, and
`f_B-f_C=(1-alpha)*(X^h-tC)`. Take h-1 points from each of the tA and tB
fibres and all h points from the tC fibre. These are disjoint nonzero sets;
exactly two codewords agree at each point, with region sizes h-1,h-1,h.
Their degrees are h, and `h<=k-2` follows from h>=6. Also
`s=2h-1` and `s-1>=k`. Thus every hypothesis of the conversion holds and
it gives n+1 genuine bad scalars on this domain.

Run `python3 scripts/probes/astra_mca_paircover_conversion.py`. It checks
the prime 2013265921 by trial division and uses h=6,12,24,48, giving
n=16,34,70,142. Each cell checks that 1,2^h,3^h are distinct and the field
is larger than n^4. The resulting 17,35,71,143 distinct scalars all pass
support agreement and independent Vandermonde dual-parity checks of the
no-joint clause: **266 certificates in total**.

The probe explicitly checks that these domains are not multiplicative
cosets of mu_n. They do not settle the production dyadic-domain problem.
This positive control is not a novelty claim about arbitrary-domain
Reed--Solomon counterexamples, and neither it nor the general conversion
has been formalized in Lean.
