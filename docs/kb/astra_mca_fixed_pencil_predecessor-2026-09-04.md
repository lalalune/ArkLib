# A fixed-pencil obstruction at the predecessor radius

This is an algebraic obstruction to a specified counterexample architecture,
not a universal MCA bound or a proof of the prize's lower endpoint. It applies
over any field, on any set of distinct evaluation points. The arguments below
have an independent mathematical review; they are not Lean-formalized.

For an integer `h>=1`, let `n=6h+4`, `k=3h+2`, and put

```text
d=k-1=3h+1,
c0=4h+2,
S=4h+4.
```

Here c0 is the joint-core size in the successful boundary construction. The
predecessor radius has agreement S and error count `n-S=2h`.

The event semantics are those of `mcaEvent` and `pairJointAgreesOn` in
[Errors.lean](../../ArkLib/Data/CodingTheory/ProximityGap/Errors.lean): the
decoded support itself must admit no joint codeword explanation. All event
counts below concern events whose decoding codeword comes from one of the
specified pencils.

**A full cover by at most five fixed polynomial pencils, each with joint core
at least c0, cannot yield more than n MCA-bad scalars at agreement S.**
Six pencils with cores exactly c0 are the first case left by the slot count.
They require genuine rational rank two, substantial interpolation-row
dependencies, and almost perfect pairing of their residual directions.

## Determinants force rational collinearity

Let the received pair be `(u0,u1)` on a domain Omega of cardinality n. A fixed
local pair is `Pi=(fi,gi)`, with both polynomial degrees at most d; its pencil
decodes by `fi+gamma*gi`. Its exact joint core is

```text
Ai={x in Omega : fi(x)=u0(x) and gi(x)=u1(x)}.
```

For any three local pairs define

```text
Delta_ijk=(fi-fk)*(gj-gk)-(fj-fk)*(gi-gk).
```

Its degree is at most 2d. At a node covered by exactly two of these three
cores, the corresponding two polynomial pairs coincide. Subtracting their
rows shows that `X-x` divides Delta. At a node covered by all three, both
difference rows are divisible by `X-x`, so `(X-x)^2` divides Delta. Distinct
nodes give coprime factors. Consequently Delta has a divisor of degree

```text
|Ai|+|Aj|+|Ak|-|Ai union Aj union Ak|.
```

This is the sum over coordinates of `max(t_x-1,0)`, where t_x is their coverage
multiplicity among these three cores. In particular,

```text
|Ai|+|Aj|+|Ak| > n+2d  ==>  Delta_ijk=0.
```

If every core has size at least `c0+1`, this holds because
`3(c0+1)-n=n+1>n-2=2d`. More strongly, suppose every core has size at least c0
and one distinguished core has size at least `c0+1`. Every triple containing
that distinguished pair then has forced degree at least `2d+1`. Their minors
vanish, so **all the local pairs are affine-collinear over K(X)**. This is a
rational-function statement; they need not lie on one affine line over K.

## Rational collinearity gives the n-direction ceiling on a full cover

Suppose the joint cores cover Omega. If all local pairs are identical, that
pair explains the received pair everywhere, and none of its decoded supports
can supply the no-joint-explanation clause of an MCA-bad event.

Otherwise, subtract one base pair and choose a nonzero difference. Dividing
its two polynomial components by their gcd gives a primitive direction
`(A,B)`, with `gcd(A,B)=1`. Rational collinearity and coprimality imply

```text
Pi=Pbase+Hi*(A,B),    Hi in K[X].
```

For completeness, if both A and B are nonzero and `(F,G)` is another
polynomial difference, the equation `FB=GA` and coprimality give `A|F` and
`B|G`, with the same polynomial quotient. If one component is zero, the other
primitive component is a unit and the conclusion is immediate.

At every coordinate x, choose a core owner j. The received pair equals
Pj(x), so its residual against any Pi is

```text
(Hj(x)-Hi(x))*(A(x),B(x)).
```

The primitive pair cannot vanish simultaneously at x. Thus every nonzero
residual at that coordinate has the same projective direction. A bad event
decoded by `fi+gamma*gi` must include a coordinate where the joint residual
against Pi is nonzero; otherwise Pi itself supplies a joint explanation on
the event's entire support. Cancellation at that coordinate forces

```text
A(x)+gamma*B(x)=0.
```

There is at most one such finite gamma per coordinate. Therefore these fixed
pencils supply at most n bad scalars in total. This argument covers all their
decoded supports, not only supports obtained by adding exactly one point.

The full-cover hypothesis matters. At an uncovered coordinate the received
pair need not lie on the rational line, and different local pairs may give
different residual directions there.

## The remaining equal-core case starts at six pencils

Suppose all exact joint cores have size c0. To reach agreement
`S=c0+2`, any one pencil must gain at least two coordinates outside its core.
Every outside residual is nonzero by exactness of the core, and cancels at
at most one finite gamma. Consequently a pencil supplies at most

```text
floor((n-c0)/2)=h+1
```

such scalars. Their union over r fixed pencils has cardinality at most
`r(h+1)`. For `r<=5` and `h>=1`, this is at most n. Combining this observation
with the preceding collinearity case proves the stated five-pencil obstruction.
Identical local pairs should be merged; repeating a pencil cannot improve the
union count.

For six pencils the maximum is `6(h+1)=n+2`. To exceed n, the sum of all
per-pencil shortfalls and all overlaps between their scalar sets must be at
most one. In particular, at least five pencils must attain their individual
maximum h+1: their `2h+2` outside coordinates must split into pairs with equal
finite cancellation direction, with different directions for different pairs.
This pairing requirement is additional to polynomial interpolation and rank.

## A necessary shape for four unequal cores

There is also a restriction without any lower bound on the four core sizes.
Write `ci=|Ai|`. A bad event explained by pencil i must include at least
`max(1,S-ci)` coordinates outside its exact core: the agreement threshold
requires `S-ci`, and the no-joint clause requires at least one even when
`ci>=S`. Hence its bad-scalar count is at most

```text
floor((n-ci)/max(1,S-ci)).
```

For `ci<=S-2` this is at most `h+1`; for `ci>=S-1` it is at most `2h+1`.
Thus four pencils with at most two cores of size at least `S-1` give at most
`2(2h+1)+2(h+1)=n` bad scalars.

Any four-pencil example exceeding n therefore needs at least three such large
cores. Those three pairs are rationally collinear by the determinant bound.
If all four cores were large, all four pairs would be rationally collinear,
and a full cover would again give the n ceiling. After merging identical
pairs, an over-budget full-cover example must consequently have **exactly
three cores of size at least S-1 and a fourth pair off their rational line**.
The determinant of that fourth pair with any two of the large pairs is
nonzero, so

```text
2(S-1)+c4 <= n+2d = 3(S-2),
c4 <= S-4.
```

At production, the three large cores must each have at least 715827883
points, while the fourth has at most 715827880. This is a necessary condition,
not an existence assertion or an exclusion of this unequal-core shape.

## Exact remaining interpolation and incidence requirements

Fix a full-cover core pattern. For one scalar coordinate of the local pairs,
subtract the first polynomial and impose the equalities among owners at each
node. A node of coverage multiplicity t_x contributes t_x-1 displayed linear
equations. With r pencils and uniform core size c, this gives a concrete
homogeneous matrix M with

```text
V=(r-1)k coefficient columns,
C=rc-n displayed rows.
```

The rows are independently chosen *within each node*. They need not remain
linearly independent after evaluation on bounded-degree polynomials. No
dimension count here is an existence or nonexistence proof.

Two linearly independent scalar solutions require exactly
`rank_K(M)<=V-2`. For six cores of size c0,

```text
V=15h+10,   C=18h+8,
C-rank_K(M)>=3h.
```

Even that rank condition is insufficient. The kernel must contain U,V whose
polynomial entries have a nonzero 2-by-2 minor: equivalently, its span over
K(X) must have rank at least two. Two solutions such as U and XU can be
linearly independent over K while remaining rationally dependent, in which
case the preceding n-direction ceiling still applies to a full cover.

At size c0 the determinant bound is sharp: `3c0-n=2d`. Thus any noncollinear
triple of local pairs must have its three cores cover all of Omega. If the
union missed even one point, its determinant would have forced degree at
least `2d+1` and would vanish. Consequently, at each coordinate, the set of
absent pencils must be affine-collinear over K(X).

For six cores, the total number of absent-pencil slots is
`6(n-c0)=2n+4`. Some coordinate therefore has at least three absent pencils,
forcing a globally collinear triple among the six distinct local pairs. A
six-point configuration with no collinear triple is excluded. A configuration
containing collinear triples is not thereby constructed or excluded.

At the production parameters these requirements read

```text
h=178956970,       n=1073741824,
k=536870912,       c0=715827882,
S=715827884,       predecessor errors=357913940,
six-pencil maximum=n+2=1073741826,
matrix columns=2684354560,
displayed rows=3221225468,
required independent row relations >=536870910.
```

The live six-pencil route would therefore need an explicit core pattern,
actual kernel vectors of rational rank two, and enough paired residual
directions to give at least n+1 distinct finite scalars. None is supplied by
these necessary conditions. Smaller or unequal cores, uncovered coordinates,
and event families not represented by these fixed pencils remain outside the
five-pencil theorem. In particular, it does not discharge the universal
predecessor-radius bound needed for a full endpoint equality.
