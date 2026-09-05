# Two polynomial generators and actual MCA cancellation directions

This note proves a conditional MCA construction and a two-point deletion
lemma that guarantees its balanced polynomial basis on the production
domain. It does **not** prove the required number of distinct cancellation
directions at production length. A separately checked length-16 example
has 18 actual MCA witnesses over the production prime.

The [compact evaluator](astra_mca_twogen_lift_eval-2026-09-04.md) now gives
explicit formulas for the production deletion and a partial count of
268435460 distinct finite witnesses. The full required count remains open.
The [anchor multiplicity filter](astra_mca_anchor_multiplicity-2026-09-04.md)
explains why a balanced basis alone does not guarantee enough directions.

## The support-level bridge

Let Omega contain n distinct field elements. Let the code consist of
polynomials of degree less than k. Suppose three local polynomial pairs
`(f_i,g_i)`, for `i=A,B,C`, agree with one received pair `(u0,u1)` on
cores `S_i` of size `s-1`, where `s-1>=k`. For every slot `(i,x)` with
`x` outside `S_i`, assume the residual vector

```text
R_i(x) = (u0(x)-f_i(x), u1(x)-g_i(x))
```

is nonzero. Let b be the number of distinct projective directions of these
vectors. If the projective line of the field has more than b points, a
constant invertible change of the two coordinates makes all residuals'
second coordinates nonzero: choose its second-coordinate linear
functional with kernel outside the b residual lines. Apply the same
change to the received pair and every local polynomial pair.

Each distinct residual direction then gives a distinct scalar
`gamma=-R_0/R_1`. Its local polynomial `f_i+gamma*g_i` agrees on
`S_i union {x}`, of size s. If another polynomial pair jointly explained
the received pair on that support, its two polynomials would equal
`f_i,g_i` by uniqueness on the at least k core points. The nonzero
residual at x contradicts this. Thus all b scalars satisfy the actual
[`mcaEvent` in Errors.lean](../../ArkLib/Data/CodingTheory/ProximityGap/Errors.lean)
definition, including its no-joint-explanation clause on the same support.

This proves a lower bound by specified witnesses, not an exhaustive count
of all MCA-bad scalars. An infinite field also permits the coordinate
change. For the constructions below, the finite sufficient condition
`q>n+1` covers all at most n+2 directions.

## A pair-region realization with two private points

Put

```text
n=6h+4,  k=3h+2,  s=4h+3,  D=k-1=3h+1,  h>=1.
```

Partition Omega into pair regions AB, AC, BC and a private-A region I of
sizes `2h,2h,2h+2,2`. Let A,B,C be the monic vanishing polynomials of the
three pair regions. Suppose two syzygies give local triples

```text
(0,F_1,G_1), (0,F_2,G_2),
F_j=A*U_j,  G_j=B*V_j,  F_j-G_j=C*W_j,
max(deg F_j,deg G_j)<=D,
F_1*G_2-F_2*G_1 = lambda*A*B*C,  lambda != 0 constant.
```

Such a pair is a balanced polynomial syzygy basis; the displayed
identities themselves suffice for this section. Each cofactor row is
nonzero at the relevant roots. Indeed, cancellation of A and B in the
last identity gives `U_1*V_2-U_2*V_1=lambda*C`. Using the syzygy also gives
the other two cofactor minors as nonzero constant multiples of A and B.

Take local pairs `(f_A,g_A)=(0,0)`, `(f_B,g_B)=(F_1,F_2)` and
`(f_C,g_C)=(G_1,G_2)`. On each pair region use its common local pair as
the received value, and use `(0,0)` on I. The cores are

```text
S_A=AB union AC union I,
S_B=AB union BC,
S_C=AC union BC.
```

Each has size `4h+2=s-1>=k`. On a pair region the missing local pair has
a nonzero residual, by the cofactor minors. At a private point x the
two missing residuals are nonzero and have different projective
directions: their determinant is `lambda*A(x)*B(x)*C(x)`, which is
nonzero outside the pair regions.

There are `|AB|+|AC|+|BC|+2|I|=n+2` slots. Consequently **at least n+1
distinct projective directions imply at least n+1 actual MCA-bad
scalars at agreement s**. Directions at different coordinates may
coincide. The determinant at a private point does not exclude such
cross-coordinate collisions. A constant change of basis preserves all
projective collisions.

The residual directions can be tested directly from the three cofactor
rows: on AB use the V row (equivalently W), on AC use U (equivalently W),
on BC use U (equivalently V), and on each private point use both U and V.
Nonzero factors A(x),B(x),C(x) do not change their projective directions.

## Why the two generator degrees must be exactly balanced

The same accounting applies to three cores of size `s-1`, with no holes,
possibly a common region of size t and private regions of total size U.
Let B_total be the total size of the pair regions. Counting points and
core memberships gives

```text
n=t+B_total+U,
3(s-1)=3t+2*B_total+U=2n-2,
t=U-2.
```

After dividing the common vanishing polynomial from the local
differences, their degree budget is `K=k-1-t`. At rate one half,

```text
B_total=n-t-U=2(k-1-t)=2K.
```

The two minimal product degrees of a column-reduced syzygy basis add
to B_total. Thus both primitive generators can fit only when both
degrees equal K. There is then no degree allowance for nonconstant
basis mixing. This is an accounting statement about this architecture,
not a bound on the unrestricted MCA event.

## Two-point deletion guarantees the balanced basis

Here is a way to produce the required basis without solving another
low-degree syzygy-existence problem.

Start with a full partition of a domain of even size n into root sets
of three pairwise coprime, monic polynomials A,B,C. Put `D=n/2`.
Assume its smallest nonzero syzygy product degree is D and
`deg A+deg B>D`, with both A and B nonconstant. Its two basis product
degrees are then D,D. To see existence directly, every locator has degree
at most D: otherwise the other two would give a relation of product
degree less than D. The three cofactor spaces at degree D have total
dimension `sum(D-deg A_i+1)=D+3`, and the polynomial identity imposes at
most D+1 equations. Thus there are two linearly independent relations
over the coefficient field. Every minimal-degree cofactor triple is
primitive, since a common nonconstant factor could be divided out to
lower the degree. Two primitive triples proportional over the rational
function field are constant multiples, so these two relations are also
independent over that field. Equivalently, choose two column-reduced basis
triples as above with degree D and

```text
F_1*G_2-F_2*G_1=lambda*A*B*C,  lambda != 0.
```

The usual degree identity can also be checked directly here. Two
independent minimal-degree syzygies have their vector cross product
proportional to the signed coefficient triple `(A,-B,-C)`; coprimality makes the proportionality factor
a polynomial, and `deg A+deg B+deg C=2D` makes it constant. It is
nonzero. Such a pair generates the polynomial syzygy module: the
Cramer coefficients have no poles, since A,B,C have no common root.
Their leading product vectors are independent by the same cross-product
identity, so every relation of product degree at most D is a constant
combination of the two.

There exist `xi` in the A root set and `eta` in the B root set with
different projective W-row directions. To prove this, first note that
the W row is nonzero at all these points, by the cofactor minors.
If every cross-pair had the same direction, every point in the union
of the A and B root sets would have one common W direction. A nonzero
constant combination W of the two W polynomials would then vanish at
`deg A+deg B` distinct points, although

```text
deg W <= D-deg C < deg A+deg B.
```

Hence W would be identically zero. The corresponding nonzero syzygy
would satisfy `F=G`, with F divisible by both A and B, contradicting
`deg A+deg B>D`. This proves existence of xi,eta with independent rows.

Make a constant change of the old basis so that column 1 kills W at eta
and column 2 kills W at xi. These columns are independent, because the
two W rows are independent. At eta, G_1 already vanishes since B does,
and `F_1-G_1=C*W_1` implies F_1 also vanishes. Similarly F_2 and G_2
both vanish at xi. Therefore the following are polynomial triples:

```text
new column 1: (0, F_1/(X-eta), G_1/(X-eta)),
new column 2: (0, F_2/(X-xi),  G_2/(X-xi)).
```

Their product degrees are D-1. Move xi from AB and eta from AC to
private A; the pair locators become

```text
A'=A/(X-xi),  B'=B/(X-eta),  C'=C.
```

Both new F polynomials are divisible by A', both new G polynomials by
B', and both differences by C. Moreover their determinant is exactly
`lambda*A'*B'*C`. Thus the preceding nonzero-residual and distinct
private-point arguments apply without additional assumptions.

There is no nonzero new syzygy of product degree D-2. Multiplying it
by `(X-xi)(X-eta)` would produce an old syzygy of product degree at most
D whose W cofactor vanishes at both xi and eta. It must be a constant
old-basis combination, and the independent W rows force it to be zero.
Thus both new minimal generator product degrees are exactly D-1.

At every coordinate x different from xi,eta, each new residual row is

```text
(old_R_1(x)/(x-eta), old_R_2(x)/(x-xi)).
```

In particular, the first-to-second ratio gains the factor
`(x-xi)/(x-eta)`. This varies with x and can break old collisions. It
does not by itself prove injectivity across coordinates. The deleted
points must be evaluated by polynomial division, not this formula with
a zero denominator.

## Application at the production length

The [three whole cosets plus an arbitrary residual split lemma](astra_mca_paircover_four_cosets-2026-09-04.md) gives an unconditional
source for the preceding deletion construction. Write `n=4m`, with
`m=1 mod 3`, and choose four distinct m-th powers alpha,beta,gamma,delta.
Set

```text
A=(X^m-alpha)*a, B=(X^m-beta)*b, C=(X^m-gamma)*c,
abc=X^m-delta,
deg a=deg b=(m-1)/3, deg c=(m+2)/3.
```

The cited lemma proves the smallest product degree is `2m=n/2`
for every such residual partition, in every field with these distinct
cosets. Also `deg A+deg B=(8m-2)/3>2m` for `m>1`.
Deleting a suitable A root and B root as above gives pair sizes

```text
(n-4)/3, (n-4)/3, (n+2)/3,
```

and two private-A points, exactly the target sizes `2h,2h,2h+2,2` for
`h=(n-4)/6`. The new generator product degrees are exactly `n/2-1`.

This applies to the unchanged production domain `mu_(2^30)` over the
repository's production prime, with `m=2^28`. The production field and
root are certified in
[`_PrizeShapePrimeP30.lean`](../../ArkLib/Data/CodingTheory/ProximityGap/Frontier/_PrizeShapePrimeP30.lean).
There is no remaining basis-existence assumption for this construction.
The unresolved step is obtaining **at least n+1 distinct residual
directions**. If established, the support-level bridge would exceed
`floor(P/2^128)=n` at agreement `(2n+1)/3`. It would still not determine
the largest safe radius requested by the grand challenge.

## Finite verification and literature scope

The separate probe
[`astra_mca_two_generator_probe.py`](../../scripts/probes/astra_mca_two_generator_probe.py)
uses n=16,k=8 and the production prime. An irregular partition, written
as exponents of its order-16 root, is

```text
AB=[0,1,4,9], AC=[2,6,11,15],
BC=[3,7,8,10,12,14], private A=[5,13].
```

Its two-dimensional degree-at-most-seven syzygy space gives 18 distinct
nonzero projective directions and 18 finite bad scalars at agreement 11.
An independent verification read the explicit polynomial receipt,
checked all supports and scalar agreements, and constructed 18
Vandermonde dual parity certificates on nine-point subsets: each
annihilates degrees zero through seven and has a nonzero received-pair
syndrome, ruling out joint explanation. This is a length-16 witness;
using the production prime does not make its length a production result.
It is not asserted to arise from the deletion construction above.

The [separate deletion checks](astra_mca_two_generator_probe-2026-09-04.md)
do instantiate the recursive full partition and two-point deletion at
n=16,64,256. For the first valid anchor pair in each cell they certify
18,66,258 distinct bad scalars, including every support agreement and
independent no-joint parity check. These finite successes do not prove
production collision control.

Brakensiek, Dhar and Gopi prove the field-size requirement
`q >= binomial(n-2,k-1)-1` for an MDS(3) code in
[Theorem 1.6 and Lemma 3.1 of their primary paper](https://arxiv.org/html/2212.11262v2#S3).
Their proof forces a failure with support sizes `2,k-1,k-1`.
Their balanced-support refinement, Lemma 3.3, introduces overlaps by
projection. Neither statement provides the disjoint full-cover pattern
of the earlier target, nor distinct cancellation directions for the
present construction. The exponential field-size obstruction therefore
does not settle this remaining collision problem.

All mathematical arguments in this note are independently reviewed
ordinary proofs and exact finite checks, not Lean formalizations.
