# Equal-core six-pencil constraints and one excluded incidence pattern

This note gives two independently reviewed algebraic results, over any field
and distinct evaluation nodes. Neither is Lean-formalized. The second excludes
one explicit six-pencil architecture, not every possible six-pencil example
and not the universal predecessor-radius problem.

Use the notation and event semantics of the
[fixed-pencil predecessor note](astra_mca_fixed_pencil_predecessor-2026-09-04.md):

```text
h>=1, n=6h+4, k=3h+2, d=k-1=3h+1,
c0=4h+2, S=c0+2=4h+4, b=h+1.
```

The six distinct polynomial pairs `Pi=(fi,gi)` have component degrees at most
d. Their exact joint cores Ai all have size c0 and cover the domain Omega.
Put `Di=Omega\Ai`. If all pairs are affine-collinear over K(X), the earlier
full-cover argument already bounds their MCA-bad scalars by n. Below assume
the whole configuration is not rationally collinear.

## Exact determinant divisors force complete line flats

For a noncollinear triple i,j,k, set

```text
Delta_ijk=(fi-fk)*(gj-gk)-(fj-fk)*(gi-gk).
```

The previous multiplicity argument forces its zero divisor to contain
`max(t_x-1,0)` copies of each `X-x`, where t_x is the number of these three
cores owning x. The three cores must cover Omega: otherwise the forced degree
is at least `3c0-(n-1)=2d+1`, contradicting nonzero Delta of degree at most 2d.
With full union, the forced divisor has degree exactly `3c0-n=2d`.

More explicitly, write `Li=product_{x in Ai}(X-x)` and
`V=product_{x in Omega}(X-x)`. For some nonzero scalar a in K,

```text
Delta_ijk = a * Li*Lj*Lk/V.
```

The quotient is a polynomial because the three cores cover Omega. No degree
remains for an extra zero. In particular, at a node with exactly one owner
among this noncollinear triple, Delta is nonzero.

Now let i,j,k be a collinear triple of distinct pairs. It cannot have exactly
one owner i at a node x. If it did, choose a configured pair Q off their line.
The noncollinear triple j,k,Q must cover Omega, so Q also owns x. Then
`Pi(x)=PQ(x)`, and the identically zero determinant of j,k,i gives
`Delta_jkQ(x)=0`. But Q is the only owner of x among j,k,Q, contradicting the
exact-divisor conclusion. Therefore, for every collinear triple,

```text
Di intersect Dj is a subset of Dk,
```

and likewise for its permutations.

At a node with at least two absent pairs, all absent pairs must already be
collinear: three noncollinear absent pairs would violate their full union.
The new inclusion says that every configured pair on that line is absent.
Thus the absent set is a **complete line flat** of the finite rational
configuration. Empty and singleton absent sets are also possible.

This resolves the proposed local-overlap mechanism in the opposite direction
from an immediate contradiction. Two absent collinear pencils cannot have a
third pencil on their line owning that coordinate. In fact, the residuals of
any two absent pairs at the same coordinate have distinct projective
directions: any owner lies off their line, and its triple determinant is
nonzero there. Almost-perfect pairing, if it exists, must relate different
coordinates. These facts alone do not rule it out.

## An explicit complete-quadrilateral pattern has at most twelve directions

Label the six pairs by the edges of a four-vertex complete graph:

```text
P12, P13, P14, P23, P24, P34.
```

Assume the domain partitions into a common set E of size 2h and four regions
`R1,R2,R3,R4`, each of size b. Every pair owns E. On Ri, exactly the three
pairs whose edge contains i are absent; the complementary triangle of three
pairs owns the region. Thus every pair is absent on two regions, giving
`|Di|=2b` and `|Ai|=c0`.

Each absent star is a collinear triple by the first result. Assume, as above,
that the six pairs are distinct and not all rationally collinear. Under these
assumptions this precise pattern supplies **at most twelve projective
residual directions**, and hence at most twelve finite MCA-bad scalars through
these pencils.

To prove it, subtract P12 from every pair and from the received pair. The
common locator `H=product_{x in E}(X-x)` divides every component difference.
Divide those polynomial pairs by H, and on `Omega\E` also replace the received
pair by `(u-P12)/H`. The nodes in E have zero residual against every pencil
and can be ignored. The component degrees of the new polynomial pairs are at most
`d-2h=b`, and their residual directions on each Ri are unchanged, since H
does not vanish there. Denote the resulting pairs again by Pij, with P12=0.
Let Wi be the monic degree-b locator of Ri.

On R3 the owners are P12,P14,P24; on R4 they are P12,P13,P23. The degree bound
therefore gives constant vectors a,bvec,c,dvec in K^2 with

```text
P14=a*W3,     P24=bvec*W3,
P13=c*W4,     P23=dvec*W4.
```

The collinear stars at vertices 1 and 2 imply `c` is proportional to a and
`dvec` is proportional to bvec. The vectors a,bvec are independent: otherwise
these four pairs and P12 lie on the same line, and the star through the
distinct pairs P13,P23 forces P34 onto it too, a contradiction.

An invertible constant change of the two residual coordinates thus puts them
in the form

```text
P14=(W3,0),          P24=(0,W3),
P13=(alpha*W4,0),    P23=(0,beta*W4),
```

where alpha,beta are nonzero. This coordinate change preserves the number of
projective directions; the original finite-scalar count is bounded by that
number even if the change moves a direction to infinity.

Writing `P34=(F,G)`, the remaining two collinear stars give

```text
F+G=W3,
F/alpha+G/beta=W4.
```

Here `alpha!=beta`, since equality would force W3 to be a scalar multiple of
W4, impossible for their disjoint nonempty root sets. Therefore F and G are
constant linear combinations of W3 and W4. All six pairs have that form.

On R2, the owners P13,P14 coincide, so `W3=alpha*W4`. On R1, the owners
P23,P24 coincide, so `W3=beta*W4`. On R3, W3 vanishes and W4 does not; on R4,
W4 vanishes and W3 does not. Consequently, on each region all six pair values
and the received owner value are a common nonzero scalar times constant
vectors. Each of its three absent pairs has one fixed nonzero residual
direction throughout that region. Four regions give at most `4*3=12`
directions; E contributes no nonzero residual.

In particular each pencil has at most two cancellation directions. The
six-pencil over-budget slot count requires at least five pencils to attain
b distinct scalars, which this pattern cannot do when `b>2`. For `h>=2`,
`n>=16>12`, so the direct direction bound already excludes it. The case
`h=1,n=10` is not excluded by the bound twelve.

At production, `h=178956970`, `b=178956971`, and `n=1073741824`. The result
rules out this exact four-region/common-core architecture regardless of
whether its required locator polynomial pencil can exist on the production
subgroup. Other complete-line-flat incidence patterns, unequal region sizes,
or configurations with empty or singleton absent sets have not been
classified here. The general six-pencil predecessor question remains open.
