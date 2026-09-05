# Low-degree rigidity of the square-resultant condition

The [resultant equations](astra_mca_six_locator_resultants-2026-09-04.md)
have a stronger consequence in degrees one and two. If `b=1`, no locator
can be saturated. If `b=2`, four projectively distinct saturated locators
force a global degree-two covering of a conic. The bound of three without
such a covering is sharp.

These are ordinary algebraic proofs, independently reviewed, with bounded
exact checks. They do not settle the production degree `b=178956971`.

## Hypotheses and the low-degree theorem

Let B,C be rows of three homogeneous binary forms of degree b over a field K.
Assume they are independent at every geometric point of the parameter line.
Then `w=B cross C` is basepoint-free of degree `2b`. A configuration point
`ci` is a nonzero constant row, taken up to scalar, and its locator is
`Wi=ci dot w`. Require each locator under consideration to have `2b` distinct
geometric roots. In the application they split on the domain and have no
root at X-infinity.

For fixed `[S:T]`, put `V_(S,T)=T*C-S*B`. It never vanishes at a geometric
X-point. A slot is a root x of Wi, together with the unique parameter for
which `V_(S,T)(x)` is proportional to ci. The resultant proof identifies its
multiplicity at a parameter with the number of these slots. Call ci
**saturated** when its `2b` slots give b distinct finite K-rational parameters, each
with exactly two slots. Equivalently its resultant is a nonzero constant
times `Fi^2`, where Fi is a split squarefree degree-b form and `Fi(1,0)!=0`.

The requirement that the ci be **projectively distinct** is essential:
different scalar representatives are the same configuration point.

The theorem is:

1. For `b=1`, there are no saturated points.
2. For `b=2`, either there are at most three projectively distinct saturated
   points, or the locator map `phi=[w]` factors over K as
   `P1 --rho--> P1 --Veronese--> P2`, up to a constant target-coordinate
   change, where rho has degree two.

In the second alternative, a squarefree locator also forces rho to be
separable. In particular, five saturated locators force a common double
cover when `b=2`; the theorem makes no such assertion for higher b.

## Degree one and the nonsingular matrix-pencil case

For `b=1`, every map `x -> V_(S,T)(x)` is a basepoint-free degree-one map
to the plane. It is an isomorphism onto a line. Two different x-points
cannot produce the same ci at the same parameter, so every resultant root
has multiplicity one.

For `b=2`, write

```text
V_(S,T)(X,Z)=M(S,T)*(Z^2,XZ,X^2)^T,
Delta(S,T)=det M(S,T).
```

The entries of the three-by-three matrix M are linear in S,T, so Delta is
a homogeneous cubic, possibly zero. If `Delta(S,T)!=0`, the corresponding
map is a projective transform of the Veronese embedding. It has no repeated
preimage of any ci. Thus every double-slot parameter must be a zero of Delta.

Suppose Delta is nonzero. There are at most three such parameters. At each,
M has rank exactly two: rank at most one would make all components of V
proportional to a single quadratic form, which has a geometric root and
would violate the nonvanishing of V. The image is therefore a line L_(S,T).

Different exceptional parameters give different lines. Otherwise one
constant linear form would annihilate V at two distinct parameters, hence
both B and C identically. Their cross product would then be a fixed vector
times a positive-degree form and would have a basepoint.

A saturated ci must lie on two of these different lines, since it needs
two distinct double-slot parameters. There are at most three pairwise line
intersections. This proves the bound of three when Delta is nonzero.

## An identically singular pencil forces the double cover

Suppose `Delta=0`. The matrix M has rank exactly two at every parameter by
the same nonvanishing argument. Its moving image line has a primitive
equation `ell(S,T)`. A nonzero row of `adj(M)`, with its homogeneous common
factor removed, gives ell with degree `e<=2`.

We use the elementary consequence of the balanced kernel calculation:

```text
ker(O^3 -> O(2b), w)=O(-b) plus O(-b).
```

Indeed B,C generate this kernel in every fiber because their cross product
is w. For positive b the kernel has no constant global section, so the
three coordinates of w are linearly independent. The standard vanishing
`H^0(P1,O(-b))=0` is included in
[Stacks Project, Lemma 30.8.1](https://stacks.math.columbia.edu/tag/01XS).

The dual image of ell cannot be a point: that would be one fixed line
containing every B(x),C(x). Suppose instead that the dual image is a line,
so all image lines pass through a point q. Since w spans three dimensions,
choose x0 for which q is not on the line spanned by B(x0),C(x0). The map

```text
[S:T] -> [T*C(x0)-S*B(x0)]
```

is an isomorphism onto that line. Projection from q identifies it with the
pencil of image lines. Consequently ell has degree one. This argument
also excludes an inseparable degree-two parametrization of a dual line.

For `e=1`, a constant coordinate change puts `ell=(S,T,0)`. Comparing
coefficients in `ell dot (T*C-S*B)=0` gives

```text
B=(0,H,B2),       C=(H,0,C2).
```

The cross product has the common quadratic factor H. If H is nonzero it
has a geometric root; if H is zero B,C are dependent. Both contradict the
hypotheses. This excludes the dual-line case.

Therefore e is two and the three coordinates of ell span all binary
quadratics. A constant coordinate change over K puts them in the form
`ell=(S^2,ST,T^2)`. No reparametrization or square-root choice is needed.
Comparing the four cubic coefficients now gives

```text
B=(0,H0,H1),       C=(H0,H1,0),
w=(-H1^2,H0*H1,-H0^2).
```

Here H0,H1 are homogeneous quadratics with no common geometric root,
because B,C remain independent. Thus `rho=[H0:H1]` has degree two and the
displayed expression for w is a Veronese parametrization after rho.

All coordinate changes and common-factor removals can be made over K.
If characteristic two made rho inseparable, every pulled-back point
divisor would have even multiplicity. This contradicts a squarefree Wi.
Hence the covering in the presence of such a locator is separable.

## Sharp degree-two controls

Over F101 put

```text
a=(X-1)(X-2), b0=(X-3)(X-4), c0=(X-5)(X-6),
B=(a,b0,c0),       C=(a,2*b0,3*c0).
```

Their cross product is `(b0*c0,-2*a*c0,a*b0)`, basepoint-free also at
infinity. The three coordinate points have squarefree locators and
resultants proportional respectively to

```text
((S-2T)(S-3T))^2,
((S-T)(S-3T))^2,
((S-T)(S-2T))^2.
```

The map `[a:b0:c0]` is a conic embedding: its coefficient determinant is
32. The displayed cross-product map is its composition with a quadratic
Cremona transformation, which is birational on this conic. Thus the
locator map is birational, giving exactly the sharp three-point control
for the theorem. The theorem rules out any fourth saturated point here.

For the covering alternative, take `B=(1,X^2,0)`, `C=(0,1,X^2)`.
Then `w=(X^4,-X^2,1)` factors through X^2. For distinct nonzero r,s, the
point `ci=(rs,-r-s,1)` has

```text
Wi=(r*X^2+1)(s*X^2+1),
Ri proportional to ((S-rT)(S-sT))^2.
```

The probe chooses five such points with all four locator roots in F101,
and verifies that they span three dimensions.

## One square at degree three does not force a cover

This control concerns one locator, not five. Over F11 take

```text
B=(1,X,6+3X^2-X^3),
C=(0,X+X^3,5+4X+2X^2+5X^3),       ci=(1,0,0).
```

Its locator and resultant are exactly

```text
Wi=X*(X-1)*(X+1)*(X-2)*(X+2)*(X-3),
Ri(S,T)=6*((S-2T)*(S-5T)*(S-10T))^2
```

for the probe's Sylvester convention. The six slots pair as
`{1,-1}`, `{2,-2}`, `{0,3}`. All three parameters are finite.
The rows are independent in every geometric fiber: at finite X, C is
nonzero and its first coordinate is zero whereas B's is one. Specifically
`C1=X(X^2+1)`, `C2(0)=5`, and `C2 mod (X^2+1)=3-X`, which has no common
root with `X^2+1` over F11 or its algebraic closure. At infinity the rows
are `(0,0,-1)` and `(0,1,5)`.

For the six quadratic coordinate products of w, the coefficient rows of
degrees zero through five have determinant 3 modulo 11. Thus its image is
not a conic; the probe independently checks this six-by-six minor.
The [balanced-bundle degree divisibility](astra_mca_six_locator_birationality-2026-09-04.md)
forces the normalization-cover degree to divide three; the only possible
nontrivial degree would be three, with conic image. Therefore this locator
map is birational. A single square resultant does not force a double cover
at b=3. The example establishes neither five squares nor a six-pencil
realization on the production domain.

## Reproduction and remaining scope

Run `python3 scripts/probes/astra_mca_low_degree_saturation_check.py`.
The checks use direct fixed-degree Sylvester determinants, independent
slot products, polynomial gcds, and exact coefficient-matrix ranks. They
include the sharp three-point example, a five-point covering example,
and the one-point degree-three control.

The subsequent [six-square degree-three countermodel](astra_mca_six_square_countermodel-2026-09-05.md)
shows that even six saturated locators at odd degree can have a birational
locator map. Its eighteen scalar parameters are distinct over F_(11^12),
but its locator union needs 33 domain points rather than the required 16.
Thus the degree-two rigidity theorem cannot extend by square-resultant
conditions alone. The remaining production question must use the actual
common-domain and incidence conditions; neither result supplies its bound.
