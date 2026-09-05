# Six square resultants at odd degree without a common cover

There is a basepoint-free degree-three pair B,C with **six** projectively
distinct saturated points whose locator map is birational. This refutes the
standalone implication that at least five square resultants force a common
degree-two cover, even when b is odd and all six square roots are pairwise
coprime. It does **not** refute the MCA bound or realize the prize hypotheses:
the six locators have a root union of size **33**, whereas the required
length at b=3 is `n=6b-2=16`.

The certificate uses characteristic 11 and the common splitting field
`K=F_(11^12)`. Its identities are already defined over F11. This is an exact
finite algebraic countermodel to a proposed intermediate implication, not a
production-field result or a Lean theorem. The
[degree-one and degree-two theorem](astra_mca_low_degree_saturation-2026-09-05.md)
remains intact.

## Exact data and resultant convention

All coefficients below are modulo 11. Homogenize every component of B,C
to the **fixed X-degree three** using a second variable Z:

```text
B=(3+8X+10X^2+X^3, 9+X, 6+9X+8X^2+X^3),
C=(8+3X+5X^2+6X^3, X^2+5X^3, 7+5X+5X^2+2X^3).
```

Thus, for example, the second component of B is `9Z^3+XZ^2`, not a
degree-one homogeneous section. Put `w=B cross C` and `Wi=ci dot w`.
Coefficient vectors in the following table are in ascending X-degree,
from the constant term through X^6; indices are **zero-based** throughout.

| i | ci | Coefficients of Wi |
|---|---|---|
| 0 | (1,0,0) | (8,8,0,6,4,3,6) |
| 1 | (1,5,5) | (3,5,8,8,2,2,7) |
| 2 | (1,7,10) | (5,0,6,2,10,5,7) |
| 3 | (1,9,4) | (7,6,4,7,7,8,7) |
| 4 | (0,1,0) | (5,8,7,10,4,6,4) |
| 5 | (0,0,1) | (5,9,10,8,0,7,5) |

In particular, `w=(W0,W4,W5)`. For each ci choose its first nonzero
coordinate p and, for j in increasing order with `j!=p`, use the annihilator
`ell_j(v)=v_j-(ci_j/ci_p)*v_p`. Set

```text
F=ell_j(T*C-S*B), G=ell_k(T*C-S*B),
Ri(S,T)=Res_X(F,G).
```

Use the six-by-six Sylvester matrix with three shifted descending-X
coefficient rows of F followed by three of G. Both X-degree bounds stay
three, including at special parameters. Direct polynomial determinants give
the following **homogeneous identities** `Ri=ai*Fi^2`:

| i | ai | Fi(S,T) |
|---|---|---|
| 0 | 9 | S^3+9S^2T+9ST^2+3T^3 |
| 1 | 10 | S^3+10S^2T+5ST^2+3T^3 |
| 2 | 2 | S^3+6S^2T+9T^3 |
| 3 | 6 | S^3+S^2T+2ST^2+6T^3 |
| 4 | 1 | S^3+8ST^2+3T^3 |
| 5 | 10 | S^3+7S^2T+2ST^2+9T^3 |

Every Wi has degree six and gcd one with its derivative; every Fi(S,1)
has degree three and gcd one with its derivative. Also `Fi(1,0)=1`, so
none of the resultant parameters is at infinity. All 15 pairwise gcds of
the Fi(S,1) are one: the six resultants contribute **18 distinct** finite
parameters after extending to K, with no scalar-overlap deficit.

## Geometric hypotheses and splitting

The exact coordinate gcd is `gcd(W0,W4,W5)=1`, so w has no geometric
finite basepoint. At X-infinity the homogeneous rows are

```text
B(infinity)=(1,0,1), C(infinity)=(6,5,2),
w(infinity)=(6,4,5) != 0.
```

Hence B,C are independent at every geometric point and w is basepoint-free
of degree six. Each individual Wi also has nonzero leading coefficient,
excluding locator roots at X-infinity. The six ci are distinct normalized
projective representatives and span three dimensions because they include
the three coordinate points.

The checker computes the complete irreducible-factor degree multisets by
Frobenius gcds, rather than inferring splitting from sampled field points:

| i | Factor degrees of Wi over F11 | Factor degrees of Fi(S,1) over F11 |
|---|---|---|
| 0 | 1,1,4 | 1,2 |
| 1 | 6 | 3 |
| 2 | 6 | 3 |
| 3 | 2,4 | 1,2 |
| 4 | 1,1,2,2 | 1,2 |
| 5 | 1,1,4 | 1,2 |

Their least common multiple is 12, so F_(11^12) is the smallest common
finite splitting field for these polynomials. The checker additionally
verifies `X^(11^12)=X mod Wi` and the corresponding identity modulo each
Fi(S,1). Squarefreeness gives six distinct geometric locator roots and
three distinct finite scalar roots per point. By the exact multiplicity
argument in the [resultant note](astra_mca_six_locator_resultants-2026-09-04.md),
each scalar root has exactly two slots. Thus all six ci are saturated over K;
they are not asserted to be saturated over F11 itself.

## Birationality excludes a common double cover

Take the six products in the order

```text
w0^2, w0*w1, w0*w2, w1^2, w1*w2, w2^2.
```

Their coefficient rows in degrees zero through five form the matrix

```text
 9  7  7  3  3  3
 7  5  2  3  8  2
 9 10  9  2  3  5
 8  1  9  3  2  7
 6  4  6  7  2  2
 2  4  2  0  4 10
```

Its determinant is **7 modulo 11**. The six quadratic products are
therefore linearly independent even after field extension, so the image of
`phi=[w]:P1 -> P2` lies on no conic.

The independent degree-three syzygies B,C give the balanced kernel

```text
ker(O^3 -> O(6), w)=O(-3) plus O(-3).
```

The [balanced-bundle argument](astra_mca_six_locator_birationality-2026-09-04.md)
therefore forces the degree nu of the map to the normalization of the image
to divide three. This includes any inseparable contribution. If nu were
three, the image would have degree `6/3=2`, contradicting the nonconic minor.
Consequently `nu=1`: phi is birational onto a plane sextic. In particular it
cannot factor through a common degree-two cover.

## Why this is not a six-pencil MCA counterexample

The only nonconstant pairwise locator gcds, normalized to be monic, are

```text
gcd(W0,W4)=X+8, gcd(W0,W5)=X+9, gcd(W4,W5)=X+10.
```

All other pairwise gcds are one. These three common roots are distinct,
and the six-locator least common multiple has degree **33**. Since all
locators are squarefree and split over K, their roots cannot fit on a
common 16-point domain. Equivalently they cannot all divide any squarefree
domain polynomial of degree `6b-2=16`, irrespective of a roots-of-unity
condition.

There is also the collinearity relation `c1-2*c2+c3=0`, but
`gcd(W1,W2,W3)=1`. In the actual equal-core incidence setting, the
[complete-line-flat identity](astra_mca_six_locator_consistency-2026-09-04.md)
for such a triple has `|E|=2t-2`, where t is the triple common-absence size.
Here t would be zero, giving the impossible value `|E|=-2`. The abstract
square-resultant data do not satisfy that realization condition either.

The implication using square resultants alone is therefore false at odd
b=3, even with six saturated points and disjoint scalar sets. The stronger
question imposing the actual common domain, incidence, and polynomial-pair
realization conditions remains open; nothing here resolves the production
degree `b=178956971` or the prize bound.

## Reproduction

Run from the repository root:

```sh
python3 scripts/probes/astra_mca_six_square_countermodel_check.py
```

It returns `PASS_SIX_SQUARE_B3_COUNTERMODEL` after computing all six
Sylvester determinants directly as polynomials in S,T, the geometric gcd
and infinity checks, square identities, factor-degree and splitting checks,
the nonconic minor, scalar and locator pairwise gcds, the degree-33 locator
LCM, and the collinear-triple obstruction. It uses only the Python standard
library and embedded exact data; no search interpolation or temporary
search output is needed. Discovery provenance was the degree-three
symmetric search's step 1988; the preserved checker independently
recomputes the certificate from B,C and the six points.
