# Outside factors vary in actual production lists

The [multiplicity argument](astra_mca_split_root_rigidity-2026-09-05.md)
bounds each fibre with a fixed outside-domain factor by three. It cannot
be extended by asserting that all list candidates have the same such
factor: an explicit production word below has two candidates with
nonconstant, coprime outside factors, each of degree 268435455.

A separate complete small-domain computation handles the first extra-root
case. At order 16 over the production prime, every received polynomial of
degree 12 has at most one degree-less-than-eight candidate with 11 punctured
agreements, including candidates whose extra root is outside the domain.
The same statement fails over F17 and F97.

These are a written production construction with exact arithmetic checks
and a reproducible finite census. Neither is Lean-formalized or independently
reviewed. The production example supplies only two candidates and does not
exceed any proposed prize budget. A bound on the number of distinct outside
factors in an arbitrary production list remains open.

## A production pair with coprime outside factors

Use the [certified prime and generator](../../ArkLib/Data/CodingTheory/ProximityGap/Frontier/_PrizeShapePrimeP30.lean)
and the existing single-hole parameters:

```text
n=2^30=1073741824,
P=365375409332725729550921208179070755120141565953,
g=303645430271030343624574566109998498685964493478,
k=n/2=536870912,
ell=n/4=268435456,
b=(n+2)/6=178956971,
A=k+b=715827883.
```

Work in F_P and omit a=1. Let C_j be the coset of mu_ell containing g^j,
for j=0,1,2,3. Set

```text
r=g,        s=g^2,
u=r^ell,    w=s^ell,     v=g^(3ell),
alpha=v-w,  beta=s-r,    gamma=v-u.
```

All three constants alpha, beta and gamma are nonzero. Define the monic
geometric-sum polynomials

```text
G_t(X)=(X^ell-t^ell)/(X-t)
      =sum_(j=0)^(ell-1) t^(ell-1-j)*X^j,

F_0=G_r*(X-s),           F_1=X^ell-v,
Q_0=(alpha+beta*G_s)/(alpha*gamma),
Q_1=(alpha+beta*G_r)/(alpha*gamma).
```

Division in the formulas for Q_0,Q_1 is by a nonzero field constant.
The root sets of F_0 and F_1 are respectively

```text
U=(C_1\{r}) union {s},   W=C_3,
```

two disjoint sets of size ell. The identity

```text
F_0*Q_0-F_1*Q_1=1                                       (1)
```

holds as a polynomial identity. To check it, multiply by alpha*gamma and
use (X-t)G_t=X^ell-t^ell:

```text
F_0*(alpha+beta*G_s)-F_1*(alpha+beta*G_r)
 = alpha*(G_r*(X-s)-(X^ell-v))
   + beta*G_r*((X-s)*G_s-(X^ell-v))
 = alpha*(gamma-beta*G_r)+beta*G_r*alpha
 = alpha*gamma.
```

In particular Q_0 and Q_1 have no common root, even over an algebraic
closure. Each has degree ell-1 and leading coefficient
lambda=beta/(alpha*gamma), which is nonzero.

### Checking all possible domain roots with eight evaluations

Neither Q_0 nor Q_1 has any root in Omega=mu_n at the production prime.
This does not require expanding a polynomial of degree ell-1 or scanning
the domain. For t=s or t=r, put N_t=alpha+beta*G_t. If x lies in the coset
with x^ell=zeta and N_t(x)=0, then

```text
(x-t)*N_t(x)=alpha*(x-t)+beta*(zeta-t^ell)=0.
```

Consequently that coset has only one possible root,

```text
x=t-beta*(zeta-t^ell)/alpha.                            (2)
```

There are only four choices zeta=g^(j*ell). The checker computes all four
points for each t and verifies both coset membership and N_t(x)=0. When
x=t it evaluates N_t(t)=alpha+beta*ell*t^(ell-1), instead of dividing by
x-t. For each of Q_0 and Q_1, the point t passes coset membership but fails
the polynomial equation, and the other three possible points fail coset
membership. Thus all eight possibilities are excluded exactly.

The complete monic outside factors are therefore

```text
E_0=Q_0/lambda=G_s+alpha/beta,
E_1=Q_1/lambda=G_r+alpha/beta.                            (3)
```

They are nonconstant, distinct and coprime. No irreducibility or splitting
over F_P is assumed; having no root in Omega is precisely the condition
needed to remove the domain-root part of the error polynomial.

### The received word and its two actual candidates

Choose the common locator explicitly as

```text
R=((X^ell-1)/(X-1))*product_(j=1)^(b+1) (X-g^(4j+2)).
```

It has ell+b distinct roots, avoids 1, and is disjoint from U and W.
Indeed, its first factor has roots C_0\{1}; the other roots lie in C_2
and exclude s. The inequality b+1<=ell-1 makes this choice possible. Set

```text
V=R*F_0*Q_0,             f_0=0, f_1=R.
```

Equation (1) gives V-f_1=R*F_1*Q_1. Since Q_0,Q_1 have no domain roots,
both candidates have exactly A=(ell+b)+ell punctured agreements. Their
degrees and values at the omitted point satisfy

```text
deg f_1=447392427<k,
deg V=984263338<=n-2,
f_0(1)=0,                f_1(1)=R(1)!=0.
```

The last nonvanishing follows from 1 not being a root of R. Thus V itself
is the canonical punctured interpolation polynomial of this received word.
The normalized errors have the outside factors (3), so the two candidates
belong to different outside-factor fibres.

The [Lean-verified single-hole equivalence](astra_mca_single_hole_reduction-2026-09-05.md)
turns these two list candidates into two bad scalars at radius
357913940/n, once the present written construction is instantiated. Its
same-support no-joint requirement follows from that equivalence; it is not
replaced by a weaker witness condition. This is only two scalars, far below
the n+1 distinct values needed to violate the necessary production budget.
The full list of this word is not classified here.

## A complete census for one extra root at order 16

This is a separate finite result. Put n=16, k=8, A=11, degree V=12, and
omit 1 from mu_16. Normalize V to be monic; scaling by its leading
coefficient preserves the list count. Any list candidate has

```text
V-f=(X-theta)*H_S,
S subset mu_16\{1}, |S|=11,
H_S the monic locator of S.
```

The extra root theta may be anywhere in F_p, including in S, at the omitted
point, at another domain node, or outside the domain. A linear residual
factor necessarily splits over F_p. Thus no candidate is excluded by this
description.

Write h_j for the coefficients of H_S and let z be the coefficient of
X^11 in V. Then theta=h_10-z, and the coefficients of X^8,X^9,X^10 in V are

```text
a_S+z*b_S,
b_S=(h_8,h_9,h_10),
a_S=(h_7-h_10*h_8, h_8-h_10*h_9, h_9-h_10^2).           (4)
```

Each of the 1365 possible sets S consequently gives an affine line
`(a_S+z*b_S,z)` in the four-dimensional space of received top coefficients.
Lower received coefficients translate candidates by a codeword and do not
change their number.

Two distinct such lines cannot coincide: coincidence would make the two
locators agree in coefficients X^7 through X^11, so their difference would
have degree at most six. Their supports intersect in at least seven points,
forcing the locators to be equal. Every line pair can therefore be handled
by elementary linear equations: it is parallel and disjoint, meets at one
point, or does not meet. A received word with two distinct candidates must
occur at one of these pair intersections.

The checker examines all 930930 pairs. At each intersection it reconstructs
the actual polynomials (X-theta)H_S and removes duplicates. This last step
is essential: a single polynomial with twelve distinct punctured roots has
twelve support representations, all yielding the same candidate.

Over the production prime the result is exactly:

```text
30030 intersecting line pairs,
455 intersection points,
one distinct error polynomial at every intersection,
no outside-root candidate at an intersection.
```

These are precisely the duplicate representations of the 455 monic
degree-twelve locators on the punctured domain: each contributes
binomial(12,2)=66 line-pair intersections. All other points on the lines
have at most one representation. Hence every degree-twelve received word
in this small problem has a whole list of size at most one. A word
V=X*H_S attains one and has its extra root at zero, outside mu_16.

The characteristic sweep gives:

| Field prime | Intersection points | Whole-list maximum | Maximum outside-root sublist |
| --- | ---: | ---: | ---: |
| 17 | 959 | 2 | 1 |
| 97 | 467 | 2 | 2 |
| 1153 | 455 | 1 | 1 |
| P | 455 | 1 | 1 |

This table makes no claim of monotonicity in the prime or a bound for
unlisted characteristics. At order 16 the agreement parameters are already
within the ordinary Johnson regime, whose count bound here is three. The
numerical allowance is 15*(11-7)/(11^2-15*7)=15/4, rounded down to three.
The degree-twelve census improves this particular finite bound to one; it does
not establish anything at production length by extrapolation.

## Reproduction and remaining task

Run `python3 scripts/probes/astra_mca_outside_factor_check.py`.
It performs the full four-field affine-line census, verifies the Bezout
identity by multiplying actual polynomials at orders 16, 64 and 256 over P,
and checks the candidates' degrees, exact agreements and distinct values.
Exact synthetic division recovers the two distinct outside factors in those
small constructions. At production it checks the eight exhaustive possible
domain roots and all construction degree/cardinality margins; the general
polynomial identity and support proof are written above.

The finite census addresses a variable single extra root at order 16. The
production pair proves that outside-factor variation really occurs in
larger-degree words and that even a common nonconstant divisor of all
outside factors cannot be assumed. A bound on the number of outside-factor
fibres, or directly on their distinct values at the omitted point, remains
unproved. Neither the universal MCA lower bound nor the prize is solved.
