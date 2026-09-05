# A reduced exact-error eliminant for punctured values

The [single-hole locator formulation](astra_mca_single_hole_locator-2026-09-05.md)
has an exact elimination model with one reduced point per decoded
polynomial. It uses actual factors of the punctured domain polynomial and
removes padded error supports. The characteristic polynomial of value
multiplication counts decoded polynomials with their value collisions;
its minimal polynomial is squarefree and has exactly the distinct
punctured values as roots.

This supplies an exact remaining degree obligation, **not a bound on that
degree**. No assertion here proves the production cap or is Lean-formalized.

## The actual divisor and exact-error conditions

Let `D=mu_n\{1}`, `P_D=(X^n-1)/(X-1)`, and `N=n-1`. Assume the
characteristic does not divide n and all n subgroup nodes belong to K.
Let V, of degree less than N, interpolate the received word v on D. Require
`1<=k<=A<=N` agreements, and put `e=N-A`.

For each integer `0<=d<=e`, take monic unknown polynomials Lambda and H
of degrees d and N-d and impose the coefficient identity

```text
Lambda*H=P_D.
```

Define polynomial functions of the coefficients of Lambda by division by
the fixed monic polynomial P_D:

```text
R=rem(Lambda*V,P_D),
Q=(Lambda*V-R)/P_D,       degree Q<d.
```

The degree condition `degree R<k+d` consists of `N-k-d` linear equations.
The factorization implies `Lambda|R`. Its quotient f has degree less than
k, and cancellation in `Lambda*V-R=Q*Lambda*H` gives

```text
V-f=Q*H.
```

At a root x of Lambda, H(x) is nonzero because P_D is squarefree. Thus x
is an actual error precisely when Q(x) is nonzero. The exact-error
condition is consequently

```text
S_d := Res_X(Lambda,Q) != 0.
```

Equivalently, differentiating the product identities at x gives
`Lambda'(x)*(v(x)-f(x))=Q(x)*P_D'(x)`, with both derivatives nonzero.
Outside the roots of Lambda the word and f agree. Therefore this
invertibility condition removes exactly the padded support points.
For d=0 use Lambda=1 and `Res(1,Q)=1`, the empty-product convention.

Conversely, a polynomial f of degree less than k with exactly d errors
determines a unique monic Lambda, the locator of those errors. Its
complement H, remainder R, and quotient Q satisfy all the conditions above.
Its error count determines d, so it occurs only once across `0<=d<=e`.

## Why the factor algebra is reduced

The monic factorization equations have exactly `binomial(N,d)` geometric
solutions, one for each d-element subset of D; every solution belongs to K.
Their derivative map in coefficient directions is

```text
(deltaLambda,deltaH) -> H*deltaLambda+Lambda*deltaH.
```

Both its domain and codomain have dimension N. If its image is zero,
coprimality forces Lambda to divide deltaLambda, while
`degree deltaLambda<d`. Thus deltaLambda and then deltaH vanish. This proves
the derivative map invertible, including d=0.

There is an explicit algebraic product decomposition as well. In the
coordinate algebra define, for every x in D,

```text
u_x=Lambda'(x)*H(x)/P_D'(x),
1-u_x=Lambda(x)*H'(x)/P_D'(x).
```

The denominator is a fixed nonzero field element. The factorization and
its derivative give `u_x*(1-u_x)=0`, `u_x*Lambda(x)=0`, and
`(1-u_x)*H(x)=0`. Thus u_x is an idempotent. Expanding
`product_x(u_x+(1-u_x))=1` decomposes the algebra into factors indexed by
subsets E of D. On the E factor, Lambda vanishes on E and H on its
complement. If `|E|!=d`, one of these monic polynomials has more roots
than its degree, forcing that factor to be zero. The usual interpolation
argument remains valid over this coefficient algebra because differences
of distinct domain nodes are units. If `|E|=d`, interpolation fixes Lambda
and H to the two corresponding root products, so the factor is K; it is
nonzero because that factorization actually exists. Consequently the
algebra is exactly a product of `binomial(N,d)` copies of K and is reduced.

Imposing the linear remainder equations takes a quotient of this product
of fields. Inverting S_d retains exactly the factors where S_d is nonzero.
These operations leave a reduced product of fields. Denote the result by
B_d; its factors are in bijection with decoded polynomials having exactly
d errors. This argument retains the full factorization constraint throughout.

## The value polynomial and its exact degree obligation

Evaluation at the omitted point gives

```text
Lambda(1)*H(1)=P_D(1)=n != 0,
f(1)=R(1)*H(1)/n.
```

In particular, no denominator saturation is necessary. Let B be the
product of B_d for `0<=d<=e`, and let M be multiplication on B by the
displayed value function. The factors of B provide a basis in which M is
diagonal, with one diagonal entry f(1) for each decoded polynomial f.
Its characteristic polynomial is exactly

```text
C(Y)=product_{degree f<k, #{x in D:f(x)=v(x)}>=A} (Y-f(1)).
```

Thus a root's multiplicity is the number of distinct decoded polynomials
with that value. There is no padding, scaling, or local algebra
multiplicity. A polynomial annihilates M precisely when it vanishes at
every diagonal value, so the minimal polynomial is

```text
E(Y)=product_{gamma in the distinct punctured-value set} (Y-gamma).
```

It is squarefree. For an empty list use C=E=1. This proof is valid in
positive characteristic even when value multiplicities exceed the
characteristic; one should not replace it by an unjustified single
division of C by `gcd(C,C')`.

An equivalent saturated ideal, with an extra variable Y, is

```text
J_d=(coefficients of Lambda*H-P_D,
     coefficients R_j for k+d<=j<N,
     n*Y-R(1)*H(1)) : S_d^infinity.
```

The intersection `J_d intersect K[Y]` has the distinct exact-d values as
its simple roots. Taking the least common multiple of these monic
generators over all d gives E. Equivalently, the whole value image is the
spectrum of the semisimple multiplication operator M.

At production,

```text
n=1073741824, N=1073741823,
k=536870912, A=715827883, e=357913940.
```

The desired single-hole bound is now exactly `degree E<=n` for every v.
The construction alone only supplies the support bound
`degree E<=degree C<=sum_{d=0}^e binomial(N,d)`. Neither the sparse shape
of P_D nor the two-generator Padé description has been shown here to
reduce this to n. The characteristic-polynomial degree need not equal
the number of distinct values.

## Why a simpler resultant presentation has extra multiplicity

For monic Lambda of degree d, one can instead form

```text
F_Lambda(Z)=Res_X(P_D(X),Lambda(X)+Z)
          =product_{x in D}(Lambda(x)+Z).
```

The vanishing of its coefficients of `Z^0,...,Z^(d-1)` is set-theoretically
equivalent to `Lambda|P_D`: the order at zero counts distinct domain roots
of Lambda and cannot exceed d. For d>=2 this presents the divisor set with
nonreduced local algebras.
Near a divisor with roots E, use coordinates `y_x=Lambda(x)` for x in E.
The factors from the other nodes are units modulo `Z^d`, so the local ideal
is generated by the d elementary symmetric functions of these y_x. Only
the first has a linear part. For d=2 this gives explicitly
`K[y1,y2]/(y1+y2,y1*y2)`, a two-dimensional algebra with a nonzero nilpotent.

After adding the `N-k-d` linear decoding conditions, its tangent dimension
is at least `2d+k-N-1`. At the production degree d=e, this is
`b-3=178956968`, where `b=178956971`. Saturating by S_d does not change the
local algebra at an exact-error point because S_d is already a unit there.
Thus exact-error saturation alone does not repair this presentation. The
monic factorization equations used above are reduced from the outset.

## Bounded independent control

Run `python3 scripts/probes/astra_mca_exact_error_eliminant_check.py`.
Over F17 it uses `Omega=mu_8`, omitted point 1, dimension k=4, and the
existing word with `v(2)=1`, `v(15)=11`, and other punctured entries zero.
It independently enumerates all `17^4` polynomials, records their exact
error supports, and compares them with the saturated factor algebra.
It also checks all relevant factorization Jacobians and the value formula.

At agreement A=5 there are three decoded polynomials and three values,
with `C=E=Y*(Y-15)*(Y-16)`. A second algebra control at A=4 has 23 decoded
polynomials and 15 distinct values. It therefore distinguishes the norm
degree from the minimal-polynomial degree and verifies padding removal
across different locator degrees. This second threshold is not the
production agreement regime. A zero-word control checks the d=0 endpoint.
No production domain or production list is enumerated.
