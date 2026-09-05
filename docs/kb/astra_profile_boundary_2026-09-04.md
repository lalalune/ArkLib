# Contact-profile realizability near the minimum binding weight

There is a structural exclusion for the surviving uniform order-34 profile.
At the exact binding degrees `(total,YS,R)=(2364,47,10)` and minimum contact
weight 6160327, a received affine line represented by polynomials of degree at
most **170039** forces the factor to contain that line's polynomial graph.
This contradicts irreducibility and positive R degree. Higher-degree received
lines remain possible under this argument, so it does not exclude the general
binding flag or improve the protocol score.

This note continues the [lower-R repair](astra_kernel_lowr_2026-09-04.md) and
[derivative-incidence](astra_incidence_derivative_repair-2026-09-04.md) analyses.
The companion pin is
[`032154395c51fd6f77715a7f42d9a987ab9fb48a`](https://github.com/proximity-prize/proximity-prize/commit/032154395c51fd6f77715a7f42d9a987ab9fb48a).
These are mathematical proofs and reproducible checks, not Lean integration.

## The restricted leading form

Put `n=262144`, `w=131071`, and let the actual contact weight be
`c=w*47-10+delta`, with `delta>=0`. The homogeneous part of joint YR degree 47
has the form

```text
sum_{j=0..10} A_j(X,Z) Y^(47-j) R^j,
degree_X(A_j) <= delta+j-10.
```

A negative degree bound means A_j=0. Consequently at delta=0 this part is
exactly `a(Z) Y^37 R^10`, where a is nonzero and has Z degree at most 2317.
After localization at any node, its coefficient of free `R^47` is
`a(Z)*t^37`. Lower joint-degree terms cannot contribute to that coefficient.
Thus the local contact order is at most **37 at every node**, improving the
general bound 57 at this precise weight.

For a factor universal on a nonzero full source kernel with contact order
at least 37, this sharpens the earlier repair consequences. The full-weight
repair requires at least `ceil(6160328/37)=166496` positive-contact nodes.
The cap-nine rank bound at order 37 is 13275685, so increasing an
order-at-most-33 node to order at most 37 adds at most 2907900 rows.
The same nullity deficit 138332486935 therefore requires at least **47572**
nodes of order at least 34. These stronger counts apply at delta=0; they
must not be substituted for the general-weight counts 131071 and 6009.
They still do not exclude the uniform order-34 profile.

For general delta, let j* be the largest index of a nonzero A_j. At every node
where `A_j*(x_i,Z)` is nonzero, the same coefficient has t order `47-j*`.
Hence `nu_i<=47-j*` outside at most `delta+j*-10` nodes, using distinct-node
root counting on a nonzero X-polynomial coefficient of A_j*. This restricts
the high-order tail but does not rule out order 34 everywhere.

## The exact weight window for that profile

For the fixed cap-nine repair and the uniform profile `nu_i=34`, its coefficient
count first exceeds its rank upper bound at

```text
c=6202658,    delta=42331.
```

The dimension difference is -865305 one weight unit below and +152310 at the
threshold. Therefore that repair leaves only `0<=delta<=42330` unresolved for
the **uniform order-34** profile. For `10<=delta<w`, the coefficient count is
affine with slope 1017615, since every joint-degree-at-most-47 channel is present
and no degree-48 channel is present. The probe verifies both threshold sides
and the remaining ten initial integer cases; no source grid is searched.

The full R-cap-ten order-34 interpolation count becomes positive slightly
earlier, at delta=41030. That guarantees a nonzero interpolant in that box,
not an irreducible factor with these exact degrees or universal provenance.
At delta=0 its dimension estimate is negative by 45395446319, which likewise
does not prove the actual kernel is zero. These distinctions matter when
interpreting the scalar profile.

## A received-line factorization theorem

Let `U(X,Z)=U0(X)+Z*U1(X)` represent the received words on all n distinct nodes.
Use a degree bound `d>=w` for U in X, with `d<n+1`. Suppose a polynomial F has

```text
joint YR degree <= y,  R degree <= r,
contactWeight(F) <= w*y-r+delta,
contactOrder_i(F) >= m0 at every node,
m0>=r, delta>=0.
```

If

```text
(y-r)*d+delta < n*(m0-r),                                (1)
```

then **Y-U divides F**. In particular, no irreducible positive-R factor can
satisfy these assumptions. This statement does not require universal-kernel
provenance or a far-word hypothesis.

To prove it, expand using a new indeterminate T:

```text
F(X,U(X,Z),U_X(X,Z)+T,Z) = sum_{j=0..r} B_j(X,Z) T^j.
```

At a node x_i, put X=x_i+t and give both t and T weight one. The original local
coordinate v becomes

```text
U(x_i+t,Z)-U(x_i,Z)-t*U_X(x_i+t,Z)-t*T.
```

Its weight is at least two; the linear Taylor terms cancel in every
characteristic. The original free R variable maps to a polynomial of
nonnegative weight. Thus `B_j` has a root of multiplicity at least `m0-j` at
every x_i, for all `j<=r`.

On the other hand, expanding each global monomial gives

```text
degree_X(B_j) <= c(F)+(d-w)*y-j*(d-1)
                <= (y-r)*d+delta+(r-j)*(d-1).
```

Here `d>=w` justifies replacing each monomial's joint YR degree by y. Inequality
(1), together with `d-1<n`, makes this strictly smaller than
`n*(m0-r)+n*(r-j)=n*(m0-j)`. Distinct-node root counting over K(Z) forces every
B_j to vanish. The change `R=U_X+T` is invertible, so F(X,U,R,Z)=0. Division by
the monic polynomial Y-U gives the claimed factorization. Since Y-U is R-free,
an irreducible positive-R F cannot be its associate.

For the binding case `m0=34`, condition (1) is exactly

```text
37*d+delta < 24*n.
```

It excludes received-line degrees through 170039 at delta=0, and through
168895 at delta=42330. These cutoffs are exact: increasing each by one fails
the strict inequality. A received line has a unique representative with each
word's degree below n; taking d to be the maximum of w and those degrees
satisfies the theorem's degree-range hypotheses. The uniform lower contact
bound is essential: knowing that only 6009 nodes have order at least 34 does
not permit this application.

## Compact inversion check

On the nonzero evaluation domain, use the Reed--Solomon inversion chart

```text
Ftilde(X,Y,R,Z)
  = X^c F(1/X, X^(-w)Y, X^(1-w)*(wY-XR), Z).
```

Every exponent of X is nonnegative because c bounds the original contact
weight. A monomial with original exponents `(a,b,j,z)` contributes new contact
weight `c-a+j`, at most c+r. The invertible linear substitution in (Y,R) over
K(X) preserves the exact joint YR, R, and residual total degrees. A possible
factor X must be removed before asserting polynomial irreducibility; it is a
unit at every evaluation node and its removal can only lower contact weight.

The transformed received word at x is `x^w U(1/x,Z)`, reduced modulo X^n-1.
Contact orders are preserved: the old node displacement is
`-t/(x*(x+t))`, of weight one, and the old v-coordinate has weight at least two
with a nonzero v coefficient. The local change has a filtered inverse given by
the same inversion, so minimum weights agree. Multiplication by X^c is a local
unit. These calculations require nonzero nodes; they hold on the companion's
multiplicative domain.

At delta=0, the leading monomial supplies the nonzero X-degree-zero term
`w^10*a(Z)*Y^47`, so Ftilde has no factor X and has exact contact weight c+10.
Here `w` is nonzero in the companion field of characteristic 2130706433.
The factorization test in the inverted chart therefore uses delta'=10 and
again excludes received degrees through 170039.

Both chart tests can still fail simultaneously. An original non-code monomial
index e maps to `e'=n+w-e`. The interval

```text
170040 <= e <= 223175
```

makes both e and e' exceed 170039. This only exhibits a nonempty arithmetic
degree window; it constructs neither F nor a universal factor, and makes no
claim about the needed far-word or large-family properties. Dense high-degree
received lines likewise need not be excluded by these two tests.

## Reproduction and remaining scope

Run `python3 scripts/probes/astra_profile_boundary.py`. It checks the exact
weight thresholds, leading-monomial restriction, degree cutoffs, and dual-chart
window. It also verifies the polynomial substitution, coefficient root-order
bounds, inversion contact preservation, and double-inversion identity on 72
finite polynomial cases. Those tests check transcription, not the general
theorem or the production prize claim.

The structural factorization proof received independent mathematical reviews.
Formalizing it against the companion's polynomial and contact interfaces is
still required. The remaining case includes higher-degree received lines and
nonuniform contact profiles; this round does not prove them impossible or
change the numerical error allowance.
