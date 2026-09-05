# Single-hole values as a projection of split error locators

The [single-hole reduction](astra_mca_single_hole_reduction-2026-09-05.md)
has an exact polynomial-remainder formulation. At production it imposes
`b` homogeneous linear equations on a degree-`2b-2` error locator, together
with the essential nonlinear requirement that the locator divide the
punctured domain polynomial. Dropping that divisor requirement makes the
relaxed value image contain at least `|K|-1` scalars for an explicit received
word on the production domain. Thus the linear equations alone cannot prove
the desired cap. This is not a counterexample to that cap.

The arguments below are elementary; they are not Lean-formalized. The
finite checker verifies the exact formulation and the failure of its linear
relaxation on an order-eight subgroup over F17.

## The special-pole substitution

Let `Omega` have `n` distinct nodes, choose `a in Omega`, and put
`D=Omega\{a}`, `N=n-1`, with `1<=k<=A<=N`.
For a punctured word v, a degree-less-than-k
polynomial f with value gamma at a has the unique form

```text
f(X)=gamma+(X-a)*g(X),       degree g<k-1.
```

Consequently `f(x)=v(x)` at a punctured node precisely when

```text
g(x)=v(x)/(x-a)-gamma/(x-a).
```

This is scalar-line decoding in dimension `k-1` with a special pole
direction. If the required agreement `A` is at least k, no polynomial of
degree less than `k-1` can agree with that direction on a witness support:
multiplication by `X-a` would give a degree-at-most-`k-1` polynomial with A
roots and a nonzero value at a. Thus any decoded support already satisfies
the transformed same-support no-joint condition. This substitution does
not supply a count of the decoded scalars.

## An exact remainder condition

Let `V` be the unique polynomial of degree less than N interpolating v on D,
and let

```text
P_D(X)=product_{x in D}(X-x),       e=N-A,
R_Lambda=rem(Lambda*V,P_D).
```

Assume `A>=k` and `0<=e<N`. The exact value set is

```text
{ f(a) : degree f<k, #{x in D:f(x)=v(x)}>=A }
 = { R_Lambda(a)/Lambda(a) :
       Lambda monic, degree Lambda=e, Lambda divides P_D,
       degree R_Lambda<k+e }.
```

To prove the forward inclusion, enlarge the actual error support to any
e-element subset E of D and use its monic locator Lambda. On D the
polynomials `Lambda*V` and `Lambda*f` agree. The latter has degree less than
`k+e<=N`, so it equals the remainder `R_Lambda`.

Conversely, `Lambda|P_D` implies `Lambda|R_Lambda`, since both terms in
`R_Lambda=Lambda*V-Q*P_D` are divisible by Lambda. The quotient
`f=R_Lambda/Lambda` has degree less than k and agrees with v at every node
outside E. Also `Lambda(a)!=0`, since a is not a root of `P_D`. This proves
the value formula, including padded error supports and the zero polynomial.

The map `Lambda -> R_Lambda` is K-linear. Therefore the displayed degree
condition consists of `N-k-e=A-k` homogeneous linear equations: the
coefficients in degrees `k+e,...,N-1` must vanish. Define their kernel W in
the vector space of polynomials of degree at most e. Then

```text
dim W >= e+1-(A-k).
```

At production,

```text
b=178956971, n=6b-2, N=6b-3, k=3b-1,
A=4b-1, e=2b-2,
number of linear equations=b,
dim W>=b-1=178956970.
```

If the monic degree-e slice is nonempty, its affine dimension is at least
`b-2`. This dimension statement concerns the linear relaxation, not the
subset of locators dividing `P_D`.

On `Omega=mu_n`, `P_D=(X^n-1)/(X-a)`; at `a=1` this is
`1+X+...+X^(n-1)`. The desired count still requires controlling which
elements of W are actual divisors of this particular polynomial.

## Why the linear relaxation already has too many values

Suppose two valid monic degree-e locators `Lambda_0,Lambda_1` give distinct
values `gamma_0,gamma_1`. On their two-dimensional linear span, the
functionals

```text
Lambda -> Lambda(a),       Lambda -> R_Lambda(a)
```

are independent: their determinant is
`Lambda_0(a)*Lambda_1(a)*(gamma_1-gamma_0)`, which is nonzero. Hence every
scalar gamma occurs as `R_Lambda(a)/Lambda(a)` somewhere in that span,
with `Lambda(a)!=0`.

Every polynomial in this span still lies in W. Requiring exact degree e and
then normalizing to monic removes at most one projective point. For finite K,
the monic linear relaxation therefore has at least `|K|-1` distinct finite values. These extra
locators need not divide `P_D`; the corresponding rational quotient
`R_Lambda/Lambda` need not be a polynomial. There is no valid inference from
these relaxed values to additional MCA events.

Two distinct actual values can be constructed on any domain of the
production size, without using subgroup symmetry. More generally take
integer `b>=3` and a field with at least three elements. Partition D into

```text
Z, B0, B1, L,
sizes 3b-2, b+1, b+1, b-3 respectively.
```

Set `H(X)=product_{z in Z}(X-z)` and choose `theta` different from zero and
one. Put v equal to zero on `Z union B0`, H on B1, and `theta*H` on L.
Then `f0=0` and `f1=H` each have exactly `4b-1` agreements, with error
supports `B1 union L` and `B0 union L` of size `2b-2`. Their values at a
are zero and `H(a)!=0`. The preceding argument therefore applies on the
actual production domain and field, where `|K|-1>n`.

This excludes a proposed proof that retains only the high-coefficient
linear equations and the value projection. It does not exclude a proof
using the divisor constraint, multiplicative root structure, or other
information about actual codewords.

## Exact finite control

Over F17 use

```text
Omega=(1,2,4,8,16,15,13,9), a=1, k=4, A=5, e=2,
v(2)=1, v(15)=11, all other punctured values zero.
```

The entire punctured list consists of

```text
0,       3+3X+5X^2+5X^3,       8+8X+8X^2+8X^3,
```

with values at a respectively `0,16,15`. Their error locators are
`X^2-4`, `X^2-16`, and `X^2-13`. The linear kernel is
`span(1,X^2)`. Its monic slice consists of all 17 polynomials `X^2-c`;
excluding `c=1`, which vanishes at a, gives 16 distinct relaxed values.
Only the three listed locators divide `P_D` and meet the decoding degree
condition. This checks the distinction between the exact set and its
linear relaxation on a multiplicative subgroup.

Run `python3 scripts/probes/astra_mca_single_hole_locator_check.py`. It
enumerates all 83,521 degree-less-than-four polynomials, all 21 degree-two
divisors of `P_D`, and all 289 monic degree-two polynomials over F17. It
also independently checks the original same-support MCA event on all 629
scalar/support cases. No production domain is enumerated, and no universal
scalar bound or counterexample is asserted.
