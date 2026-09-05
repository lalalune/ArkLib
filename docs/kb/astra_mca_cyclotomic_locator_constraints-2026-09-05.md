# Exact constraints on the three cyclotomic locators

The [one-triple six-pencil model](astra_mca_six_locator_consistency-2026-09-04.md)
requires, after nonzero constant rescaling, pairwise coprime polynomials

```text
A+B=C,       ABCD=X^n-1,
degree A=degree B=degree C=d=(n-10)/3,       degree D=10.
```

The rescaled A,B,C need not be monic. All four polynomials are squarefree,
split on the nonzero domain, and have nonzero constant coefficients. At
production `n=2^30`, `d=357913938`, and the coefficient field is the certified
prime field from `_PrizeShapePrimeP30.lean`.

This note proves a cyclic-shift restriction and rules out common power lifts
of order at least four. It also records an exact length-16 example in the
same prime field and the limits of a proposed elliptic-cover reformulation.
It does not exclude or construct the production locator triple, and it is
not Lean-formalized.

## Cyclic shifts constrain repeated fiber labels

For a domain element zeta define

```text
Q_zeta(X)=A(X)*B(zeta*X)-A(zeta*X)*B(X).
```

The degree-2d coefficients cancel because A and B have the same degree.
The constant coefficients cancel as well. Therefore

```text
degree Q_zeta <= 2d-1,       X divides Q_zeta.
```

If Q_zeta is nonzero, it has at most `2d-2` nonzero roots. Every domain
coordinate x for which x and zeta*x belong to the same A-root, B-root, or
C-root set is such a root: the ratio A/B takes values `0,infinity,-1` on
those three sets. Hence at most `2d-2` covered coordinates retain their fiber
label under that shift, unless A/B is invariant under it.

The invariance case has an exact restriction. Suppose zeta has order ell
and Q_zeta=0. Coprimality and equal degrees force
`A(zeta*X)=a*A(X)` and `B(zeta*X)=a*B(X)` for a nonzero constant a.
Their nonzero constant coefficients imply a=1. The relation gives the same
invariance for C, and the product identity gives it for D. Comparing
coefficients, each polynomial belongs to `K[X^ell]`. Thus

```text
ell divides d,       ell divides 10.
```

At production `gcd(n,d,10)=2`. No multiplicative symmetry of order at least
four is possible. The same-label bound

```text
2d-2=715827874
```

therefore applies to every domain shift of order at least four. A common
`X^2` lift remains possible under these necessary conditions; this argument
does not dispose of it. The bound is about the actual three-color partition,
not containment of arbitrary differences in a subgroup or a Paley estimate.

## Inversion supplies another triple, not a field conjugation

Define fixed-degree reciprocals `A*=X^d*A(1/X)`, and similarly for B,C;
use degree ten for D. Linearity and the product identity give

```text
A*+B*=C*,       A*B*C*D*=1-X^n.
```

Their root sets are the inverses of the original sets. Nothing here equates
the corresponding individual sets. In the prime field every field
automorphism is the identity. In particular, since `P=1 mod n`, every power
of Frobenius fixes the primitive n-th root G and cannot send it to `G^-1`
when n>2. The complex reciprocal-conjugation argument cannot be imported
into this field by replacing conjugation with Frobenius.

There is an explicit example with the same degree-ten defect and n=16 in
the actual prime field. Let i have order four and set

```text
A=X^2-1,
B=(i-1)*(X^2-i),
C=i*(X^2+1),
D=-(X^2+i)*(X^8+1)/(1+i).
```

Then `A+B=C` and `ABCD=X^16-1`. All denominators are nonzero. For a primitive
sixteenth root omega with `omega^4=i`, the A,B,C root exponents are
`{0,8}`, `{2,10}`, `{4,12}`. The inverse B-root exponents `{6,14}` belong to
D, not to the original three fibers. This example precludes a uniform
exclusion for every dyadic length based only on ten leftover roots and these
algebraic identities. It is exactly an X-squared construction. Power-lifting it would
also multiply the defect ten, so it is not a production construction.

## The elliptic cover is exact, but its basic genus bound is attained

Let Cf be the smooth projective model of `Y^3=f(X)`, where `f=ABC`.
Work geometrically when computing its genus. Since f is squarefree of degree
3d and the characteristic is not three, its degree-three X-map has 3d
finite branch points, all with ramification index three. Infinity is
unramified, with three geometric points. The tame
[Riemann-Hurwitz formula](https://stacks.math.columbia.edu/tag/0C1B) gives

```text
2g(Cf)-2=-6+2*(3d),       g(Cf)=3d-2=n-12.
```

The curve `E: z^3=t*(1-t)` has three branch points over the t-line and genus
one, with a rational point. The formulas

```text
t=A/C,       z=Y/C
```

define a morphism Cf -> E of degree exactly d: the common t-map has degree
3d on Cf and degree three on E. The map is separable because d<P. Moreover
the X-map and the E-map generate the full function field, since
`Y=z*C(X)`.

Consequently the
[Castelnuovo-Severi inequality, Proposition 2.1 of Poonen](https://math.mit.edu/~poonen/papers/gonality.pdf)
applies to the degree-three map to P1 and degree-d map to E. It gives

```text
g(Cf) <= 3*g(P1)+d*g(E)+(3-1)*(d-1)=3d-2.
```

This is equality for every triple under consideration. It gives no
contradiction or stronger map-degree lower bound here. For comparison,
`Y^3=X^n-1` has genus n-1 and an explicit degree-n/2 map
`(X,Y) -> (X^(n/2),Y)` to the genus-one curve `Y^3=U^2-1`. Existence of that
map does not establish its minimality, and deleting ten branch points does
not automatically preserve a proposed minimal degree.

At production `P=2 mod 3`, so cubing is a bijection on F_P. Every finite X
therefore yields exactly one rational Y on Cf. Its affine model is smooth:
at a zero of f the X-derivative is nonzero, and elsewhere the Y-derivative
is nonzero. At infinity put `v=Y/X^d`; its limiting equation is
`v^3=leading_coefficient(f)`, with a nonzero right-hand side. It has exactly
one F_P root, and that root is simple. Hence Cf has exactly `P+1` rational
points. The same count holds for E, whose affine fibers each have one point
and whose unique point at infinity is rational.

Thus the F_P point count alone supplies no exclusion either. No specialized
supersingular, Jacobi-sum, or cyclotomic elliptic-map lower bound is claimed.

## Reproduction

Run `python3 scripts/probes/astra_mca_cyclotomic_locator_check.py`. It verifies
the archived field certificate, the actual-prime length-16 polynomial
identities and all sixteen cyclic shifts, the inversion example, and the
exact production degree/genus arithmetic. It does not construct the
production polynomials or enumerate an entire field or production domain.
