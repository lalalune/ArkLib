# Private-locator cubic normal form and the section-degree obstruction

The two-disjoint-triple incidence pattern forces a cubic polynomial identity
with quadratic cofactors. It does not immediately force a small-degree
solution: an explicit smooth elliptic family below has quadratic cofactors
and sections of unbounded degree. This excludes the shortcut from bounded
coefficient degree alone to bounded section degree.

The normal form is a necessary condition for the actual configuration. The
elliptic example only addresses that shortcut: it does not verify squarefree
private locators, saturation, the required cyclotomic product, or the
production characteristic. Neither part is a Lean formalization or a proof
of the prize bound.

## The common locator span forces an intersection factor

Use the hypotheses of the
[two-disjoint-triple incidence note](astra_mca_incidence_feasibility-2026-09-05.md).
Put `m=2b-2`, `n=3m+4`. The long-flat locators T1,T2 are coprime monic
quadratics, `D=T1*T2`, and the two private triples have common product

```text
A1*A2*A3 = B1*B2*B3 = H = (X^n-1)/D.
```

Every private locator has degree m, and the three in each triple are
pairwise coprime. Their constant spans have dimension two. The full spaces
`E1=T1*span(A1,A2)` and `E2=T2*span(B1,B2)` have a three-dimensional sum,
so their intersection is one-dimensional. A nonzero generator J satisfies

```text
J=D*R,       R != 0,       deg R <= m-2.
```

Indeed J is divisible by both coprime quadratics and has degree at most
`m+2`. Homogeneously R is a section of degree `m-2`; its affine degree may
be smaller because J can vanish at infinity.

No configured locator is proportional to J, since that would place a
configured point on both disjoint long lines. We can consequently choose
bases `(F,T2R)` and `(G,T1R)` and constants with

```text
Ai=ki*(F-ai*T2*R),       Bj=lj*(G-bj*T1*R),
ki,lj != 0; all three ai distinct; all three bj distinct.
```

The degrees of F,G are at most m. Pairwise coprimality implies
`gcd(F,T2R)=gcd(G,T1R)=1`, hence `gcd(R,H)=1`: at a root of R the
three Ai are nonzero multiples of the same F-value. This does not imply
`gcd(R,D)=1`; R may vanish in either long-flat region.

## A depressed cubic and a nonempty production degree interval

Work over an algebraic closure in characteristic different from three.
Absorb the quotient of the two leading constants by rescaling G and its
three bj, then translate F,G by constant multiples of T2R,T1R. The product
identity becomes

```text
F^3 + p*T2^2*R^2*F + q*T2^3*R^3
  = G^3 + p'*T1^2*R^2*G + q'*T1^3*R^3.
```

Both underlying constant cubics have nonzero discriminant. At production,
`P=2 mod3`, so cubing is bijective on F_P and this normalization can be
performed over F_P itself. Since the constant cubics split into three
distinct F_P-roots, `p,p'!=0`: a polynomial `Z^3+q` has only one F_P-root.
In particular the production case cannot use the stronger special identity
obtained by setting `p=p'=0`.

Rearranging gives the exact necessary divisibility

```text
F^3-G^3 = R^2*C,
C=p'*T1^2*G-p*T2^2*F+R*(q'*T1^3-q*T2^3),
deg C <= m+4.
```

For `m>6`, `F^3-G^3` is nonzero. Otherwise, after a constant rescaling,
G=F and

```text
F*(p*T2^2-p'*T1^2)+R*(q*T2^3-q'*T1^3)=0.
```

The first parenthesis is nonzero: if it vanished, coprimality of T1,T2
would force `p=p'=0`; the identity would then force `q=q'=0`, contradicting
the cubic discriminants. The second parenthesis is also nonzero. Since
`gcd(F,R)=1`, R divides the first and F divides the second. Thus
`deg R<=4`, `deg F<=6`, and all private locators have degree at most six,
contradicting `m>6`.

There is a useful lower bound as well. Write `r=deg R`. If `r<m-2`, then
`deg F=deg G=m`. Since `deg(R^2*C)<=2r+m+4<3m`, their leading cubes agree.
After multiplying G by a cube root of unity, `deg(F-G)<m`, whereas the
other two difference factors have degree m. Their product is nonzero, so

```text
0 <= deg(F-G) <= 2r-m+4.
```

The case `r=m-2` also satisfies the resulting bound. Consequently

```text
ceil((m-4)/2) <= deg R <= m-2,       m>6.
```

At production `m=357913940`, this leaves the interval
`178956968 <= deg R <= 357913938`, rather than a contradiction.

At roots of R, F and G are nonzero, so the three factors `F-omega^j*G`
are pairwise coprime there. One can allocate the prime-power factors of R
as `R=R0*R1*R2`, with pairwise coprime Rj and
`Rj^2 | F-omega^j*G`. Over F_P with `P=2 mod3`, the latter two parts are
conjugate over F_(P^2). Their product has only even-degree irreducible
factors over F_P, but the available degree interval permits this. These
divisibilities alone do not supply an exclusion.

## An explicit smooth cubic with unbounded section degrees

The following construction is over characteristic zero and illustrates the
degree-bound obstruction. It does not assert all the preceding locator
hypotheses. Over Q(t), put

```text
T1=7t^2-10t-1,       T2=14t^2-6t-4,
U=-14t^2+2t,         V=-7t^2-6t+1,       R=1.
```

The quadratics are squarefree and coprime. Exact integer-polynomial
arithmetic gives

```text
U^3-T2^2*R^2*U = V^3-T1^2*R^2*V.
```

Both sides are products of three linear forms in their respective
two-dimensional spaces. Set `z=T1/T2`, `u=U/T2`, and `v=V/T2`. The base
map z has degree two and the cubic becomes `u^3-u=v^3-z^2*v`. It is
birational to

```text
E_z: y^2=x^3-3z^2*x+z^6+1,
x=(z^4*u-v)/(u-z^2*v),       y=(z^6-1)/(u-z^2*v),
u=(z^2*x-1)/y,              v=(x-z^4)/y.
```

The discriminant is `-432*(z^6-1)^2`, and the j-invariant is
`-6912*z^6/(z^6-1)^2`. The generic fiber is therefore smooth and
non-isotrivial. The checker verifies these birational identities by
expanding the denominator-cleared polynomials, not just by specialization.

Let P be the section supplied by U,V above. At `t=0`, one has `z=1/4`.
Scaling the fiber by `(X,Y)=(16x,64y)` gives

```text
Y^2=X^3-48X+4097,       P=(256,-4095).
```

Both 11 and 17 are primes of good reduction. The point has exact order
8 modulo 11 and exact order 13 modulo 17. It is therefore non-torsion:
for a torsion point, its 2-primary order must survive reduction at either
odd prime, which these two orders contradict. This uses the standard
prime-to-p torsion-reduction theorem; see
[Milne, Elliptic Curves, II Corollary 5.7, printed page 66](https://jmilne.org/math/Books/ectext6.pdf).
Hence the original section is non-torsion as well.

The example also has nontrivial dependence on the quadratic base change.
The other preimage of `z=1/4` is `t=17/7`, since
`4T1-T2=2t*(7t-17)`. The conjugate section specializes to
`(-47/4,441/8)` on the same integral fiber. The difference from P has
orders 16 modulo 11 and 1 modulo 17, so it too is non-torsion by the same
2-primary argument. The involution of `Q(t)/Q(z)` is exactly
`sigma(t)=(17-7t)/(7-49t)`; the checker verifies `z(sigma(t))=z(t)` and
`sigma(sigma(t))=t`. The specialized difference proves `P-sigma(P)` is
non-torsion. Thus no nonzero multiple of P descends to Q(z): such a
descent would imply `N*(P-sigma(P))=0`.

The conclusion about unbounded degree uses an **external standard height
theorem**, beyond the exact Python calculations. For this non-isotrivial
elliptic surface the height pairing is positive definite modulo torsion,
and `height(NP)=N^2*height(P)`. The intersection formula for the height
has bounded fiber-correction terms, so these multiples have unbounded
coordinate degrees. See
[Schutt and Shioda, Theorem 11.5 and subsection 11.8](https://arxiv.org/pdf/0907.0298).
The fixed birational formulas transfer this conclusion to rational
solutions u,v of the cubic relation. Clear common denominators and remove
the gcd of the resulting polynomial triple `(U,V,R)`. These primitive
triples still satisfy the homogeneous cubic with the same quadratic T1,T2.
Their degrees are unbounded: a bound on their degrees would bound the
degrees of `u=U/(T2R)`, `v=V/(T2R)`, and then x,y through the fixed
birational formulas. This is not growth obtained by multiplying one
solution by a common polynomial.

This is an ordinary mathematical deduction using the cited theorem. It is
not a Lean-checked height bound, and the checker does not purport to prove
the external height or torsion-reduction theorems.

## Reproduction and remaining scope

Run from the repository root:

```sh
python3 scripts/probes/astra_mca_private_cubic_surface_check.py
```

It returns `PASS_PRIVATE_CUBIC_SURFACE_CONTROLS`, checking the full symbolic
birational and discriminant identities, the integer section identity,
quadratic gcds and degree, both rational specializations, both pairs of
finite orders, and the arithmetic of the production degree interval. It
uses only the standard library; no search or external CAS is required.

The unbounded family does not establish preservation of squarefree private
factors, a prescribed degree pattern, saturation, or the cyclotomic product
`H=(X^n-1)/D`. Non-descent through Q(z) also does not by itself prove that
the two private ratios jointly generate Q(t). No production-characteristic
claim is made. A successful exclusion must use additional actual-domain
or realization conditions; bounded-degree coefficients in the cubic
equation alone are insufficient.
