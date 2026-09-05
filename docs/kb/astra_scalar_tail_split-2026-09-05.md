# Splitting the scalar list by its next derivative

The [scalar differential carrier](astra_scalar_differential_carrier-2026-09-05.md)
gives a written uniform list bound of 12546010856 at the companion profile.
The argument below improves that written bound to **4812927256**, using the
stronger hypothesis that the characteristic exceeds the interpolation's
weighted degree cap. That hypothesis holds for the companion parameters.

This is a mathematical argument with exact finite controls. It has **not**
received independent mathematical review or a complete Lean formalization.
It does not improve the MCA bound, prove the companion ProtocolClaim, or
determine a grand-prize threshold.

## Setup and statement

Let 2<=w<A<=n, and let Q in K[X,Y,R] be the nonzero fixed-word interpolation
polynomial from the preceding note, with

```text
weighted_degree_(1,w,w-1)(Q) < D,
total_degree_(Y,R)(Q) <= d0,
Q(X,f,f')=0 for every candidate polynomial f.
```

Assume char K=0 or char K=p>D, and put

```text
rho=(n-w)/(A-w),
E_next(d)=(2w-1)(d-1)+1.
```

If d0>=1 and E_next(d0)>=rho, the resulting bound is

```text
list size <= d0*E_next(d0)+d0*(d0-1)
          = d0*(2w*(d0-1)+1).                         (1)
```

More generally the same proof gives the floor of
d0*max(E_next(d0),rho)+d0*(d0-1). If d0=0 there is no candidate.
For an infinite field, apply the proof to an arbitrary finite subset of the
list; the uniform finite-subset bound then bounds the complete list.

Factor Q in K[X,Y,R], discarding its X-only factors. Each remaining primitive
irreducible factor F has weighted degree <D and total Y,R degree d<=d0.
Weighted degree is additive under multiplication, since the highest weighted
homogeneous parts have nonzero product. Thus the same cap applies to F.

As before set H=F_R, G=-F_X-RF_Y and use the derivation on
K[X,Y,R,H^(-1)]/(F),

```text
delta(X)=1, delta(Y)=R, delta(R)=G/H.
delta^j(Y)=N_j/H^(2j-3), j>=2,
degree_(Y,R)(N_j) <= (2j-3)(d-1)+1.                  (2)
```

Factors with H=0 are independent of R and contribute at most d candidates.
For H nonzero, candidates with H(X,f,f')=0 contribute at most d(d-1), by the
same separability and Bezout argument as in the preceding note. The remainder
of this argument concerns regular candidates, meaning H(X,f,f') is nonzero
as a rational function of X.

## A proper next-derivative cut

Every polynomial f of degree <=w has f^(w+1)=0. If N_(w+1) is nonzero modulo
F over K(X), all regular candidates give distinct points of

```text
F=N_(w+1)=0 in the Y,R plane over an algebraic closure of K(X).
```

These equations have no common curve component, so Bezout gives at most
d*E_next(d) such candidates. This counts points directly; it does not incur
the scalar incidence ratio rho from the previous carrier argument.

## When the next derivative vanishes identically

Suppose instead delta^(w+1)(Y)=0 in the localized coordinate ring. All higher
derivatives of Y are then zero. We show that any finite set of regular
polynomial solutions is contained in a union of coefficient curves of total
degree at most d. The fact that these curves are over a constant field,
rather than merely over K(X), is essential to the degree argument.

Choose x0 in an algebraic closure of K away from the finitely many roots of
H(X,f,f') for the selected candidates. Also exclude the finitely many points
where a coefficient denominator used in a polynomial identity vanishes or
the specialized equation is identically zero. This is possible even when K
is finite, because its algebraic closure is infinite.

For a point P=(x0,y,r) of F=0 with H(P) nonzero, define

```text
q_P(U)=sum_(j=0..w) delta^j(Y)(P)/j! * (U-x0)^j.       (3)
```

We first prove that this is an actual polynomial solution of F, not only a
Taylor polynomial with a finite contact order. In characteristic p, the map

```text
a |-> sum_(j=0..p-1) delta^j(a)(P)/j! * t^j
```

is a ring homomorphism to Kbar[t]/(t^p). This follows directly from the
iterated Leibniz identity; every denominator j! occurring here is invertible.
Localization at H is valid because H(P) is nonzero. The map sends X to x0+t,
Y to q_P(x0+t), and R=delta(Y) to q'_P(x0+t). It sends F to zero. Therefore

```text
F(U,q_P(U),q'_P(U)) is divisible by (U-x0)^p.
```

Its degree is <D<p, so it is the zero polynomial. In characteristic zero,
use the same truncated exponential modulo t^M for an integer M>=D.

For an actual selected solution f, specialization commutes with delta and
(3) recovers f by Taylor's identity. Thus the image of the open subset H!=0
of the specialized curve F(x0,Y,R)=0 contains every selected coefficient
point. Taking reduced image closures gives curves W_i over Kbar. There are
no constant image components: evaluation at x0 recovers both y and r from
q_P, so the map is injective on its domain. The generic polynomial on each
W_i solves F and is regular, since its derivative projection is nonzero
already at x0 on the defining open subset.

### The coefficient curves have degree at most d in total

Let T be a new transcendental variable. Project each coefficient curve W_i
linearly to the plane over Kbar(T), by

```text
(c_0,...,c_w) |-> (sum c_j*T^j, sum j*c_j*T^(j-1)).     (4)
```

Its image is contained in F(T,Y,R)=0. The derivative reconstruction (2)
followed by Taylor's formula recovers every c_j rationally from the image:
use the derivation in T that fixes the coefficient functions c_j, then
differentiate F(T,f(T),f'(T))=0. Regularity gives the same delta recursion.
Consequently (4) is birational onto its image. Different W_i have different
image components, because this rational inverse is the same for all of them.

On the projective closure of W_i, the linear system for (4) is

```text
[z:c_0:...:c_w] |-> [z:sum c_j*T^j:sum j*c_j*T^(j-1)].
```

It has no base points. A base point would have z=0. The projective curve has
only finitely many points at infinity, and their coordinates are over Kbar.
At each such point (c_0,...,c_w) is nonzero; hence sum c_j*T^j is nonzero
because T is transcendental. The base-point-free linear projection pulls
back O(1) to O(1). Since it is birational on curves, it preserves degree.
This is the usual degree/pullback formula for proper curves; see the
[Stacks Project, degrees on curves](https://stacks.math.columbia.edu/tag/0AYQ).

The distinct image curves are components of a plane curve of degree d.
It follows that sum degree(W_i)<=d. Applying the scalar carrier incidence
lemma now bounds the regular candidates in this identically-zero-tail case
by d*rho, rather than by d*E(d)*rho.

This projection argument is specific to coefficient curves: their boundary
at infinity is finite. Applying it unchanged to an MCA coefficient surface,
whose boundary can be a curve, would leave an unproved base-point assertion.

## Combining factors and the companion arithmetic

Each regular factor contributes at most d*max(E_next(d),rho). Add the
singular allowance d(d-1) and sum over distinct factors. The inequalities
sum d<=d0, E_next(d)<=E_next(d0), and
sum d(d-1)<=d0(d0-1) prove (1). The independent-of-R factors also fit because
max(E_next(d0),rho)>=1. Repeated factors need only be counted once.

For the existing uniform interpolation dimension certificate, the values are

| Quantity | Exact value |
|---|---:|
| n, w, A | 262144, 131071, 181353 |
| m, R cap | 99, 30 |
| D=mA | 17953947 |
| Characteristic p | 2130706433 |
| Source dimension C | 30638265433 |
| Single-node contact rank L | 116870 |
| C-nL | 1496153 |
| Total Y,R degree cap d0 | 136 |
| E_next(136) | 35389036 |
| Proper-cut allowance d0*E_next(d0) | 4812908896 |
| Singular allowance | 18360 |
| Flat-curve incidence ratio rho | 131073/50282 |
| New written list bound | 4812927256 |

In particular p>D and E_next(136)>rho. Also

```text
binomial(4812927256+1,2)=11582134388180308396 < p^6,
4812927256 < floor(p^6/2^128)=274980728111395087.
```

The existing exact interleaving projection therefore transfers this written
bound to every positive arity, including eight. The sharper scalar estimate
still supplies no same-radius MCA bound.

## Why this aggregate bound does not close the grand predecessor

At the [single-hole production predecessor](astra_mca_single_hole_reduction-2026-09-05.md),
write n=6b-2=2^30 and w=3b-2, with b=178956971. The required value budget is n.
The aggregate allowance in (1) is already too large at the smallest nonlinear
total degree:

```text
B(2)=2*(2w+1)=2n-2=2147483646 > n.
```

B(d) increases for d>=2. Thus a certificate giving only the total degree d0
of an arbitrary differential relation cannot use (1) to reach that budget
when d0>=2. This is a limitation of the allowance, not a lower bound on the
actual list size. Separate control of the flat factors, or a sharper count
of values rather than polynomials, could still improve it.

The linear case cannot be obtained by the uniform positive-dimension argument
for this interpolation space, at any multiplicity. On the punctured domain
put N=6b-3, A=4b-1, D=mA, and restrict to total Y,R degree at most one:

```text
Q=A0(X)+B0(X)*Y+C0(X)*R.
```

The coefficient dimension is C=3mA-2w+1. In the local rank calculation there
are only h=0 and h=1 blocks. The h=0 blocks contribute m. For m=1 the h=1
block contributes one; for m>=2 its ranks are 1, then m-2 copies of 2, then
1. Consequently the exact single-node rank is L=2 for m=1 and L=3m-2
otherwise. The uniform dimension surplus is therefore

```text
C-NL = 8-6b                         when m=1,
C-NL = 6b-1-6m(b-1) <= 11-6b        when m>=2.
```

Both are negative for every b>=3. This calculation concerns the full
degree-one weighted space just specified; it does not exclude differently
chosen coefficient spaces. Nor does it show that all individual received
words have zero interpolation kernel: the combined node conditions may have
dependencies not captured by the bound N*L.

The checker verifies the block sums and both closed forms on 660 parameter
pairs and computes the exact production values. The all-multiplicity
exclusion is the elementary calculation above, not an extrapolation from
the grid. This audit is not Lean-formalized.

The subsequent [Riccati contact obstruction](astra_riccati_contact_obstruction-2026-09-05.md)
is stronger for the shape a_0(X)+a_1(X)Y+a_2(X)Y^2+d_1(X)R. Its derivative
coefficient must vanish at production for every multiplicity, regardless
of source-space restrictions or received-word-specific rank dependencies.
The local divisibility and production degree argument are Lean-checked.
This does not cover YR or R^2 terms, or a different interpolation method.

## Checks and limitations

Run `python3 scripts/probes/astra_scalar_tail_split_check.py`.
The checker covers the proper factor R-Y, the flat line XR-2Y, and the flat
power curves R^r-r^r*Y^(r-1) for r=2,3,4 over F17, F257, and the companion
prime field. It checks the next-tail remainder, regular Taylor reconstruction,
and direct polynomial solutions. It also checks truncated-exponential product
coefficients and exact companion arithmetic.

The stronger characteristic hypothesis must not be silently dropped. Over
F7, F=R-X^7 and w=2 have an identically zero next derivative. Nevertheless,
at x0=1 the reconstruction q(U)=y0+U-1 leaves
F(U,q,q')=1-U^7=-(U-1)^7, which is not zero. Its weighted degree is p, exactly
where the root-count step fails. The checker records this counterexample.

The controls do not mechanize the general truncated-exponential homomorphism,
geometric image construction, or degree-preserving projection argument.
Those written arguments and the resulting production list bound remain
unreviewed and unformalized. No improved prize inequality is claimed.
