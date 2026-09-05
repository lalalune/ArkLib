# Riccati contact forces the derivative coefficient to vanish

A Riccati relation would give a useful bound on the entire production
scalar list, without fixing outside factors. But the current contact
interpolation cannot supply a genuine Riccati equation at these parameters:
its derivative coefficient is forced to be zero for **every positive
multiplicity**, independently of the received word or coefficient choices.

The polynomial divisibility obstruction and the all-multiplicity production
arithmetic are now checked in
[Lean](../../scripts/probes/astra_riccati_contact_obstruction.lean). This is
stronger than a negative dimension surplus for a particular source basis.
It does not exclude equations containing YR or R^2, a different interpolation
construction, or a Riccati relation obtained by another argument. The
universal MCA lower bound remains open.

## Why the Riccati shape was worth testing

Suppose a nonzero relation

```text
a_0(X)+a_1(X)f(X)+a_2(X)f(X)^2+d_1(X)f'(X)=0           (1)
```

holds for every member of a fixed received word's list. Assume deg f<=w
and characteristic zero or characteristic p>2w. The classical cross-ratio
method for Riccati equations is discussed in
[Gasull, Torregrosa and Zhang](https://arxiv.org/abs/1602.03503); their stated
polynomial-solution theorem is over the real or complex numbers and is not
being imported as a finite-field theorem here. The following is a
self-contained written argument for a sufficient bounded-degree allowance.

If d_1=0, the nonzero quadratic in Y has at most two roots in K(X), so the
whole list has at most two members. Otherwise (1) is a Riccati equation over
K(X). Differences of solutions satisfy a first-order linear equation;
differentiating their cross ratio shows that it has derivative zero. Its
numerator and denominator have degree at most 2w. In characteristic p>2w,
such a rational function with zero derivative is constant in K: after
reducing to coprime numerator and denominator, each divides its own
derivative, so both derivatives vanish; the degree cap then forces both
polynomials to be constant. Thus the usual constant-parameter formula is
valid for the bounded-degree solutions in this finite characteristic too.

If at least three distinct polynomial solutions exist, choose f_0,f_1,f_2
and write

```text
f_1-f_0=H*u,        f_2-f_0=H*v,        gcd(u,v)=1.
```

All other solutions have the form

```text
f_t=f_0+H*u*v/(v+t*(u-v)),       t in K,
f_infinity=f_0.                                         (2)
```

Only parameters with a nonzero denominator polynomial are used.

If u and v are constant, these solutions belong to one affine polynomial
pencil. For N nodes and A>w agreements, its list has at most
(N-w)/(A-w) members, by counting the nodes where the pencil is constant
and the nodes where at most one parameter can agree.

Otherwise put h=deg H and r=max(deg u,deg v)>=1. The finite-parameter
denominators in (2) are nonzero and pairwise coprime. Each one corresponding
to a polynomial solution divides Huv. At most one has degree below r.
For L distinct polynomial solutions including f_infinity, their denominator
degrees therefore give

```text
(L-2)*r <= deg(Huv) <= h+2r,
h+r <= w,
L <= h/r+4 <= w+3.                                      (3)
```

This argument bounds any finite subset and hence the whole solution set
when it is not an affine pencil. At the production punctured parameters

```text
N=1073741823, w=536870911, A=715827883,
(N-w)/(A-w)=3-4/178956972 <3,
w+3=536870914 <1073741824.
```

Thus a nonzero common relation of shape (1) would suffice for the necessary
single-hole value budget. This counting argument is written, not
Lean-formalized or independently reviewed. No such relation for every
production received word is constructed below.

## Extracting the forced root multiplicity

Consider exactly the Riccati source

```text
Q(X,Y,R)=a_0(X)+a_1(X)Y+a_2(X)Y^2+d_1(X)R,
weighted_degree_(1,w,w-1)(Q)<mA,
```

with the existing
[contact substitution](astra_scalar_differential_carrier-2026-09-05.md)
at every node x with received value v:

```text
X=x+t,        Y=v+tR+z,        weight(t,z,R)=(1,2,0).
```

All terms of contact weight below m are required to vanish. Put
E_x(X)=a_1(X)+2v*a_2(X). The exact expansion separates the relevant terms:

```text
Q(x+t,v+tR+z,R)
 = (a_0+v*a_1+v^2*a_2)(x+t)
   + R*(d_1(x+t)+t*E_x(x+t))
   + R^2*t^2*a_2(x+t)
   + z*E_x(x+t) + 2Rzt*a_2(x+t) + z^2*a_2(x+t).
```

The pure-R coefficient has t-order at least m. The pure-z coefficient
has t-order at least max(m-2,0). In unshifted polynomial notation these
necessary conditions are

```text
(X-x)^m divides d_1+(X-x)*E_x,
(X-x)^(m-2) divides E_x,                                (4)
```

where a negative exponent is truncated to zero. For m>=2, subtracting
(X-x)E_x from the first expression proves that (X-x)^(m-1) divides d_1.
For m=1 the pure-R constant coefficient gives d_1(x)=0. Consequently, if
Z is the monic locator of all N nodes,

```text
Z^q divides d_1,       q=max(1,m-1).                    (5)
```

The factors X-x are pairwise coprime, so (5) follows from the individual
divisibilities. A nonzero d_1 must therefore have degree at least Nq.
The weighted cap, on the other hand, gives

```text
deg d_1 <= mA-w.                                        (6)
```

## The all-multiplicity contradiction

For N=6b-3, w=3b-2 and A=4b-1 the gap between (5) and (6) is

```text
N*max(1,m-1)-(mA-w)
 = 5b-4                         if m=1,
 = 2m(b-1)-3b+1 >= b-3          if m>=2.
```

Both are strictly positive for b>=4. At production b=178956971, the gaps
at m=1 and m=2 are 894784851 and 178956968. The latter increases by
357913940 for each subsequent m. Thus d_1=0 for every positive m.

This conclusion applies to every coefficient tuple obeying the weighted
cap and contact conditions, including received-word-specific kernels and
arbitrarily chosen subspaces of this four-term shape. It does not merely
say that a dimension estimate fails to guarantee a kernel.

The [three-member construction](astra_mca_moment_rigidity-2026-09-05.md)
provides a production received word with three distinct list candidates.
The usual contact/root-count argument makes all three solutions of Q.
After d_1=0, a quadratic in Y over K(X) vanishing at these three distinct
polynomials has a_0=a_1=a_2=0. Hence that word has no nonzero contact
interpolator of Riccati shape at any multiplicity. The three-candidate
existence construction is sufficient here; its entire-list classification
is not needed for this obstruction.

## Lean scope and finite boundary checks

All eight named reports in
[`astra_riccati_contact_obstruction.lean`](../../scripts/probes/astra_riccati_contact_obstruction.lean)
pass local Lean 4.30.0-rc2 and both CI pins without diagnostics, using only
propext, Classical.choice and Quot.sound. They cover the exact expansion, the local
divisibility implication, the product divisor and its degree, the production
gap for every positive m, the vanishing derivative coefficient, and the
zero quadratic conclusion from three distinct polynomial solutions.

The main theorem `production_riccati_zero_of_three` states the extracted
conditions (4) and the three polynomial solution identities explicitly.
It does not conceal contact extraction or the root-count implication in a
new axiom. The multivariate contact formalism and the general Riccati
counting argument (3) are not formalized by these eight reports. The
[construction helper](../../scripts/check-mca-production-basis.sh) and
[CI axiom audit](../../.github/workflows/proximity-strip-proof.yml) now
include the module on both toolchain pins.

Both jobs succeeded in
[run 33995562671](https://github.com/lalalune/ArkLib/actions/runs/33995562671)
at `4b72b913f05999c078ce0071d41d390464e7a6da`. The ArkLib job used Lean
4.30.0-rc2 and accepted all 126 required axiom reports; the companion job
used Lean 4.32.2 and accepted its 104 reports. Both totals include these
eight new obstruction statements. They retain the separate status of the
earlier upper-bound construction and do not prove a universal lower bound.

Run `python3 scripts/probes/astra_riccati_contact_check.py` for two exact
boundary controls and the integer arithmetic checks:

- At b=3, n=16 and m=2 over the production prime, the three-candidate
  received word has a 61-column contact space of rank 60. Its one-dimensional
  kernel has a nonzero derivative coefficient equal, after scaling, to the
  degree-15 punctured domain locator. Its weighted degree contribution is
  21, strictly below mA=22. The checker constructs the kernel by elimination,
  checks all 60 local equations separately, and verifies all three polynomial
  solution identities. This shows why the b>=4 condition cannot be omitted.
- At b=4 over F97, using 21 nodes and the received word x^2, the m=2 space
  has 81 columns, rank 71 and a ten-dimensional kernel. Every kernel basis
  vector has zero derivative coefficient. Nonzero algebraic kernels still
  exist; the theorem does not claim that all sources vanish for all words.

The arithmetic checker covers 504 small pairs (b,m) and the exact production
constants. The all-multiplicity production conclusion uses the Lean theorem,
not extrapolation from those pairs. This rules out the specified contact
route to (1), while terms involving YR, R^2 or other constructions remain
outside the obstruction. No prize threshold has been improved.
