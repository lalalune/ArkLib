# An exact single-hole reduction to a punctured RS value set

The universal predecessor bound contains a family in which **every useful
joint polynomial pair is already rationally collinear**, all triple
determinants vanish identically, and every MCA event has an explicit joint
core. The missing quantity is the number of distinct extrapolated values
of a punctured RS list. None of the joint cores covers the omitted point,
so the full-cover rational-collinearity theorem does not settle this family.

This is an exact reduction with the actual same-support no-joint condition.
It gives no new scalar-count bound or counterexample, and is not
Lean-formalized.

## Exact event equivalence

Let Omega be n distinct field elements, fix a in Omega, and let C be the
evaluations of polynomials of degree less than k. Assume
`1<=k` and `k+1<=t<=n`. For an arbitrary word v on `Omega\{a}` define

```text
u0(x)=v(x) for x!=a,  u0(a)=0,
u1(x)=0    for x!=a,  u1(a)=1.

L(v)={f : deg f<k, #{x!=a : f(x)=v(x)}>=t-1}.
```

At the radius whose integer agreement threshold is t, the exact MCA-bad
scalar set is

```text
Bad(u0,u1)={f(a) : f in L(v)}.                         (1)
```

For the forward direction, choose an actual MCA witness S and its decoding
polynomial f. If a is absent from S, `(f,0)` jointly explains `(u0,u1)` on
S, contradicting the no-joint clause. Hence a belongs to S, `f(a)=gamma`,
and f agrees with v at at least t-1 other points.

Conversely, take f in L(v), set gamma=f(a), and use its punctured agreement
set together with a as the support. A hypothetical joint explanation would
include a polynomial g of degree less than k with at least t-1>=k distinct
zeros outside a but `g(a)=1`. The root bound rules this out. Thus this is
exactly the event of
[Errors.lean](../../ArkLib/Data/CodingTheory/ProximityGap/Errors.lean),
including its no-joint requirement on the same support.

Equation (1) concerns an **evaluation image**, not necessarily the full list
size: different f may have the same f(a). Every event is attributed to the
constant polynomial pencil `(f,0)` with core

```text
A_f={x!=a : f(x)=v(x)}.
```

That pencil contributes precisely the one scalar f(a) when f belongs to
L(v). Outside a the received line is independent of gamma; any mismatch
there can never be canceled by changing gamma.

## Classification of large maximal joint cores

Every joint core of size at least k+1 excludes a. Otherwise its direction
polynomial g would have at least k zeros elsewhere but value 1 at a.
After excluding a, the same root bound forces g=0. Therefore every such
core is contained in A_f for a pair `(f,0)`.

Each A_f of size at least k+1 is itself a maximal joint core. A larger joint
core would also have direction polynomial zero, and its first polynomial
would agree with f at at least k points, forcing it to equal f. Distinct
such A_f cannot contain one another for the same reason.

When t>=k+2, the maximal cores with size at least t-1 are consequently in
bijection with L(v). All their polynomial pairs lie on the rational line

```text
(f,0)=(0,0)+f*(1,0).
```

Their primitive direction is `(1,0)` and all triple determinants are zero
before any root-divisor argument. Yet their union excludes a. In particular
the [full-cover fixed-pencil theorem](astra_mca_fixed_pencil_predecessor-2026-09-04.md)
has an unavailable hypothesis here. Rational collinearity does not bound
the number of these maximal cores. No extraction into a bounded number of
them is supplied by the determinant identity.

## The genuine rank-two case and the RS Gram constraint

The enlarged space `D=C+span(u0,u1)` has dimension k+2, equivalently
`D/C` has dimension two, exactly when v is not the
restriction of a codeword to `Omega\{a}`. Indeed, u1 is outside C because
it has n-1>=k zeros. A relation `u0 in C+span(u1)` is precisely such a
punctured codeword explanation. If L(v) contains two distinct polynomials,
v cannot have a global punctured explanation: either polynomial agrees
with that explanation at at least k points and would have to equal it.

The Gram constraint in fact holds for every half-rate RS evaluation set,
not just a smooth subgroup. Suppose n=2k, set
`P_Omega(X)=product_{x in Omega}(X-x)`, and use the nonzero weights
`lambda_x=1/P_Omega'(x)`. Lagrange interpolation, taking the coefficient
of degree n-1, gives

```text
sum_{x in Omega} lambda_x*h(x)=0       if deg h<=n-2.
```

Consequently C is self-dual for
`B_lambda(v,w)=sum_x lambda_x*v(x)*w(x)` since `deg(f*g)<=2k-2=n-2`.
For the errors `r_f=u0+f(a)*u1-f`, put

```text
s=B_lambda(u0,u0), h_f=B_lambda(u0,f), gamma_f=f(a).
```

Every r_f vanishes at a. Since `B_lambda(f,g)=0`, `B_lambda(u0,u1)=0`,
`B_lambda(u1,u1)=lambda_a`, and `B_lambda(f,u1)=lambda_a*f(a)`,
direct expansion gives

```text
B_lambda(r_f,r_g)=s-h_f-h_g-lambda_a*gamma_f*gamma_g.
```

Thus this entire family has error Gram rank at most **three**, while its
scalar count is still the evaluation image in (1). This is an exact
necessary relation, not an assertion that the image can be arbitrarily
large on the production domain. On `Omega=mu_n`, the derivative
`P_Omega'(x)=n/x` gives `n*lambda_x=x`; scaling the form by n recovers
the subgroup identity in the [rank-four Gram note](astra_mca_mds_rank_obstruction-2026-09-05.md),
with coefficient a in place of lambda_a. The rank-three constraint alone
therefore does not express additional structure specific to the smooth
subgroup.

## The remaining production statement and prior work

At the production predecessor the parameters are

```text
n=1073741824, k=536870912, t=715827884,
|Omega\{a}|=1073741823,  t-1=715827883.
```

The universal cap requires, in particular, the following statement for
every a and every punctured received word v:

```text
#{f(a) : deg f<536870912,
         #{x in Omega\{a}:f(x)=v(x)}>=715827883}
 <=1073741824.                                         (2)
```

A cap on the entire list L(v) would suffice but is stronger than (2).
This does not newly identify the general punctured-list difficulty:
[_S2PuncturedJohnsonDischarge.lean](../../ArkLib/Data/CodingTheory/ProximityGap/Frontier/_S2PuncturedJohnsonDischarge.lean)
already handles the within-Johnson part of the large-zero branch, and
[_R157PuncturedListBudgetConsumer.lean](../../ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R157PuncturedListBudgetConsumer.lean)
consumes a punctured-list budget. The production punctured parameters are
beyond that Johnson regime. The additional content here is the exact MCA
equivalence, evaluation-image target, maximal-core classification, and
rank-three identity for this single-hole subfamily.

## A bounded witness check

Over F17 take `Omega=mu_8={1,2,4,8,16,15,13,9}`, `a=1`, `k=4`, `t=6`.
Let v vanish on `{2,4,8,16,15}` and agree on `{13,9}` with

```text
f1=(X-2)*(X-4)*(X-8)=X^3+3X^2+5X+4 mod17.
```

Both f0=0 and f1 have exactly five punctured agreements, so their scalars
are `f0(1)=0` and `f1(1)=13`. Adding a gives exactly six agreements each;
the five zero conditions on any hypothetical direction explanation
contradict its required value 1 at a. The received pair has quotient rank
two, since a punctured codeword explanation would have five zeros and
would also have to equal the nonzero values on `{13,9}`.

This small example checks the definitions; it is not an over-budget
example or evidence for a production-size lower bound. The general result
is the elementary proof above, valid independently of the field size.

Run `python3 scripts/probes/astra_mca_single_hole_check.py` to reproduce the
finite check. It enumerates all 83,521 degree-less-than-four polynomials,
obtaining exactly the two listed punctured codewords. Independently, 629
scalar/support rank checks over every support of size at least six give
exactly the same MCA-bad set `{0,13}` using the original no-joint condition.
The probe also checks quotient rank two and the weighted Gram identity.

A second complete control shows that the rank-three bound is attained
by actual list candidates on a nonsubgroup evaluation set. Over F17 set

```text
Omega=(0,1,16,2,15,3,14,4), a=4, k=4, t=6,
v(1)=7, v(16)=10, v(x)=0 at the other punctured points.
```

The entire punctured list is `0`, `10X+14X^3`, `15X+9X^3`, with values
at a equal to `0,1,7`. Their error supports are respectively `{1,16}`,
`{2,15}`, `{3,14}`. The Lagrange weights in the displayed domain order
are `(15,2,8,9,3,14,2,15)`, giving the error Gram matrix
`diag(14,5,16)`, of determinant 15 modulo 17. The probe enumerates the
whole list and checks the original no-joint condition on all three
witness supports. This certifies sharpness of the Gram rank bound, not
a violation of any production scalar budget.
