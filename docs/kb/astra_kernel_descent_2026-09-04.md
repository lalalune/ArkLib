# Universal factors: repair and descent inside the actual kernel

A positive-R factor cannot divide every polynomial in a nonzero full contact
kernel if its lost contacts can be repaired without exceeding that factor's
weighted and residual degrees. This compares the actual kernel with itself and
does not need separate estimates for source and quotient dimensions.

In particular, **a factor of contact order zero at every node cannot be
universal on a nonzero full source kernel**. The earlier
[colon/Hermite upper bound](astra_colon_2026-09-04.md) failed numerically in that
case; the stronger descent argument here excludes the case outright once full
universal divisibility is assumed. It therefore excludes the previously
constructed monic-R geometry witness as a universal source factor. It does not
exclude every factor with the binding degree flag or prove an improved score.

All source references use companion commit
[`032154395c51fd6f77715a7f42d9a987ab9fb48a`](https://github.com/proximity-prize/proximity-prize/commit/032154395c51fd6f77715a7f42d9a987ab9fb48a).
The statements below have mathematical proofs and reproducible arithmetic
checks; their companion Lean integration remains open.

## Repair/descent lemma

Let V be the nonzero vector space of **all** polynomials satisfying the given
nodewise order-m contacts and the source flag-box inequalities

```text
contactWeight(Q) < D,      weights (X,Y,R,Z)=(1,w,w-1,0),
residualTotal(Q) <= L,     weights (X,Y,R,Z)=(0,1,1,1),
degree_R(Q) <= S.
```

Suppose nonzero F divides every Q in V, with `r=degree_R(F)>0`, contact weight
c, residual total t, and nodewise contact orders `nu_i`. Set
`b_i=min(m,nu_i)`. If there exists a nonzero **R-free** polynomial P with

```text
contactOrder_i(P) >= b_i  for every i,
contactWeight(P) <= c,
residualTotal(P) <= t,
```

then these assumptions contradict each other.

Indeed, choose nonzero Q in V with minimum R degree. Write Q=F Q'. The existing
contact-colon identity gives `contactOrder_i(Q') >= max(0,m-nu_i)`. Thus P Q'
retains order m at every node. Additivity of the maximum weighted degree of a
nonzero product gives

```text
contactWeight(P Q') <= contactWeight(Q),
residualTotal(P Q') <= residualTotal(Q),
degree_R(P Q') = degree_R(Q)-r < degree_R(Q).
```

Therefore nonzero P Q' lies in V, contradicting the chosen minimum. The proof
does not require F to be irreducible or the characteristic to exceed its degree.
If a kernel has further independent support restrictions, preserving those
restrictions is an additional premise; the displayed box is the actual
`globalCoefficientBox` used by the full source.

Taking `P=1` proves the all-order-zero assertion. More generally, let

```text
P(X) = product_i (X-x_i)^b_i.
```

This has residual total zero and contact weight `sum_i b_i`. Its contact order
at node i is at least b_i. Hence any universal positive-R factor necessarily
satisfies

```text
sum_i min(m,nu_i) > contactWeight(F).                       (1)
```

This strict inequality is a necessary condition; it is not sufficient for
universality.

## A characteristic-free local order bound

If `X-x_i` does not divide F, and F has joint YR degree at most y and R degree
at most r, then

```text
nu_i(F) <= y+r.                                           (2)
```

Here is a proof that accounts for cancellation in the local substitution.
Write `t=X-x_i`, `A=Y-u0_i-Z*u1_i`, and work over the coefficient field K(Z).
Split F into homogeneous components of total degree d in (A,R). Translation
does not increase y or r. For one component, put `s=min(r,d)` and write

```text
F_d = sum_{j=0..s} C_j(t) A^(d-j) R^j.
```

After `A=v+Rt`, the coefficient of `v^b R^(d-b)` is

```text
t^(d-b) * sum_{j=0..s} binom(d-j,b) C_j(t)t^(-j).
```

If its minimum contact weight exceeds d+s, then for `b=0,...,s` the Laurent
polynomial sum on the right is divisible by t. The square matrix
`M[b,j]=binom(d-j,b)` has determinant `(-1)^(s*(s+1)/2)`. To see this over the
integers, evaluate the binomial polynomial basis of degrees 0,...,s at the
consecutive points d,d-1,...,d-s: the Vandermonde product cancels the product
of factorial leading denominators, leaving the displayed sign. Thus M has an
integer inverse and remains invertible in every characteristic. All
`C_j(t)t^(-j)` are divisible by t, so all C_j are divisible by t.

Different components d have different total (v,R) degrees after localization,
so they cannot cancel. Since F is not divisible by t, some component is not
divisible by t, and has order at most `d+s<=y+r`. This proves (2).
The bound is sharp: `(A-Rt)^r A^(y-r)` has order y+r when `0<=r<=y`.
For an irreducible positive-R factor, `X-x_i` cannot divide F, so (2) applies
at every node. The argument also works over K[Z] by the same integer inverse;
passing to K(Z) only simplifies the notation.

## R-free interpolation supplies another repair

For an R-free polynomial, the contact order under `A=Rt+v` equals its ordinary
minimum total degree in (t,A). Indeed, an initial term `t^a A^b` contributes
`t^(a+b)R^b`; distinct b cannot cancel this coefficient. Thus the needed repairs
can be found using ordinary two-variable multiplicity conditions, with Z free.

The R-free box with contact weight at most c and residual total at most t has
dimension

```text
C0(c,t) = sum_{h=0..min(t,floor(c/w))} (t+1-h)*(c+1-w*h).
```

At a single node, imposing contact order b has rank at most

```text
rho(b,t) = sum_{h=0..min(b-1,t)} (b-h)*(t+1-h).
```

For each `tLocal^a A^h` coefficient with `a+h<b`, the remaining Z degree is at
most t-h: translating `Y=A+u0+Zu1` preserves this bound. Counting these rows
proves the rank bound. When `b<=t+1`, this simplifies to

```text
rho(b,t) = b*(b+1)*(t+1)/2 - b*(b-1)*(b+1)/6.
```

If `C0(c,t)>sum_i rho(b_i,t)`, rank-nullity produces a nonzero repair P with
exactly the caps required by the descent lemma. Consequently universality
requires the additional profile inequality

```text
C0(c,t) <= sum_i rho(min(m,nu_i),t).                       (3)
```

This use of a rank upper bound is legitimate: it constructs a repair, after
which the same-kernel descent supplies the contradiction. It does not try to
upper-bound a quotient kernel with a rank upper bound.

## Consequences at the binding flag

For the exact factor degrees `(total,YS,R)=(2364,47,10)`, use
`w=131071`, `n=262144`, and a full source multiplicity at least 57. Irreducibility
gives `nu_i<=57`, so no clipping by m is needed. The degree lower bound
`c>=w*47-10=6160327` uses **joint degree at least 47** and **R degree at most 10**;
support upper bounds alone would not justify it.

The exact consequences of (1)--(3) are:

| Necessary condition for a universal factor | Value |
|---|---:|
| Sum of node contact orders | at least 6160328 |
| Nodes with positive contact order | at least 108076 |
| R-free repair dimension at the conservative c | 347392733438 |
| Rank per node at order 33 | 1320781 |
| Uniform order-33 repair nullity lower bound | 1157918974 |
| Rank per node at maximum order 57 | 3878489 |
| Nodes with contact order at least 34 | at least 453 |

The last row follows because replacing an order-at-most-33 node by an
order-at-most-57 node increases the rank bound by at most 2557708. At most 452
such replacements cannot cover the nullity deficit. These use the conservative
c; a larger actual contact weight strengthens the necessary inequalities.

This is a real restriction on a universal factor's provenance, not an observed
contradiction for all binding factors. The arithmetic profile `nu_i=34` at all
n nodes passes both necessary tests at the conservative c. That profile is
not a constructed polynomial or a far-word/large-family witness. Excluding
such profiles requires additional information about the received words and
their regular families, or a stronger repair construction.

## Exact source insertion point and limitation

The [derivative-repair follow-up](astra_incidence_derivative_repair-2026-09-04.md)
permits a repair with smaller positive R degree and raises the positive-contact
node minimum from 108076 to 131071. It also derives the regular-solution
agreement-incidence bound. These stronger necessary conditions still admit
the uniform order-34 arithmetic profile.

The [lower-R interpolation repair](astra_kernel_lowr_2026-09-04.md) separately
raises the necessary count of nodes with order at least 34 from 453 to 6009.
It also leaves that uniform arithmetic profile unexcluded.

The official predicate is polynomial divisibility in `P4`, not merely the
presence of a component over an algebraic closure. In
[`PackedLocatorTail.lean`](https://github.com/proximity-prize/proximity-prize/blob/032154395c51fd6f77715a7f42d9a987ab9fb48a/ProximityPrize/SubmissionLower/PackedLocatorTail.lean#L21561),
`LocatorFixedBridge.mem_initialAUniversalFactors` says literally that F divides
the reconstruction of **every** element of `LocatorCaps.AKernel`. The
`common_divides_TCap` and `common_divides_B` fields and
`LocatorCaps.full_divisor_mem_box` likewise concern full source kernels.
The existing `LocatorContact.mem_kernel_iff_contactAtLeast`, contact-colon
identity, and quotient degree lemmas provide the main formal interfaces.

A safe use is to prove the contrapositive repair criterion before an initial
full-source universal/nonuniversal split. A factor failing the necessary
profile inequalities then belongs on the nonuniversal side, where
`exists_avoiding_nonuniversal_factors` can select a source vector avoiding it.

However, the generic
[`universalFactors`](https://github.com/proximity-prize/proximity-prize/blob/032154395c51fd6f77715a7f42d9a987ab9fb48a/ProximityPrize/SubmissionLower/PackedLocatorTail.lean#L5790)
is defined for an arbitrary **current** linear-map domain. In later phases
that domain can be a subspace obtained by projection. The replacement `P Q/F`
need not remain in that subspace. The descent lemma must not be applied there
without a separate stability proof. No phase recurrence or numerical score
has been changed by this investigation.

## Reproduction

Run `python3 scripts/probes/astra_kernel_descent.py` from the repository root.
The probe checks the exact thresholds, matches the R-free rank and coefficient
counts to existing independent formulas, verifies 473 integer binomial-matrix
determinants, and checks 24 small local contact matrices over F2 and F5 by
direct substitution and Gaussian rank. Those finite checks validate
transcription; the general statements rest on the proofs above. There is no
claim that small-field behavior proves the production theorem, and no Lean
kernel or protocol certificate is generated by this Python script.
