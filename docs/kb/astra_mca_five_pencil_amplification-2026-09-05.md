# Five pencils give 805306374 bad scalars below the prize budget

The [five-candidate construction](astra_mca_five_candidate_lift-2026-09-05.md)
admits a polynomial-pencil amplification. At the actual production prime
and domain it supplies **805306374 distinct MCA-bad scalars** at radius

```text
335544321/1073741824 = 5/16 + 1/2^30.
```

The count comes from an injective reciprocal map on an explicitly described
subset of the domain, plus five separately checked scalars. It needs no
billion-point scan. It is a lower bound on the actual error at that radius,
not a census of all bad scalars. It remains below the security numerator
budget of 1073741824 and gives no new unsafe-radius bound.

A separate argument covers arbitrary polynomial changes to these five
pencils when sufficiently many of their original core agreements are
retained. That restricted family has at most 1014089502 bad scalars from
its five pencils, also below the budget. Different core patterns, additional
pencils, and other decoding polynomials remain outside that result.

Both results have written proofs and exact arithmetic controls. An independent
agent audit found no defect in either claim within its stated scope. They are
**not Lean-formalized or externally peer-reviewed**. The prize remains open.

## Polynomial normalization

Use the previous note's field P, generator g, and notation

```text
n=16s=2^30, s=2^26, d=2s, k=8s, w=k-1,
eta=g^s, zeta=eta^2, T=X^d,
J_d=1+X+...+X^(d-1), G=J_d*(T-zeta^2).
```

The differences between the five previous candidate polynomials and the
first one are `G*W_i(T)`, where

```text
W_0=0,
W_i(T)=(T-zeta)*(zeta^i-1)*(T-zeta^(-i)), i=1,2,3,
W_4(T)=-(T-zeta^6)*(T-zeta^7).
```

The nonzero W_i are quadratic in T. Their gcd is one: the gcd of W_1,W_2,W_3
is T-zeta, which is coprime to W_4. The exact checker verifies both these
identities and the gcd. Substitution T=X^d preserves coprimality by Bezout.
Thus the W_i(X^d) do not all vanish at any field point.

G has the `4s-1` simple roots in the two cosets T=1 and T=zeta^2, excluding
1. At either of these two values of T, W_0,W_1,W_2,W_3 are pairwise
distinct. This follows from

```text
W_i(T)-W_j(T)=(T-zeta)*(zeta^i-zeta^j)*(T-zeta^(-(i+j)))
```

for i,j in {0,1,2,3}, including W_0=0. None of the factors vanishes there.

## An explicit amplification

Remove the root -1 from G and define

```text
B(X)=G(X)/(X+1)
    =(1+X^2+...+X^(d-2))*(T-zeta^2),
p_i(X)=B(X)*W_i(T), q_i(X)=X*p_i(X).
```

Both components are code polynomials: `degree p_i<=k-2` and
`degree q_i<=k-1`. B has exactly `4s-2` domain roots, namely the two cosets
T=1 and T=zeta^2 with both 1 and -1 removed.

Let S_i be the original punctured agreement sets of the five candidates.
They have sizes `11s-1` for i<4 and `12s-1` for i=4. Remove -1 from the
first four sets and retain the fifth. At each covered point x, choose an
owner j and set

```text
(u0(x),u1(x))=(p_j(x),q_j(x)).
```

All retained owners agree with this pair. Away from -1 this follows from
the original agreement relations and the displayed normalization. At -1
only the fifth retained core is required. Every point except 1 is covered.
The five exact joint-core sizes are

```text
11s-2,11s-2,11s-2,11s-2,12s-1.
```

At a covered point outside the roots of B, the p_i values are not all
equal, since the W_i do not vanish simultaneously. Hence at least one
pencil has a nonzero residual against the received pair. All such residuals
have direction `(1,x)`, and cancel at

```text
gamma_x=-1/x.
```

These scalars are distinct for distinct x. There are exactly

```text
n-1-(4s-2)=12s+1
```

such coordinates. A core plus its extra point has at least `11s-1`
agreements. Trimming a larger core, if necessary, gives that exact support
size while keeping at least k core points. Any joint codeword explanation
would then equal the local pair on the core by the root bound, and fail at
the nonzero residual point. Thus these are actual same-support MCA events.

### Five more scalars at the hole

At 1 the five local pairs are `(v_i,v_i)`, with

```text
v_i=s*(1-zeta^2)*W_i(1).
```

Set `(u0(1),u1(1))=(0,1)`. The exact production calculation verifies that
the v_i are distinct and none is one. The five cancellation scalars are

```text
gamma_i=v_i/(1-v_i).
```

They are distinct, and the first is zero. For each of the other four,
the checker verifies `(-1/gamma_i)^n != 1`. None therefore lies in the
ordinary reciprocal image, even before removing B's roots from that image.
The residual at the hole is nonzero for every i. The same core uniqueness
argument proves the no-joint condition on each selected support.

The total number of certified distinct scalars is consequently

```text
12s+6=805306374,
event agreement=11s-1=738197503,
radius=(5s+1)/n=335544321/1073741824.
```

In particular the true worst-case error is at least `805306374/P` there.
The inequality `805306374*2^128 < P` shows that this certified set alone
does not exceed the security budget. It is not an upper bound on the true
error: other decoding polynomials may contribute further bad scalars.

## Why retaining these cores limits further amplification

This part permits arbitrary new polynomials `p_i,q_i` of degree at most w,
and an arbitrary received pair. It assumes only that p_i and q_i jointly
agree with that pair on subsets of the original S_i obtained by removing
at most

```text
l=(s-1)/3=22369621 points from each S_0,...,S_3,
m=(4s-1)/3=89478485 points from S_4.
```

These are exactly the maximum losses that leave each chosen core with at
least 715827882 points. Removed points may be anywhere and may overlap.
The assertion counts all MCA events decoded by these five pencils,
including supports with multiple additional agreements. It does not assert
that all decodings of the received line belong to these pencils.

### A small rank certificate controls all production degrees needed here

On the sixteen-point base, impose the original shared-value conditions
for the first four candidates, subtract the first polynomial, and allow
degree at most eight in each of the remaining three polynomials. There
are 25 displayed equations in 27 coefficient columns. The exact
certificate gives a nonzero minor in the first 25 columns, of determinant

```text
96848988683743615843982839670225765648960583663 mod P.
```

The kernel has dimension two. Its two explicitly checked independent
members are the original normalized seed vector v(Y) of degree seven and
Y*v(Y). Hence they span the whole degree-eight kernel.

Now take any three normalized production polynomials satisfying the
original first-four shared-value conditions, with degrees at most w+h,
where h<2s. Their common zeros include the s-1 points of the fibre of 1
other than 1, so divide by J_s. The resulting degree cap is 7s+h.
Write each polynomial uniquely as

```text
sum_(r=0..s-1) X^r*a_r(X^s).
```

Each a_r has degree at most eight. On a complete nontrivial fibre,
vanishing of a difference on its s points implies that all s coefficients
of its degree-less-than-s remainder vanish. Thus each coefficient vector
a_r satisfies the base shared-value equations. The kernel certificate
forces it to be `(alpha_r+beta_r Y)*v(Y)`. Reassembling shows that the
entire normalized production tuple is a polynomial multiple of the
original seed tuple. Its multiplier has degree at most h.

Let E be the locator of the union of the points removed from the first
four cores, of degree h<=4l<2s. Multiplying arbitrary new normalized
polynomials by E restores all those original conditions. It follows that,
for each scalar coordinate of the received pair, the first four new
polynomials differ by one common rational multiplier of the original
differences.

The fifth obeys that same multiplier. After clearing E, the difference
from the predicted fifth polynomial has degree at most `8s-1+h` and at
least `12s-1-m-h` roots. These are original fifth-core points retained by
the fifth and outside the union of the first-four removals. At every such
point an original first-four owner is still retained. The root surplus is

```text
4s-m-2h >= 4s-m-8l = 3.
```

The difference therefore vanishes. Since the W_i have gcd one, clearing
the common rational factor gives actual polynomials A0,A1 of degrees at
most `4s-1` and two base polynomials a0,a1 such that all five new pairs are

```text
(p_i,q_i)=(a0,a1)+W_i(X^d)*(A0,A1).
```

### Count the possible cancellation directions

Among the `4s-1` original roots of G, a point retaining at least two of
the first four owners forces A0=A1=0 there: those owners' W values are
different. The new received pair equals every local pair at such a point,
so it contributes no nonzero residual direction. Excluding one such point
requires at least three first-four core removals. There are therefore at
least

```text
z=4s-1-floor(4l/3)=238609294
```

covered coordinates with no nonzero residual. Every original punctured
point had at least two first-four owners. A newly uncovered point costs at
least two first-four removals, so the number of uncovered coordinates,
including the original hole, is at most

```text
u=1+2l=44739243.
```

At any covered coordinate all nonzero residual rows are scalar multiples
of `(A0(x),A1(x))`, giving at most one finite cancellation scalar. At an
uncovered coordinate there are at most five nonzero rows, giving at most
five scalars. An actual MCA event decoded by a local pencil must contain
a nonzero joint residual somewhere; otherwise that pair jointly explains
the entire witness support. Hence the total contributed by these pencils
is at most

```text
n-z+4u=1014089502 < 1073741824,
margin below budget=59652322.
```

This accounts for every possible location of the allowed removals. It
does not apply when more original agreements are lost and replaced by new
ones elsewhere, or when additional decoding pencils are introduced.

## Reproduction

```bash
python3 scripts/probes/astra_mca_five_pencil_amplification_check.py
```

The [checker](../../scripts/probes/astra_mca_five_pencil_amplification_check.py)
verifies the base minor, both kernel vectors and all required field
identities. Independent dense constructions on orders 16,64,256 over P
certify 18,54,198 distinct scalar/support witnesses respectively. An
order-64 control over F65537 certifies 54. Every finite witness includes
a parity check of the same-support no-joint condition.

Six additional order-64 removal patterns check the full 128-column source
matrix against the predicted multiplier dimension, including a common-root
removal, two newly uncovered coordinates, and three deterministic random
patterns. Their nullities are 2,1,2,1,1,1. These are independent controls;
the proof for all production removal patterns is the written rank,
descent, root-count and incidence argument above. Neither result is yet
Lean-formalized.

### Independent audit

An independent agent reviewed the mathematical argument at source commit
`ca77ac1069ae7c7f2adef6a803010f454d9f3c32`, including the exact same-support
MCA definition. It found no correctness defect. This is an agent review,
not external human peer review or an audit of literature novelty.

Run the separately implemented arithmetic audit with

```bash
python3 scripts/probes/astra_mca_five_pencil_independent_check.py
```

The [independent checker](../../scripts/probes/astra_mca_five_pencil_independent_check.py)
imports no other repository probes. It reconstructs H and the actual base
agreement sets, verifies the minor and primitive gcd, and checks the five
production hole values. Its order-16 no-joint check uses augmented
Vandermonde ranks on each exact witness support. It also checks fifteen
removal patterns, the recursive Lucas primality certificate, and the domain
generator order.

The strict descent cutoff is essential. At order 64, the first-four source
kernel has dimensions 1,2,4,8 at h=0,1,3,7, respectively. At h=8=2s its
dimension is 11, exceeding the nine polynomial multiples of the seed.
The proof above uses only h<2s and does not extend across this boundary.
