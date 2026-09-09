# Projective sparse-combination safety, with the infinity slot retained

2026-09-08. Base HEAD `c9ec164fdcc4cb93842a03b7be0dada07ddb8e55`.
Written theorem and exact integer checks; no new Lean build or claim.

The coordinator reviewed the proof. The
[production arithmetic check](../../scripts/probes/astra_mca_projective_sparse_check.py)
reproduces the [retained count](../../scripts/probes/receipts/astra_firststep_next_20260908/projective-sparse.json).
The full projective safety instantiation is not Lean formalized.

Let `n=4s`, `k=2s`, `t=3s-1`. C is RS of polynomial degree below k on
any n distinct points over any finite field F. For a received pair (u,v),
let B be the ordinary finite MCA-bad set. Define projective badness at
`[alpha:beta]` by replacing `u+gamma*v` with `alpha*u+beta*v`, retaining
the original same-support no-joint condition.

## General projective punctured-list theorem

Suppose `(a,b)!=(0,0)` and c in C satisfy

    m = |{x : a*u(x)+b*v(x) != c(x)}| < t.

If a positive integer L satisfies

    (L+1)(t-m)^2 > (n-m)((t-m)+L(k-1)),

then the total number of projective bad slots is at most **L*m+1**.
In particular the original finite bad set has at most L*m+1 points.

Proof. Complete the nonzero row (a,b) to an invertible two-by-two matrix,
using (a,b) as its second row. The resulting second received word is
w=a*u+b*v. Subtract c, so the new direction z=w-c has support E of size m.

Invertible row mixing gives a bijection of projective coefficient slots:
`[alpha:beta]` maps to the original coefficients obtained by multiplying
the row vector `(alpha,beta)` by the mixing matrix. The decoder polynomial
is merely scaled when normalizing a nonzero projective coefficient pair.
Joint codeword pairs transform through the same invertible matrix, so
same-support joint explainability and its negation are preserved.
Subtracting a codeword from a received row also preserves the event, after
subtracting its corresponding scalar multiple from the decoder.

For any finite bad scalar in the new chart, its witness support must meet
E; otherwise (f,0) jointly explains that support. The witness decoder f
agrees with the fixed offset word on at least t-m points of D\E. The
displayed incidence inequality bounds the total fixed punctured decoder
list by L, with no assumption about regular dependence on gamma.
Each decoder fixes at most m finite scalars, by agreement at a point of E.
The finite bad count is therefore at most L*m. There is one additional
projective slot, infinity, whose contribution is at most one. Projective
invariance gives the stated bound in the original coordinates.

For m=0, every finite scalar is jointly explainable whenever it has a
decoder, so the projective bound is at most one directly.

The existing formal source `MCAProjectiveEquivariance.lean` already proves
the relevant row-mixing, codeword-translation, and projective-census laws.
This note supplies a written sparse-bound instantiation, not a new formal
instantiation of those laws.

## Production specialization

For s>=304, the prior sparse-direction arithmetic proves the displayed
condition for L=18 whenever `m<=floor(n/18)`. At the actual production n:

    floor(n/18) = 59652323,
    18*floor(n/18)+1 = 1073741815 = n-9.

Thus **any nonzero linear combination of u and v within 59,652,323
coordinates of C proves the full finite MCA bound strictly below n**.
This applies regardless of the cardinality of the high-core pair list J,
including J empty. It extends the previous hypothesis on v alone to the
entire projective received line, while paying the infinity contribution.

For an affine combination u+gamma_0*v with gamma_0 finite, an explicit
coordinate choice is `(U,V)=(v,u+gamma_0*v-c)`. Its new finite parameter
eta!=0 corresponds to old gamma `gamma_0+1/eta`; eta=0 is the old infinity,
and new infinity is old gamma_0. This exhibits exactly where the added
point can enter the old finite census.

## Necessary condition for any over-budget counterexample

If the original finite bad count is greater than n, then

    dist(a*u+b*v,C) >= 59652324

for **every** nonzero coefficient pair (a,b). In particular the two
received cosets in `F^D/C` are linearly independent.

Every ordinary bad scalar gamma still supplies a decoder within
`n-t=s+1=268435457` of u+gamma*v. Therefore any over-budget counterexample
must have all its bad projected words in the distance band

    59652324 <= dist(u+gamma*v,C) <= 268435457.

This is a necessary condition and a safety branch, not a contradiction.
It leaves a substantial dense-combination regime open. It also shows
why choosing an arbitrary existing bad scalar as pivot is insufficient:
its witness only ensures the much larger upper endpoint s+1.

## Exact dependent-coset classification

If span([u],[v]) in `F^D/C` has dimension zero, no projective slot is bad.
If that dimension is one, **exactly one projective slot is bad**, for any
support threshold t<=n.

To prove the latter, write `u=c0+a*r`, `v=c1+b*r` with codewords c0,c1,
r not in C, and `(a,b)!=(0,0)`. At a slot with alpha*a+beta*b!=0, any
decoder on S produces a codeword agreeing with r on S by subtracting
alpha*c0+beta*c1 and dividing by alpha*a+beta*b. That codeword gives a
joint explanation of (u,v) on S, so the slot is not bad. At the unique
kernel slot, the projected word is globally a codeword; the full support
D cannot have a joint explanation because r is not in C. Thus this slot
is bad. The finite census is zero or one depending on whether the kernel
slot is the omitted infinity point.

## A concrete failure of affine-census invariance

On the actual production subgroup take `r(x)=x^k`, which is not in C by
the polynomial root bound (`k<n`). For `(u,v)=(0,r)`, the finite bad set
is exactly `{0}`. After swapping the rows to `(r,0)`, the finite bad set
is empty and infinity is bad. Both have one projective bad point.

This exact actual-domain example refutes an attempted GL2 argument that
equates the two affine counts without accounting for infinity. The +1
in the general transport bound cannot simply be discarded.

## Scope of the remaining gap

This does not prove that an arbitrary J-empty line has a sparse
combination. No uniform decoder family, rational dependence on gamma,
or unproved inverse statement is assumed. Dense two-dimensional
quotient spans remain the next obstruction.
