# Preserving a scalar list budget under arbitrary interleaving

A large-field separation argument transfers a **uniform scalar list bound B**
to the same bound for every positive interleaving arity, at the same radius,
provided `binomial(B+1,2)<=q`. Both fixed field/budget profiles used in this
campaign satisfy this condition. This removes an interleaving loss from that
conditional implication; the transfer itself supplies no scalar bound.
The subsequent [fixed-word differential carrier note](astra_scalar_differential_carrier-2026-09-05.md)
gives a written scalar estimate at the companion radius 80791/262144,
with independent review and Lean formalization still outstanding. Neither
argument identifies the MCA bad set with a decoding list.

This note gives an elementary written proof and reproducible finite checks.
A [general Lean candidate](../../scripts/probes/astra_exact_list_projection.lean)
now states the exact list-budget equivalence at integer agreement thresholds;
its compiler and axiom checks are pending in the two-version auxiliary-proof
CI workflow. It is not yet a verified Lean theorem or a novelty claim.
The general interleaving literature is
reviewed in [ABF26, Definition 2.9 and Lemma 2.10](https://eprint.iacr.org/2026/680).
The in-tree [product bound](../../ArkLib/Data/CodingTheory/InterleavedListSize.lean)
applies without linearity and transfers B to B^m; the argument here uses
linearity and the explicit field-size condition to preserve B exactly.

## A projection separating a finite family

Let K be a field of q elements, let W be a finite-dimensional K-vector space,
and let `v_1,...,v_M` be distinct elements of `W^m`, with `m>=1` and `M>=2`.
For `lambda in K^m` put

```text
pi_lambda(v)=sum_j lambda_j*v_j in W.
```

For each pair of distinct family members a,b, collision is the kernel of the
nonzero linear map

```text
lambda -> sum_j lambda_j*(v_{a,j}-v_{b,j}).
```

If its rank is r_ab, the kernel has `q^(m-r_ab)` elements, and `r_ab>=1`.
All these kernels contain zero. With `h=binomial(M,2)`, their union therefore
has cardinality at most

```text
1+sum_{a<b}(q^(m-r_ab)-1)
 <=1+h*(q^(m-1)-1).
```

When `h<=q`, this is at most `q^m-q+1<q^m`. Consequently a lambda outside
the union exists and its projection is injective on the family. This includes
the equality case `h=q` and the case `m=1`. No random sampling or probability
of computational success is needed. The rank-sensitive sum can also certify
separation when the coarse condition fails.

The proper-subspace covering fact is already proved by
`ProximityGap.exists_nonzero_notMem_of_proper_family` in
[InterleavingStabilityMCA.lean](../../ArkLib/Data/CodingTheory/ProximityGap/InterleavingStabilityMCA.lean).
Its field-indexed family can contain these at most q collision kernels,
with remaining entries set to the zero subspace. The new application to
list-candidate collisions and its complete library assembly have not been
Lean-checked here; citing that existing lemma does not certify the assembly.

The condition cannot simply be dropped from this **separation lemma**. The
four points `(0,0),(1,0),(0,1),(2,2)` in F5^2 determine all six projective
directions; every scalar linear projection collides on a pair. This is a
control on the projection method, not an interleaved-list counterexample.

## Exact transfer of the numerical list budget

Let C be a K-linear code in K^n. Write L_1(delta) for its maximum scalar
list size and L_m(delta) for the maximum m-interleaved list size, with the
usual Hamming metric on rows: a row agrees when all m symbols agree.
For every integer `B>=1` with `binomial(B+1,2)<=q`,

```text
L_1(delta)<=B  if and only if  L_m(delta)<=B,    m>=1.       (1)
```

To prove the forward implication, suppose an interleaved received word U has
B+1 distinct nearby codeword tuples. Apply the separation lemma with
`W=K^n` and M=B+1. Each projected tuple belongs to C by linearity. At every
coordinate where the tuple agrees with U, its projection agrees with
`pi_lambda(U)`. Thus each projected scalar word is within the same radius.
The projection gives B+1 distinct scalar list members, a contradiction.
Different tuple candidates may have different agreement supports; no common
support across the list was assumed.

Conversely, embed any scalar received word and its list by repeating their
column m times. This preserves Hamming distance and gives an injection into
the interleaved list. This proves the reverse implication without a field-size
condition. The statement concerns a **uniform bound over all received words**;
a bound for one chosen scalar received word does not suffice.

As a separate quantitative estimate, if `1<=B<q` and `L_1(delta)<=B`, then

```text
L_m(delta)<=floor(B*(q-1)/(q-B)).                          (2)
```

Indeed, for an interleaved list of size M, every projection has at most B
image values. If its nonempty fiber sizes are s_i, Cauchy--Schwarz gives at
least `(M^2/B-M)/2` colliding unordered pairs. Averaging over all q^m
projections gives at most `binomial(M,2)/q`, by the collision-kernel count.
For M>0, comparison rearranges to `M*(q-B)<=B*(q-1)`; M=0 is immediate.
The B+1-subfamily proof of (1) has a better field-size gate for preserving
the exact integer B than rounding (2) alone.

## The same implication for a linear observable

The separating argument also applies to a fixed linear map `ell:C->W0`,
where W0 is a K-vector space. If every scalar received word has at most B
distinct ell-values among its nearby codewords, then every interleaved
received word has at most B distinct tuples `(ell(c_1),...,ell(c_m))` among
its nearby tuple-codewords, under the same field-size gate. Choose one
candidate per distinct observable tuple, separate these tuples in the
finite-dimensional space W=ell(C), and use

```text
ell(pi_lambda(c))=sum_j lambda_j*ell(c_j).
```

The projected observable values are distinct and still belong to one scalar
list's observable image. The diagonal converse again preserves values.

For a punctured RS code with at least k nodes, the extrapolation
`ell(f)=f(a)` is well-defined and linear on codewords. Consequently a uniform
single-hole value bound transfers at the **value level**, without upgrading
it to a bound on the number of polynomials. This keeps that weaker research
target separate from the full scalar list bound in (1).

## What this establishes at the two fixed profiles

For the grand-challenge production instance,

```text
P=365375409332725729550921208179070755120141565953,
B=floor(P/2^128)=1073741824,
binomial(B+1,2)=576460752840294400 < P.
```

For the companion instance,

```text
p=2130706433, q=p^6,
B=floor(q/2^128)=274980728111395087,
binomial(B+1,2)<q.
```

At either fixed profile and any fixed radius, a uniform scalar list bound
at this budget is equivalent to the same interleaved list bound for **every
positive m**. In particular no loss to B^8 is necessary for this implication
at the companion field. No scalar-list estimate or protocol soundness claim
is supplied by (1).

For Reed--Solomon codes this statement is rate-independent, so it applies to
all four requested rates on either fixed field, while leaving their scalar
thresholds unknown. It is not a uniform claim over arbitrary field sizes
with B=floor(q/2^128): that B itself grows with q and the separation gate can
eventually fail. Nor may q be replaced by the extension-field cardinality
when projecting only with coefficients from the prime subfield; the proof
uses the field over which the code is linear and the projections range.

The [single-hole value bound](astra_mca_exact_error_eliminant-2026-09-05.md)
is weaker than a scalar list-size bound, because different polynomials can
have the same omitted-point value. Proving only that value bound would not
activate (1); it would activate the observable version above. The new
capacity paper's inapplicable finite parameters and
oversized scalar certificate also remain as recorded in the
[finite audit](astra_capacity_finite_gates-2026-09-05.md).

## Reproduction

Run `python3 scripts/probes/astra_interleaved_projection_check.py`.
The checker verifies the two production arithmetic gates, collision-kernel
counts and separating projections over prime and extension fields, and
scalar/interleaved worst-case list maxima in bounded linear-code examples.
It includes the equality-gate case q=3,B=2 and a small-field control: the full
length-two code over F2 has scalar list size 3 at radius 1/2, whereas its
two-interleaved code has list size 7. That control fails the field gate.
A separate repetition-plus-free-coordinate code has full list maxima 3 and
9 over F3, but its decoded repetition value is unique at both arities,
checking the distinction between full lists and observable images.
No production list or field is enumerated.

The Lean candidate covers avoidance of at most q proper subspaces, separation
of a finite family using unordered collision pairs, monotonicity of agreement
under projection, both directions of the budget equivalence, and the three
field-size gates used here and in the scalar differential-carrier note.
It imports Mathlib alone and does not claim the scalar production bound or
an MCA reduction. CI compiles it against both repository pins and audits nine
explicit axiom reports, in addition to the existing auxiliary checks.
