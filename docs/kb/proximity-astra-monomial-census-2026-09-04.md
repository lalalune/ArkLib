# Order-eight monomial MCA census: an exact field-uniform certificate

Date: 2026-09-04. Base: `54007b004` on the local Proximity Prize research checkout.

The threshold-four maximum over the 64 order-eight monomial pencils is **exactly nine
in every field of characteristic different from two containing an eighth root of exact
order eight**. The four maximizing exponent pairs are `(4,3)`, `(4,7)`, `(5,2)`, and
`(5,6)`. There is no exceptional odd characteristic for this monomial census.

This improves the G328/G330 state from finite-prime observations of the below-ceiling
monomial profile to a field-uniform arithmetic certificate. It is a mathematical
argument backed by an exhaustive exact Python certificate, **not a Lean-checked theorem**.
The production Proximity Prize problem remains open. The restriction to monomial pencils
is essential; this result does not bound arbitrary received-word pencils or the full
MCA supremum.

## Precise statement

Let `F` be a field with `char F != 2`, let `g^4 = -1`, and put
`G = {1,g,...,g^7}`. These eight elements are distinct. For `a,b` in `{0,...,7}`,
define `Gamma(a,b)` to be the scalars `gamma` for which some subset `S` of `G`, with
`|S| >= 4`, and some affine polynomial `ell` satisfy:

1. `x^a + gamma*x^b = ell(x)` at every `x` in `S`;
2. the two words `x^a` and `x^b` are **not both** restrictions of affine polynomials
   on that same set `S`.

The second clause is the MCA joint-agreement exclusion. Omitting it changes the event,
especially for exponents zero and one.

The entire matrix `|Gamma(a,b)|`, with rows indexed by `a` and columns by `b`, is:

| a \\ b | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 0 | 0 | 0 | 1 | 1 | 1 | 1 | 1 | 1 |
| 1 | 0 | 0 | 1 | 1 | 1 | 1 | 1 | 1 |
| 2 | 0 | 0 | 1 | 0 | 4 | 8 | 4 | 0 |
| 3 | 0 | 0 | 0 | 1 | 8 | 4 | 0 | 4 |
| 4 | 0 | 0 | 5 | 9 | 1 | 8 | 5 | 9 |
| 5 | 0 | 0 | 9 | 5 | 8 | 1 | 9 | 5 |
| 6 | 0 | 0 | 4 | 0 | 4 | 8 | 1 | 0 |
| 7 | 0 | 0 | 0 | 4 | 8 | 4 | 0 | 1 |

In particular, this covers every prime `p = 1 mod 8`, including `p=17`. G330's
exception at `17` concerns the **different, threshold-three ceiling spectrum**;
it does not extend to this threshold-four monomial profile.

## Completeness of the four-point reduction

Suppose a scalar has a witness `S` with `|S| >= 4`. On `S`, the combination is affine.
If `x^b` were affine there, subtracting `gamma*x^b` would make `x^a` affine too,
contradicting the joint-exclusion clause. Thus `x^b` is nonaffine on `S`.

Choose two distinct points of `S` and their unique affine interpolant for `x^b`.
Some third point of `S` violates this interpolant. Enlarge these three points by
one more point of `S`. The resulting four-point set `T` still witnesses agreement
of the combination and nonaffineness of `x^b`. Conversely, any such four-point
witness is itself a valid witness. It therefore suffices, without losing any
scalar, to enumerate the `C(8,4)=70` four-point supports.

For a support `T`, write

```text
H_T(X) = product_(x in T) (X-x),
X^a mod H_T = r_a,0 + r_a,1 X + r_a,2 X^2 + r_a,3 X^3,
v_a = (r_a,2, r_a,3).
```

Monic division uses no denominators. Agreement with an affine polynomial on the
four distinct roots of `H_T` is equivalent to `v_a + gamma*v_b = 0`: the difference
between the degree-at-most-three remainder and an affine polynomial cannot have
four roots unless it vanishes. Nonaffineness of `x^b` is exactly `v_b != (0,0)`.

Consequently:

* if `v_b = 0`, this support produces no MCA scalar;
* if `det(v_a,v_b) != 0`, it produces no scalar;
* otherwise, choose a nonzero coordinate `d` of `v_b`; the unique scalar is
  `gamma = -v_a[i]/d`.

This treats existence and the exclusion clause together. It does not assume
that a largest agreement set is the relevant witness.

## Why the finite certificate applies to every field

Perform the entire enumeration in

```text
R = Z[z] / (z^4 + 1),
```

representing each element by its four integer coefficients. Reduction modulo a
monic polynomial makes this a free abelian group of rank four. The certificate
computes the determinant `N(c)` of multiplication by each relevant element `c`.
Independently, it computes the same norm through G330's two antipodal-squaring
identities and checks exact equality of the two methods.

Every norm needed to preserve the census is a power of two:

| Elements checked | Complete observed set of nonzero absolute norms |
|---|---|
| Differences of distinct domain roots | `{2,4,16}` |
| Nonzero proportionality determinants | `{1,2,4,8,16}` |
| Chosen nonzero candidate denominators | `{1,2,4,8,16}` |
| Nonzero candidate cross-products used during deduplication | `{4,8,16,64,128,256,1024}` |

For any field in the statement, the homomorphism `R -> F`, `z -> g`, is defined.
An element whose multiplication determinant is `+/-2^k` becomes a unit after
inverting two, by the adjugate matrix identity. Its image in `F` is therefore
nonzero. Equivalently, G330's explicit norm factorization shows that a zero image
would force `2^k = 0` in `F`, which is impossible.

Thus every nonzero determinant remains nonzero, every chosen denominator remains
invertible, and every pair of distinct scalar candidates remains distinct. Zero
coordinate vectors, zero determinants, and equal-candidate cross-products are
literal identities in `R`, so they stay zero under every specialization. Each
support retains its exact contribution, and deduplicating contributions from
different supports retains exactly the same equivalence classes in every field.
This proves the displayed matrix from the exhaustive finite arithmetic certificate.

There are no untreated exceptional odd primes: the complete bad-prime candidate
set from these norms is `{2}`, excluded by the theorem's hypothesis. In particular,
the argument does not use a finite prime-search cutoff or a heuristic about
sufficiently large characteristic.

## Reproduction and independent checks

Run:

```sh
python3 scripts/probes/astra_order_eight_monomial_certificate.py
```

The probe uses only the Python standard library. It checks all 70 supports and
64 pencils, verifies polynomial remainders by independent evaluation on their
four roots, compares two norm implementations, and emits the full matrix and
norm sets. It finds 154 distinct scalar labels in total across the 64 pencils.

Independent verification evaluates the original MCA event directly for **every
scalar** at `p=17,41,73`, constructing affine witnesses from all pairs of points.
This routine uses neither cyclotomic remainders nor the symbolic candidate
enumeration and agrees with every entry of the matrix. The existing
`g328_k2_field_stability_boundary.scan_prime` implementation also agrees at
`p=17,41,257,1009`, including its ceiling count and maximizing exponent pairs.

The universal conclusion rests on the norm certificate and specialization
argument. These finite-field comparisons are additional implementation checks.
The exact probe passed on 2026-09-04. Lean compilation and a kernel axiom audit
were not performed for this new result; it is ready for a future Lean port of
the finite remainder/candidate certificate and the four-point MCA bridge.

## Relation to the prize

This removes one explicit finite-family residual left in the G330 log: the
field-uniform below-ceiling monomial census. It does not assert an upper bound
for arbitrary pencils, larger subgroup orders, production `n=2^30`, or the
signed Newton/BGK estimates. It therefore does not close the Proximity Prize.
