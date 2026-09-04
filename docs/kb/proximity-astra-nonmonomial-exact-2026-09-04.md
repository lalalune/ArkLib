# Exact census of the explicit nonmonomial order-eight pencil

Date: 2026-09-04. This extends the explicit ten-scalar construction with a
complete census for every prime `p = 1 mod 8` and every order-eight generator.
The conclusion is backed by exact integer and finite-field certificates; it
has not been ported to Lean.

The construction has **exactly ten** threshold-four MCA bad scalars for every
prime `p > 641`, `p = 1 mod 8`, for every choice of order-eight generator.
There are six exceptional characteristics, completely classified below.
Two admit **eleven** bad scalars for some generators. These are counts for
this particular pencil, not an upper bound for arbitrary pencils.

## Construction and exact result

For `g^4 = -1` in `F_p`, put

```text
A = {g,g^2,g^3}, B = {g^5,g^6,g^7}, C = {1,-1}.
```

Define received words on their disjoint union `mu_8` by:

| Coordinates | u(x) | v(x) |
|---|---:|---:|
| `x in A` | `0` | `0` |
| `x in B` | `1` | `x` |
| `x = 1` | `3` | `2` |
| `x = -1` | `5` | `2` |

A scalar is bad if `u+gamma*v` agrees with an affine polynomial on at least four
coordinates, on a witness set where `u` and `v` are not both individually affine.

Outside the six exceptional primes, the bad set is exactly

```text
{-1/x : x in A union B} union {-3/2, -2, -5/2, -4/3},
```

and has cardinality ten. The full exceptional table is:

| p | Generators g and exact bad-scalar counts |
|---:|---|
| 17 | `2:9, 8:9, 9:9, 15:9` |
| 41 | `3:11, 14:11, 27:10, 38:10` |
| 97 | `33:9, 47:9, 50:9, 64:9` |
| 137 | `10:10, 41:11, 96:10, 127:11` |
| 337 | `85:9, 111:9, 226:9, 252:9` |
| 641 | `256:9, 318:9, 323:9, 385:9` |

The six-root part of the displayed set is independent of the generator,
because it equals `mu_8 \ {1,-1}`. The construction's partition into `A` and
`B` does depend on the generator; the exceptional extra witnesses at `41`
and `137` detect that dependence. A check at only one generator would miss it.

## Universal certificate

The four-point reduction proved in
`proximity-astra-monomial-census-2026-09-04.md` applies to arbitrary words:
every MCA witness of size at least four contains a four-point witness on
which `v` is nonaffine. Enumerate all 70 four-point supports.

For an ordered support `(i,j,k,l)`, define the unnormalized second divided
difference

```text
D_k(w) = (x_j-x_i)(w_k-w_i) - (x_k-x_i)(w_j-w_i),
a = (D_k(u), D_l(u)), b = (D_k(v), D_l(v)).
```

The event on this support is exactly `a+gamma*b=0` with `b != 0`.
Thus a nonzero determinant `det(a,b)` excludes the support; when that
determinant vanishes and `b != 0`, a chosen nonzero coordinate of `b`
determines the unique candidate. The condition `b != 0` implements the
joint-affine exclusion, rather than silently counting trivial joint witnesses.

Compute all these quantities in `Z[z]/(z^4+1)`, with `x_i=z^i`. Exactly ten
distinct generic rational candidates remain; the certificate verifies that
they are precisely the displayed explicit set by cross multiplication.
For every nonzero determinant, denominator, and candidate-separation
cross-product, compute the norm by two independent exact methods: the
antipodal-squaring ladder and a four-by-four multiplication determinant.

The complete norm sets are:

```text
determinants:
{8,16,32,64,68,136,200,388,400,512,676,776,800,1024,1312,
 1348,1352,2048,2564,2624,2696,3364,4384,5000,5184,8768,
 10000,10256,13456}

denominators:
{2,32,162}

candidate separations:
{4,8,16,64,68,100,388,676,1024,1348,2500,2564,3364,9604}
```

Factoring all these integers leaves exactly

```text
{17,41,97,137,337,641}
```

among prime divisors congruent to one modulo eight. At every other admissible
prime, all nonzero determinants stay nonzero, all chosen denominators stay
nonzero, and all distinct candidates stay distinct. This follows from the
multiplication-matrix adjugate identity, or equivalently the explicit norm
factorization. Literal zero identities remain zero under specialization.
Hence no four-point support can acquire or lose a scalar, and no scalar
candidates can merge. The generic count ten is therefore exact at every
remaining prime and every generator, without a search cutoff.

At the six exceptional primes, the probe evaluates every one of the 70
supports at **all four generators**, including cases whose determinants
vanish only after specialization. This gives the complete table above.

## The extra witnesses at 41 and 137

The supports with one coordinate in `A`, one in `B`, and both coordinates
in `C` account for the new exceptions. Their determinant norms are

```text
{32,800,1312,2624,4384,5184,8768}.
```

The factors `1312=32*41`, `2624=64*41`, `4384=32*137`, and
`8768=64*137` reveal the two extra characteristics. Their new scalars are:

| (p,g) | Additional gamma beyond the explicit ten-set |
|---|---:|
| `(41,3)` | `23` |
| `(41,14)` | `5` |
| `(137,41)` | `85` |
| `(137,127)` | `46` |

For example, at `(p,g)=(41,3)`, scalar `23` agrees with `ell(x)=9-x` on
`{1,g^2,-1,g^7}={1,9,40,14}`. The values of `v` are `2,0,2,14`, so `v`
is nonaffine on that witness. The full bad set is

```text
{3,9,14,18,19,23,26,27,32,38,39}.
```

At `(p,g)=(137,41)`, scalar `85` agrees with `ell(x)=37-x` on
`{1,g^2,-1,g^5}`. The full bad set is

```text
{10,37,41,66,67,85,90,96,100,127,135}.
```

An independent implementation enumerates **every scalar, intercept, and
slope** at both these cells, checks the original MCA event including the
joint-exclusion clause, and agrees with the support-elimination census.

## Reproduction and scope

Run:

```sh
python3 scripts/probes/astra_nonmonomial_exact_census.py
```

The probe uses the integer cyclotomic arithmetic helpers from
`astra_order_eight_monomial_certificate.py`, checks the complete finite norm
certificate and all exceptional cells, and performs the independent
all-affine exhaustive checks. It passed on 2026-09-04 in under one second
on the working host.

Combined with the field-uniform monomial maximum nine, this construction
proves that monomial pencils miss genuine order-eight MCA behavior even
at arbitrarily large admissible prime-field size: the explicit pencil has
ten bad scalars at every `p>641`. No claim that ten or eleven is the global
maximum follows. This does not settle the production subgroup order,
production threshold, or Proximity Prize; those remain open. No Lean
compilation or axiom audit was claimed for these new certificates.
