# A uniform nonmonomial witness exceeding the order-eight monomial maximum

Date: 2026-09-04. Status: explicit mathematical construction with exact Python
verification; not Lean checked. The production Proximity Prize remains open.

For every prime `p = 1 mod 8` outside `{17,97,337,641}`, the order-eight,
dimension-two Reed–Solomon code admits a received-word pencil with **at least
ten** threshold-four MCA bad scalars. The companion monomial certificate proves
that all 64 pure monomial pencils have at most nine. Thus even the field-uniform
monomial answer does not give the arbitrary-pencil answer.

The repository already records other failures of monomial extremality, notably
the order-sixteen experiments in `deltastar-466-p5-replication-2026-07-01.md`.
The point here is a short, explicit order-eight construction with a uniform
large-field argument, alongside the now-certified monomial comparison.

## Construction and witnesses

Let `g` have order eight. Partition the domain as

```
A = {g,g²,g³}, B = {-g,-g²,-g³}, and {1,-1}.
```

Define received words `u,v` by

| Points | u(x) | v(x) |
|---|---:|---:|
| A | 0 | 0 |
| B | 1 | x |
| 1 | 3 | 2 |
| -1 | 5 | 2 |

For every `x` in `B`, the scalar `gamma=-1/x` makes `u+gamma*v`
agree with the zero affine polynomial on `A union {x}`. For every `x` in
`A`, the same scalar makes the pencil agree with `1+gamma*X` on
`B union {x}`. These are six distinct scalars.

Four more explicit witnesses are:

| gamma | affine polynomial | four-point support |
|---|---|---|
| -3/2 | 0 | A union {1} |
| -5/2 | 0 | A union {-1} |
| -2 | 1-2X | B union {1} |
| -4/3 | 1-(4/3)X | B union {-1} |

Each satisfies the MCA exclusion: `u` itself is not affine on its support.
An affine polynomial agreeing with `u=0` on three points of `A` must be zero;
its added point has a nonzero `u` value. Likewise an affine polynomial agreeing
with `u=1` on three points of `B` must be the constant one, and its added point
has a different value. In these prime fields `p>=17`, all the differences used
here are nonzero. These witnesses prove badness under the actual nonjoint MCA
event, not merely closeness of a linear combination to the code.

## Distinctness uniformly in the field

The first six scalars form `H \ {1,-1}`. They are precisely the roots of

```
S(X) = (X²+1)(X⁴+1) = X⁶+X⁴+X²+1.
```

For a reduced rational `a/b`, multiplying `S(a/b)` by `b⁶` gives
`a⁶+a⁴b²+a²b⁴+b⁶`. The four explicit scalars have the following values:

| Scalar | Integer numerator | Factorization |
|---|---:|---|
| -3/2 | 1261 | 13 * 97 |
| -2 | 85 | 5 * 17 |
| -5/2 | 18589 | 29 * 641 |
| -4/3 | 8425 | 5² * 337 |

Among these prime divisors, only `17,97,337,641` are one modulo eight. Pairwise
differences of the rational scalars have numerators with prime divisors only
`2,7`; denominators use only `2,3`. Consequently all ten values are distinct
for every prime in the stated range. In particular the lower bound holds for
every prime `p = 1 mod 8` with `p>641`, without a search cutoff.

This proves a lower bound, not an upper bound. Other agreement supports can
contribute additional scalars. The independent exact-census analysis in
`proximity-astra-nonmonomial-exact-2026-09-04.md` finds eleven, for example,
at `p=41,g=3`. Generator choice changes this piecewise construction; it does
not change the underlying code.

## Verification and scope

Run `python3 scripts/probes/astra_nonmonomial_witness.py`. It checks the integer
factorizations, each explicit affine witness and its exclusion clause over all
68 eligible primes up to 2000, and the same ten witnesses at the Proth-certified
prime `111*2^128+1`. It independently enumerates every scalar and every affine
codeword at `p=17,41,73` for its selected generators.

The large-prime check addresses field size only: the domain still has length
eight. Nothing here gives a production-length bound, the full MCA supremum,
a new threshold for the prize's security target, or a companion leaderboard
submission. The value of this check is to keep those quantifiers explicit.
