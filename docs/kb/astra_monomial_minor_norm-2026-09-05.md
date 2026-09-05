# Monomial seeds, Fourier minors, and finite-field exceptions

**Status:** a bounded obstruction certificate, not a production lower bound.
On `mu_16` over the production prime, every word `X^d`, `8<=d<16`, has
at most eight agreements with every degree-less-than-eight polynomial.
Thus this family cannot seed a single-hole counterexample at eleven
punctured agreements. The checker classifies exactly the characteristics
where this statement fails on `mu_16`, rather than extrapolating from
complex Fourier matrices. No analogous production-length bound is proved.

The complex nonvanishing statement is an application of established work:
[Alexeev, Cahill, and Mixon, Theorem 9 and Lemma 10](https://borisalexeev.com/pdf/spark.pdf)
characterize full-spark Fourier row sets at prime-power lengths. Related
universal-sampling results appear in
[Osgood, Siripuram, and Wu](https://arxiv.org/abs/1204.0992).
For `n=2^r`, `k=n/2`, the rows `{0,...,k-1,d}` are uniformly distributed
modulo every divisor of n. That theorem concerns complex matrices. The
explicit finite-field exception computation below is the research receipt.

## An exact coefficient criterion

Let a field contain a primitive n-th root omega, with `n=2^r` and `k=n/2`.
Fix `k<=d<n`, choose any `k+1` domain points I, and let T be their complement,
of size `k-1`. Write `H_I=product_(x in I)(X-x)`. There exists a polynomial
f of degree less than k equal to `X^d` on I precisely when

```text
[X^k] rem(X^d,H_I) = 0.
```

Indeed, the unique interpolant of degree at most k is this remainder.
Put `j=d-k`. The coefficient has the useful exact form

```text
[X^k] rem(X^(k+j),H_I)
  = h_j(I)
  = (-1)^j * e_j(T)
  = [X^(k-1-j)] product_(x in T)(X-x).                 (1)
```

For the first equality, the coefficients of the remainders satisfy the
recurrence obtained by reducing powers with the monic polynomial H_I;
their generating series is `product_(x in I)(1-xZ)^(-1)`. For the second,

```text
product_(x in I)(1-xZ)^(-1)
  = product_(x in T)(1-xZ)/(1-Z^n),
```

and `j<n`, so the denominator does not change the required coefficient.
This derivation is valid in every characteristic not dividing n.

Thus monomial-plus-code nonvanishing on all `k+1` subsets is equivalent
to nonvanishing of all coefficients of all size-`k-1` domain locators.
It is stronger than exclusion at a two-thirds agreement threshold.

## The characteristic-zero statement and a sufficient transfer bound

Lift the roots to powers of a complex primitive root zeta and put
`beta=(-1)^j e_j(T)` in `Z[zeta]`. Reduction `zeta -> 1` modulo 2 gives
`beta -> binomial(k-1,j)=1 mod 2`, since `k-1` has all binary digits equal
to one. Hence beta is nonzero in the cyclotomic field. This is the
elementary specialization of the cited prime-power argument.

Every conjugate of beta has absolute value at most `binomial(k-1,j)`.
Its norm is therefore a nonzero integer of absolute value at most

```text
B_n = binomial(k-1, floor((k-1)/2))^k.                 (2)
```

If reduction at any primitive n-th root in characteristic p makes beta
zero, then p divides that nonzero norm. Therefore `p>B_n` suffices for
all the same monomial nonvanishing statements in every field of that
characteristic containing `mu_n`.

This transfer bound already fails for the production prime at `n=32`:
`binomial(15,7)^16>P`, whereas it passes at `n=16`, where `B_16=35^8`.
It also fails at the actual length `2^30`: here the binomial base is at
least seven and the exponent at least 64, while `7^64>P`. This is only
failure of a sufficient bound. It proves neither vanishing nor
nonvanishing of production-length minors.

## Exact exception certificate at length sixteen

The checker enumerates all `binomial(16,7)=11440` subsets T and all eight
coefficients of each locator in `Z[Z]/(Z^8+1)`. It computes 91,520 norms
exactly, obtaining 50 distinct positive odd values, with maximum
`66049=257^2`. Trial division gives the exact exceptional-characteristic set:

```text
3,5,7,11,17,23,31,41,97,113,193,241,257,337,353,401,433,
449,577,593,641,673,769,881,929,977,1489,1553,1873,2113,
2129,3137,3329,3761,9601.
```

For any odd characteristic outside this set, all coefficients and hence
all the specified Fourier minors are nonzero. In particular every prime
greater than 9601 works at length sixteen.

Conversely, if p is in the set, some norm is zero modulo p. In any field
of characteristic p containing `mu_16`, that norm is the product of
beta evaluated at the eight primitive roots. At least one factor is zero.
Changing the primitive root multiplies T's exponents by an odd residue,
which permutes the enumerated subsets. Thus some coefficient vanishes
for any fixed primitive root: the exception set is exact, not merely a
list of possible primes. For prime fields themselves retain only the
listed primes congruent to one modulo sixteen.

There is a directly reconstructed failure over F17, with omega=3:

```text
d=13,
f=5+12X+11X^2+11X^3+14X^4+9X^5+13X^6+12X^7,
agreement exponents={6,7,8,9,11,12,13,14,15}.
```

This polynomial has nine agreements with `X^13` on `mu_16`, contradicting
an unqualified finite-field import of the complex agreement cap eight.
A second independent field control over F97, omega=8, uses

```text
d=10,
f=4+58X+42X^3+55X^4+30X^5+41X^6+76X^7,
agreement exponents={3,6,7,9,10,12,13,14,15}.
```

These do not refute any prize threshold. Their role is to prevent a
false transfer across characteristics.

## Consequence for the current search

Over the actual production prime P at length sixteen, (1) and the norm
certificate imply the agreement cap eight for every `8<=d<16` and every
candidate f, including arbitrary low-degree coefficients. A codeword
translate and nonzero scalar multiple of a monomial have the same cap.
Deleting a domain point cannot increase the number of agreements, so the
[single-hole target](astra_mca_single_hole_reduction-2026-09-05.md) of eleven
punctured agreements has no seed in this family on `mu_16`.

This does not restrict arbitrary punctured received words, prove a locator
rank cap, exclude monomial seeds at production length, or bound the complete
MCA event. The universal value-image problem remains open. No independent
agent review or Lean theorem is claimed.

## Reproduction

```sh
python3 scripts/probes/astra_monomial_minor_norm_check.py
```

The norm calculation uses successive relative norms under `zeta -> -zeta`.
An independent fraction-free determinant of multiplication by beta checks
one representative for each of the 50 norm values. There are also 128
direct remainder checks of (1), direct modular coefficient evaluations
over F17, F97 and the production prime, and explicit verification of both
failure polynomials. The receipt records the full norm histogram and
exception set. All computations are at length sixteen; the large-length
cell checks only the failure of the sufficient bound (2).
