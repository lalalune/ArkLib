# Two monomial classes have empty production punctured lists

On the production domain, neither `X^805306367` nor `X^805306368` has a
degree-<536870912 polynomial agreeing at 715827883 punctured coordinates.
The conclusion also holds after multiplying either word by a nonzero scalar
and adding a code polynomial. This follows from a four-coset root count over
the actual finite field. It does not bound the list of arbitrary words or
the universal MCA error.

There is also a sharp characteristic-zero exclusion for the entire
nontrivial monomial window. Its reduction modulo 2 does **not** transfer to
the production prime. The finite-field theorem below handles exactly two
degrees in that window. These are written proofs with exact computational
controls, not Lean formalizations or claims of literature novelty.

## Exact monomial-to-locator equivalence

Let `n=4^a`, `a>=2`, and let the field contain n distinct nth roots of unity.
Put

```text
n=6b-2, k=3b-1, A=4b-1, e=2b-2,
W=(X^n-1)/(X-1), d=e+1=2b-1=(n-1)/3.
```

The domain is `mu_n` with 1 removed. A candidate f of degree <k that agrees
with a word v at least A times is equivalent to a monic degree-e divisor
Lambda of W satisfying

```text
degree rem(Lambda*v,W) < k+e.
```

For the forward direction, pad the candidate's error set to e points and
use its locator Lambda. The remainder is Lambda*f, whose degree is <k+e.
Conversely, the remainder is divisible by Lambda because Lambda divides W.
Its quotient f has degree <k and agrees with v at every point outside
Lambda's roots, giving at least `(n-1)-e=A` agreements. This equivalence
uses the actual split divisor, not an arbitrary polynomial with the right
degree.

For a non-code monomial v=X^D, reduce the exponent modulo n and take
`k<=D<=n-1`.
The root bound excludes D<A. Multiplying the agreement equation by
`X^(n-D)` excludes `D>n+k-1-A`, because then `1-X^(n-D)f` is a nonzero
polynomial of degree <A. Thus the only possible window is

```text
4b-1 <= D <= 5b-3.
```

Write `Lambda=sum lambda_j X^j`. First reduce Lambda*X^D modulo X^n-1,
then subtract its X^(n-1) coefficient times W. In the relevant high-degree
range no wrapped term contributes. Consequently the remainder condition
is exactly

```text
lambda_L=lambda_(L+1)=...=lambda_U,
L=5b-3-D, U=6b-3-D.
```

Setting `H=(X-1)Lambda` gives a monic degree-d divisor of X^n-1 containing
the root 1, with the b consecutive zero coefficients

```text
h_(L+1)=...=h_U=0.
```

Conversely, a divisor H with these properties recovers such a Lambda and
therefore a candidate. The possible gaps start at indices 1 through b-1.
For production n, the monomial window is 715827883 through 894784852.

## Two central gaps are impossible over every allowed field

Write

```text
ell=n/4=3q+1, q=(ell-1)/3,
d=4q+1, b=2q+1, k=6q+2, A=8q+3.
```

For `D=3ell-1=9q+2`, the required gap is `q+1,...,ell`.
For `D=3ell=9q+3`, it is `q,...,ell-1`.

The four values zeta=x^ell partition mu_n into four cosets. In the first
case write

```text
H=A_0(X)+X^(ell+1)*B_0(X),
degree A_0<=q, degree B_0<=q-1, A_0(0)=H(0)!=0.
```

On each coset H equals `A_0+zeta*X*B_0`. This polynomial has degree at most
q and nonzero constant term, so it has at most q roots there.

In the second case write

```text
H=A_1(X)+X^ell*B_1(X),
degree A_1<=q-1, B_1 monic of degree q.
```

The restriction `A_1+zeta*B_1` has degree exactly q, giving the same root
bound. No restriction can vanish identically: its constant term in the
first case or leading coefficient in the second is nonzero.

Thus H has at most 4q roots in mu_n. But H is a squarefree divisor with
degree 4q+1. This contradiction proves both empty-list claims. At production
the excluded degrees are 805306367 and 805306368. Replacing f by `(f-g)/c`
proves the claimed extension to `cX^D+g`, for `c!=0` and `degree g<k`.

## Sharp characteristic-zero benchmark

Let `d_a=(4^a-1)/3`. Its binary expansion has ones at positions
`0,2,...,2a-2`. Over F2, direct expansion gives

```text
(1+X)^d_a = product_(i=0..a-1) (1+X^(4^i)).
```

Its nonzero coefficient indices form
`S_a=S_(a-1) union (4^(a-1)+S_(a-1))`. The largest distance between
successive indices is

```text
G_a=max(G_(a-1),4^(a-1)-d_(a-1))=(4^a+2)/6=b,
G_1=1.
```

The longest run of zero coefficients therefore has length b-1. Every
internal block of b indices contains a nonzero coefficient.

For any characteristic-zero monic H whose d_a roots lie in mu_n, its
coefficients lie in Z[zeta_n]. The map `zeta_n -> 1` into F2 is well-defined
because the cyclotomic polynomial at 1 is 2. Under this map H becomes
`(X-1)^d_a`. Every coefficient indexed by S_a is nonzero already in
Z[zeta_n]. Hence H cannot have a b-coefficient internal zero gap.
The locator equivalence excludes all non-code monomials in characteristic
zero, not merely the two central ones.

The bound b-1 is attained by actual squarefree divisors. Choose Q monic of
degree q with distinct roots in `mu_n` outside `mu_ell`, and set
`H=(X^ell-1)Q`. The coefficients at `q+1,...,ell-1` vanish, a run of
`ell-q-1=b-1` zeros, with nonzero coefficients at both boundaries. H has
degree d, contains the root 1, and divides X^n-1. This construction also
works in the finite fields under consideration.

A coefficient nonzero under the characteristic-zero argument may vanish
on reduction at an odd prime. Nothing in the argument rules this out at
the production prime. The finite-field central-gap proof is independent
of this characteristic-zero benchmark.

## Reproduction and limits

Run

```bash
python3 scripts/probes/astra_mca_monomial_gap_check.py
```

The [standalone checker](../../scripts/probes/astra_mca_monomial_gap_check.py)
enumerates all 1365 degree-five divisors containing 1 at length 16, over
each of seven fields including the production field. It checks both gap
positions against an independently computed polynomial remainder, giving
19110 comparisons and no candidates. A constructed non-monomial word
provides a positive locator-to-decoder recovery control in each field.

Nine dense controls at lengths 16,64,256 over F257, F65537 and the production
field check the sharp b-1 gap, divisibility and the exact domain roots.
The parity-support recurrence and central-gap indices are checked through
`n=4^15=2^30`. The production-length conclusion relies on the written root
count, not on enumerating its domain.

The [single-hole reduction](astra_mca_single_hole_reduction-2026-09-05.md)
explains why arbitrary punctured words matter for MCA. Two empty monomial
classes do not establish the required cap of n values for every word, and
that cap itself is only a subfamily of the universal received-pair problem.
