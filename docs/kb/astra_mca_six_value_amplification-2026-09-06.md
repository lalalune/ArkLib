# Six production values from split-fibre assignments

There is an explicitly specified word on the punctured production domain
with six degree-<k candidates taking six distinct values at the hole. The
smallest punctured agreement count is 724775729, exceeding the required
715827883 by 8947846. This improves the earlier construction's count of
five values. Six is still far below the production scalar budget 1073741824;
these witnesses do not change the known unsafe-radius bound.

A later [root-relocation construction](astra_mca_root_relocation-2026-09-06.md)
changes the seed family and produces an over-budget general MCA line.
The six-value result on this page is an earlier punctured-list construction.

The change is to assign different received values to different points in
three fibres of the map `X -> X^s`. The candidate polynomials remain lifts
of six degree-at-most-seven seed polynomials. The received word is not
required to be a lift of a single sixteen-point word.

The construction has a written proof, an exact certificate, and independent
agent review with a separately implemented dense check. It is not
Lean-formalized or externally peer-reviewed. No claim of literature novelty
or of a complete production list census is made.

## Exact seed and fibre assignments

Use the [certified production field](../../ArkLib/Data/CodingTheory/ProximityGap/Frontier/_PrizeShapePrimeP30.lean)
and generator

```text
P=365375409332725729550921208179070755120141565953,
g=303645430271030343624574566109998498685964493478,
n=2^30, k=n/2, s=n/16=67108864, eta=g^s.
```

The [exact certificate](../../scripts/probes/astra_mca_six_value_certificate.json)
lists six polynomials f_0,...,f_5, with coefficients in ascending order,
and every received base value as a canonical field integer. The first five
are the earlier [five-candidate seeds](astra_mca_five_candidate_lift-2026-09-05.md).
Their degrees, followed by the new seed's degree, are `7,7,7,7,5,7`.
All six values f_i(1) are distinct; `2*f_5(1)=f_4(1)`.

For each base exponent j, the following rows prescribe a fraction of that
fibre and all candidates equal to its assigned base value. The value is
f_i(eta^j) for any listed owner; the exact checker verifies every equality
and every unlisted candidate's inequality.

| j | Fraction | Owners |
| --- | --- | --- |
| 1 | 1 | 0,1,2,3,5 |
| 2 | 1 | 0,1,2,3,4 |
| 3 | 1 | 2,3,4,5 |
| 4 | 1 | 1,3,4,5 |
| 5 | 1 | 0,3 |
| 6 | 1 | 0,2,4,5 |
| 7 | 1 | 0,1,4,5 |
| 8 | 1 | 0,1,2,3,4 |
| 9 | 1 | 0,1,2,3,5 |
| 10 | 1 | 0,1,2,3,4,5 |
| 11 | 1 | 2,3,4,5 |
| 12 | 3/5 | 1,3,4 |
| 12 | 2/5 | 2,5 |
| 13 | 4/5 | 1,2 |
| 13 | 1/5 | 0,3 |
| 14 | 2/5 | 1,5 |
| 14 | 3/5 | 0,2,4 |
| 15 | 1 | 0,1,4,5 |

The fractional nonhole agreements are `49/5` for candidates 0,1,2,3,5,
and `51/5` for candidate 4. These rational numbers are an exact certificate,
not toleranced output from the numerical search that discovered them.

The fibre of eta^j has the ordered points `g^(j+16t)`, `0<=t<s`.
For a split row, assign its first value to the first `floor(s*w)` points
and its second value to the rest. Thus the exact split counts are

```text
j=12: 40265318,26843546;
j=13: 53687091,13421773;
j=14: 26843545,40265319.
```

## Lift and exact agreement counts

Set

```text
J_s(X)=(X^s-1)/(X-1),
F_i(X)=J_s(X)*f_i(X^s).
```

On a nontrivial fibre let the received value at x be `J_s(x)*y`, with y
chosen by the assignment above. There J_s(x) is nonzero, so F_i agrees
exactly when f_i(eta^j)=y. On the fibre of 1, set the received value to zero
at every point other than 1. All candidates agree at these s-1 points
because J_s vanishes there. The point 1 is omitted.

For each candidate the exact punctured count is s-1 plus the integer sizes
of all owned rows. The polynomial degree is `s*(degree f_i+1)-1`, and the
hole value is `s*f_i(1)`. Since s is nonzero in the field, the six hole values
remain distinct.

| Candidate | Degree | Punctured agreements |
| --- | --- | --- |
| 0 | 536870911 | 724775731 |
| 1 | 536870911 | 724775729 |
| 2 | 536870911 | 724775731 |
| 3 | 536870911 | 724775730 |
| 4 | 402653183 | 751619276 |
| 5 | 536870911 | 724775730 |

These are counts for the new split-fibre word. The old sixteen-point word
had only nine agreements with f_5, so its unsplit lift would fail the target.
The fractional reassignment is what makes the sixth candidate qualify.

## Actual same-support MCA consequence

Set u_0 equal to the new word off 1 and zero at 1, and let u_1 be the
indicator of 1. At gamma=F_i(1), the scalar word `u_0+gamma*u_1` agrees
with F_i at all of its punctured agreements and at 1. Trim to a support of
715827884 points containing 1 if necessary.

A joint explanation on this same support would require a degree-<k
polynomial equal to u_1. It would have at least 715827883>=k zeros off 1
and value one at 1, contradicting the root bound. Therefore the six
distinct hole values are actual MCA-bad scalars, not just scalar decodings.
This is the [single-hole reduction](astra_mca_single_hole_reduction-2026-09-05.md).
It gives

```text
epsMCA(C,357913940/1073741824) >= 6/P.
```

The displayed lower bound is below 2^-128. It does not prove security:
other words and other candidates are not bounded by this construction.

## Reproduction and independent review

Run

```bash
python3 scripts/probes/astra_mca_six_value_check.py
python3 scripts/probes/astra_mca_six_value_independent_check.py
```

The [primary checker](../../scripts/probes/astra_mca_six_value_check.py)
uses exact field and rational arithmetic, with no LP dependency. It checks
the seed incidences, integer fibre sizes, production counts and hole values.
Dense controls at lengths 512 and 1024 expand all six polynomials, evaluate
all coordinates, and check a parity obstruction to a joint explanation on
each witness support.

The [independent checker](../../scripts/probes/astra_mca_six_value_independent_check.py)
imports no repository probes and embeds the exact inputs separately. It
reconstructs the rational and rounded counts, expands all six polynomials
at length 1024, and checks all 6144 candidate evaluations. Independent
mathematical review found no defect in the degree, counting or same-support
argument. The full production domain is not enumerated.
