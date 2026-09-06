# Four cubic sources improve the production unsafe radius to 5/16+1/n

There is a received line for the actual production prime, subgroup of order n=2^30, and Reed–Solomon dimension k=n/2 with at least

    n+6 = 1073741830

MCA-bad scalars at exact support size 738197503. Thus its MCA error exceeds 2^-128 at radius

    delta = 335544321/1073741824 = 5/16+1/n.

This is a written construction with exact production-prime seed and parameter checks and independent actual-polynomial controls. The seed/fiber construction and final numerical bound are not Lean-formalized. Generic finite-choice and original-event bridges are kernel-checked separately; this is not a full bad-set census or an exact determination of the optimal MCA radius. The construction uses general polynomial pencils, not the separate single-hole value family.

For the repository's supremum convention, this gives

```text
epsMCA(C,335544321/2^30) >= (2^30+6)/P > 2^-128,
mcaDeltaStar(C,2^-128) <= 335544321/2^30.
```

It improves the earlier [six-source bound](astra_mca_root_relocation-2026-09-06.md).
The field and generator are the [certified production parameters](../../ArkLib/Data/CodingTheory/ProximityGap/Frontier/_PrizeShapePrimeP30.lean).

## Current bracket and the remaining gap

For this code and the repository's supremum convention, the available written
arguments give

```text
268435457/2^30 <= mcaDeltaStar(C,2^-128) <= 335544321/2^30.
```

The interval has width exactly `1/16`. The lower side comes from the existing
[`ProximityGap.UDRwire.epsMCA_rs_udr_le_full`](../../ArkLib/Data/CodingTheory/ProximityGap/MCAUDRBound.lean)
and the [RS relative unique-decoding-radius formula](../../ArkLib/Data/CodingTheory/ReedSolomon.lean):
at `delta=1/4`, the agreement floor is `t=3n/4`, the distance condition is
`2(n-t)=n/2<n-k+1=n/2+1`, and `epsMCA<=n/P<2^-128`.
The event predicate depends on delta only through the integer support floor
`ceil((1-delta)n)`. This floor stays `3n/4` throughout
`[1/4,(n/4+1)/n)`, so that entire half-open interval is safe. Its right endpoint
is therefore a lower bound on the supremum; this does not assert safety at
that endpoint. The [arithmetic receipt](../../scripts/probes/receipts/astra_four_cubic_20260906/bracket_arithmetic.json)
checks the numeric substitutions and interval width. The lower theorem's
source was audited; a fresh kernel check of that dependency chain is not
claimed by this receipt.

A solution still needs a matching universal safety bound or a stronger attack
and matching bound. The fixed-family dual below cannot supply that universal
statement. The [official grand MCA challenge](https://proximityprize.org/)
also ranges over the specified constant rates and smooth domains, beyond this
one code.

## Four explicit cubics on the actual order-eight subgroup

Set

    P=365375409332725729550921208179070755120141565953,
    g=303645430271030343624574566109998498685964493478,
    n=2^30, s=n/8=134217728, k=4s, eta=g^s.

The checker verifies that g has order n and eta has order eight in F_P. Define

    R1(Y)=(Y-1)(Y-eta)(Y-eta^5),
    R2(Y)=(Y-1)(Y-eta^3)(Y-eta^4),
    R3(Y)=(Y-eta)(Y-eta^2)(Y-eta^3).

All three R_i(eta^6) are nonzero. Let

    W0=0,
    W1=R1,
    W2=[R1(eta^6)/R2(eta^6)] R2,
    W3=[R1(eta^6)/R3(eta^6)] R3.

These definitions are explicit field operations, with no assumed interpolants or search oracle. The exact certificate expands their coefficients and checks every equality class below over the production field:

| j | Equality classes of W_i(eta^j) |
|---|---|
| 0 | {0,1,2}, {3} |
| 1 | {0,1,3}, {2} |
| 2 | {0,3}, {1}, {2} |
| 3 | {0,2,3}, {1} |
| 4 | {0,2}, {1}, {3} |
| 5 | {0,1}, {2}, {3} |
| 6 | {0}, {1,2,3} |
| 7 | {0}, {1,2,3} |

It also verifies gcd(W1,W2,W3)=1 and the six complete root sets of the nonzero cubic differences:

| Pair | Exponents of its three roots |
|---|---|
| 0,1 | 0,1,5 |
| 0,2 | 0,3,4 |
| 0,3 | 1,2,3 |
| 1,2 | 0,6,7 |
| 1,3 | 1,6,7 |
| 2,3 | 3,6,7 |

Each difference is checked to equal its leading coefficient times the displayed three linear factors. In particular, the data retain actual common-domain membership rather than only abstract incidence counts.

## Exact domain and degree allocation

Fiber j consists of the s distinct domain points

    x=g^(j+8t), 0<=t<s,

and has x^s=eta^j. In fibers 4 and 5 choose s/2-1 common roots each, using the first such points in this order. Let Z be their union and define

    B(X)=product_(z in Z)(X-z),
    p_i(X)=B(X)W_i(X^s), q_i(X)=X p_i(X).

The factor B is an actual squarefree split divisor of X^n-1 with degree s-2. The common gcd condition gives exactly Z as the simultaneous zeros of the four p_i. Each nonzero p_i has degree s-2+3s=k-2, and q_i has degree k-1, so both belong to the full code.

At Z set the received pair to (0,0). Use the following remaining allocations; ownership means setting the received pair equal to (p_i(x),q_i(x)) for an index in the indicated full equality class.

| Fiber | Covered non-root nodes | Common roots | Uncovered nodes |
|---|---|---|---|
| 0 | s with owner {0,1,2} | 0 | 0 |
| 1 | s with owner {0,1,3} | 0 | 0 |
| 2 | s/2 with owner {0,3} | 0 | s/2 |
| 3 | s with owner {0,2,3} | 0 | 0 |
| 4 | s/2 with owner {0,2} | s/2-1 | 1 |
| 5 | s/2 with owner {0,1} | s/2-1 | 1 |
| 6 | s with owner {1,2,3} | 0 | 0 |
| 7 | s with owner {1,2,3} | 0 | 0 |

Consecutive blocks in the stated fiber order specify every node. Each of the four exact joint cores has size

    A=11s/2-2=738197502.

For index 0, covered ownership contributes 3s+3s/2; for each other index it contributes 4s+s/2. Adding the same s-2 common roots gives A in all cases. The assignments at uncovered nodes below are off every local pair, so they give no additional joint-core points.

## Finite choices giving distinct directions

At each covered non-root node the local pairs have the form (z,xz), and there are at least two distinct z values. Any nonowner has nonzero residual proportional to (1,x), and therefore cancels at gamma=-1/x. Different domain nodes give different finite scalars. These covered nodes supply

    13s/2=872415232

ordinary directions.

Every uncovered node is in fiber 2, 4, or 5, where there are exactly three distinct local values z. The following finite choice supplies three fresh directions at each such node.

Maintain a set Gamma containing all reciprocal directions -1/mu_n and all fresh directions already chosen. Choose a outside the three local values. Set the received pair to (a,t); its direction for local value z is

    gamma_z=(a-z)/(xz-t).

Exclude t=xz for each z, so no denominator vanishes. Exclude t=xa: the cross-multiplied equality between the directions for distinct z,z' has numerator (z'-z)(xa-t), so this makes the three directions distinct. For every nonzero gamma in Gamma and each z, exclude

    t=xz-(a-z)/gamma.

The zero direction is already impossible because a differs from every z. At most 3(|Gamma|+1)+1 field elements t are forbidden. There are at most n uncovered nodes, so |Gamma|<=4n throughout; P>12n+4 is more than sufficient. The displayed production prime meets this bound. Choosing the least permitted field representative at every step makes the construction deterministic.

Consequently the s/2+2 uncovered nodes supply

    3s/2+6=201326598

finite directions distinct from all ordinary directions and from each other. The total certified count is

    D=13s/2+3s/2+6=8s+6=n+6.

This is a finite existence argument with an explicit forbidden-set bound, not an assumption about random choices or an exhaustive production-sized computation.

## Original same-support MCA witnesses

For each counted scalar choose a pencil whose nonzero residual is cancelled at the displayed outside node x. On its full A-point exact core, both received components agree with p_i,q_i. Therefore p_i+gamma q_i agrees with the received line on the exact support consisting of that core and x, of size A+1.

A joint pair of degree less than k on the same support would coincide with p_i,q_i on the A>=k core points. The polynomial root bound forces equality as polynomials, which contradicts the nonzero residual at x. This establishes the original same-support/no-joint condition against the full Reed–Solomon code; it does not restrict competing codewords to the composed source family.

The production prime satisfies P=n(2^128+192)+1, and

    (n+6)2^128-P=6*2^128-192n-1>0.

Hence the MCA error is strictly greater than 2^-128 at the displayed radius.

## The integer correction is optimal within these four sources

This section concerns only directions supplied by the selected four pencils with p_i=B W_i(X^s), q_i=Xp_i and a nonzero common factor B of degree at most s-2. It permits arbitrary common-root locations and received values. It does not upper-bound additional decoder pencils or the full bad-scalar set.

Assign candidate weights (0,2,2,2) and fiber weights

    beta=(5,5,3,5,3,3,7,7), sum beta=38.

At a non-root uncovered node, at most the number of local classes can supply finite nonzero-residual directions, and that number is at most beta_j. At a covered node, at most one such direction occurs and the weighted core credit is 2 times the number of owners among {1,2,3}; the exact partition table verifies that their sum is at most beta_j.

At a common root, either all four pairs jointly agree (weighted core credit six and no nonzero residual) or none does (core credit zero and at most one direction). Both are bounded by beta_j+3. Counting root nodes by deg B and summing gives

    D+2(C1+C2+C3)<=38s+3deg B.

For all four cores at least A and deg B<=s-2,

    D+6A<=41s-6.

Requiring D>=n+1=8s+1 yields A<=11s/2-7/6, hence the integer bound A<=11s/2-2. The construction attains equality in the count bound, with D=n+6. Raising every core by one would force D<=n. Thus no different ownership or common-root placement within this fixed source family improves the radius correction while retaining an over-budget certified union.

## Reproduction and independent checks

Run the standalone standard-library checker:

    python3 scripts/probes/astra_mca_four_cubic_check.py

It derives the four cubics directly from eta, verifies the eight partitions and six cubic factorizations, checks gcd one, all production allocations/degrees/core counts, the strict security inequality, and every local inequality in the restricted dual. Its output is the exact [primary JSON fixture and receipt](../../scripts/probes/receipts/astra_four_cubic_20260906/primary.json) with status `PASS_EXACT_ORDER8_FOUR_SOURCE_PRODUCTION_CONSTRUCTION`. No numerical LP dependency is used in certification.

An [independent implementation](../../scripts/probes/astra_mca_four_cubic_independent_check.py) expands actual B and p_i at n=64 and n=128 over the same production field, constructs every received value, and checks all 70 and 134 distinct directions and exact core-plus-outside agreement sets. Its [receipt](../../scripts/probes/receipts/astra_four_cubic_20260906/independent.json) records both dense controls. Its independently hardcoded sources differ from the displayed normalized sources by one common nonzero scalar; a [coefficient comparison](../../scripts/probes/receipts/astra_four_cubic_20260906/normalization.json) checks that equivalence. The independent audit also checks no-joint through the full-code polynomial root bound. Production parameters are checked by exact formulas, rather than expanding billion-entry words.

The seed discovery used intersections of the 56 five-support syndrome hyperplanes for order-eight dimension-four Reed–Solomon codes. It enumerated 5184 distinct rank-three intersection points and then tested the resulting seed families. Discovery output is not a universal optimality theorem; the certificate above depends only on the explicit four cubics and exact finite arithmetic.

The [manifest](../../scripts/probes/receipts/astra_four_cubic_20260906/manifest.json) binds this proof, both checkers, and their receipts by SHA-256. Reproduce the independent implementation with:

```sh
python3 scripts/probes/astra_mca_four_cubic_independent_check.py
```

The [generic Lean bridges](../../scripts/probes/astra_mca_root_relocation.lean) prove simultaneous fresh-direction selection and the original MCA event from a joint core plus one point. They discharge those reusable steps under explicit hypotheses. The numerical production theorem still requires the seed, fiber, common-factor, received-word, and final counting instantiations.
