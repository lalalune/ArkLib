# A genuine common-domain six-pencil example with 23 bad scalars at length 22

There is an exact RS example over K=F43[i], i^2=-1, with n=22, k=11, six saturated polynomial pencils, and exactly 23 finite MCA-bad scalars on the whole received line at agreement threshold 16. Every exact joint core has size 14. All pairwise absence intersections have size 2=b-2, and all six locators divide one squarefree degree-22 domain polynomial.

This realizes the common-domain conditions missing from the [earlier abstract six-square countermodel](astra_mca_six_square_countermodel-2026-09-05.md). It shows that those conditions, even with the sharp pairwise gcd bound and six full saturation conditions, do not force two scalar overlaps or an unsaturated pencil at arbitrary domains and even b. The example has exactly one scalar overlap. It therefore does not refute a claim forcing at least one overlap.

It is a small-characteristic, non-cyclotomic example, not a production-field or production-length counterexample, and not a Lean proof. The covering degree is two, which is compatible with even b=4 and excluded by the companion [covering-multiplicity lemma](astra_mca_cover_multiplicity-2026-09-05.md) at the production odd b.

The [nested-extension obstruction](astra_mca_nested_odd_extension-2026-09-06.md)
also excludes retaining all six locators and adding roots to reach b=5,
n=28, even if the six coefficient points move. It needs only the target
common-domain and balance conditions. Extensions that change the old
incidences remain outside that obstruction.

## Exact degree-two frame over F43

All following coefficients are modulo 43 and listed in ascending polynomial degree, component by component:

    B=((10,18,19), (36,37,40), (17,0,9)),
    C=((6,32,1), (30,3,17), (9,12,20)).

Put w=B cross C and W_i=c_i dot w. The data are:

| i | c_i | Four roots of W_i | Cancellation directions, in that root order |
|---|---|---|---|
| 0 | (1,20,7) | 1,20,22,36 | 30,29,38,19 |
| 1 | (1,39,12) | 0,15,20,39 | 29,5,1,34 |
| 2 | (1,17,13) | 20,29,34,42 | 32,40,6,7 |
| 3 | (1,31,20) | 22,32,39,42 | 14,21,26,41 |
| 4 | (1,29,26) | 1,15,29,32 | 2,17,9,28 |
| 5 | (1,42,30) | 0,32,34,36 | 12,23,35,42 |

Every locator has degree four and exactly the displayed four distinct roots. Divide each W_i and c_i by the leading coefficient of W_i when using monic locators; this changes no root, pair, or cancellation direction. Both checkers verify the normalized locators. Their root union is

    Y={0,1,15,20,22,29,32,34,36,39,42}.

Their gcd is one and their constant span has dimension three. The leading cross product is (2,16,25), so there is no homogeneous basepoint at infinity. The displayed complete splitting and empty common root set rule out every finite geometric basepoint as well.

Every pencil has four distinct finite directions. Of all 24 slots, exactly one direction is repeated across pencils: gamma=29 occurs for pencils 0 and 1. Thus there are 23 distinct directions, all already finite in this chart.

The long absence flats are 012 at y=20 and 345 at y=32. Each of the other nine nodes belongs to one cross pair. Every pairwise locator gcd has degree one at the base.

## Explicit reconstruction, including the degree bound

Let V0(Y)=product_(a in Y)(Y-a). Solve A dot w=V0 with degree A at most seven. One exact solution, again in ascending coefficients, is

    A0=(18,24,32,24,8,23,29,22),
    A1=(21,42,32),
    A2=0.

The checker independently solves the coefficient system and verifies this identity. The bound is seven because this base domain has eleven nodes. One must not use the degree-six Bezout bound from the separate b=2, n=10 reconstruction theorem.

Set N to have rows A,B,C and M=adj(N). Its columns are w, C cross A, A cross B, with degrees at most 4,9,9. The identities NM=MN=V0 I and det M=V0^2 give

    c_i M = W_i(1,f_i,g_i),       deg f_i,deg g_i<=5.

Each quotient is checked by exact polynomial division. At each node a choose any pencil with W_i(a)!=0 and define u(a)=(f_i(a),g_i(a)). All such owners agree, and every absent pencil disagrees as a pair. The checker verifies every one of these assertions directly; the receipt includes all six pairs and received values.

## Quadratic pullback and the actual 22-node RS code

Use rho(X)=X^2+2 and define

    Omega={x in K : rho(x) in Y},
    V(X)=V0(X^2+2),
    F_i(X)=f_i(X^2+2), G_i(X)=g_i(X^2+2),
    received(x)=u(rho(x)).

The branch values 2 and infinity lie outside Y. Each fiber therefore has two distinct finite geometric points. They all split in K: -1 is a nonsquare in F43, so K=F43[i] is a quadratic field, and every equation X^2=a-2 with a in Y splits there. The checker supplies all 22 roots explicitly, verifies their distinctness, and evaluates V on each of them.

The pulled-back B,C have homogeneous degree four and remain independent at every geometric point. Each locator has degree eight and is an actual squarefree divisor of V. The core of each pair has 2*(11-4)=14 nodes. Each of the four base directions is duplicated exactly twice, so all six pencils are saturated. Every pairwise absence intersection has size two, and the two triple flats and nine cross flats each have weight two.

The pairs F_i,G_i have degree at most ten, hence belong to the full RS code of dimension eleven on Omega. No restriction to the smaller space of even polynomials is imposed on candidate joint explanations.

For every listed gamma of pencil i, F_i+gamma G_i agrees with the received scalar word on exactly sixteen nodes: its fourteen-node exact core and the two nodes over its one cancelling base root. This is already a support of the exact required size.

Any joint explaining pair of degree at most ten on that support must equal F_i,G_i on the fourteen-node core, hence must equal them as polynomials. They fail on the additional absent nodes, proving the original no-joint clause. As an independent finite check, the script expands each interpolation system over F43[i] into a base-field F43 system with 22 coefficient unknowns. Every 16-node design has rank 22, while augmenting by either received coordinate has rank 23. The scalar received combination has augmented rank 22. All 24 pencil/scalar witnesses pass these full-code checks. The full received-pair extension has quotient rank two as well.

The union of finite bad scalars is

    {1,2,5,6,7,9,12,14,17,19,21,23,26,28,29,30,32,34,35,38,40,41,42},

of size 23>22. The receipt records every exact support and rank result.

## Complete census over all 1849 field scalars

The following independently audited reduction accounts for arbitrary degree-at-most-ten decoders and arbitrary qualifying supports. It proves that the displayed 23 scalars are the full bad set.

Every degree-at-most-ten polynomial over K has a unique decomposition

    P(X)=E(Y)+X*O(Y), Y=X^2+2, deg E<=5, deg O<=4.

A support of at least sixteen nodes among eleven two-element fibers contains at least five complete fibers. If P agrees with the even received scalar word there, subtracting its values at x and -x gives 2x*O(Y)=0 at those five distinct base nodes. Here x is nonzero and the characteristic is odd. Thus O=0, and the decoder is even. Its complete agreement set consists of entire fibers over at least eight base nodes.

Write gamma=alpha+i*beta and E=U+i*V, with alpha,beta in F43 and U,V over F43. If beta is nonzero, then on every agreeing base node

    V=beta*u1, U=u0+alpha*u1.

Consequently (U-alpha*V/beta,V/beta), composed with Y, jointly explains the original received pair on the original support. Its components have degree at most ten, contrary to the no-joint condition. Every bad scalar is therefore in F43. For gamma in F43, the imaginary part of E vanishes on at least eight base nodes, so it is zero and E is over F43.

For completeness of the support reduction, suppose an MCA witness projects to m>=8 agreeing base nodes. A joint degree-at-most-five explanation on all m would compose to a forbidden joint explanation on the original support. Interpolate both received rows on any six of those nodes. At least one interpolant fails at a seventh node; otherwise the pair would explain all m. These seven nodes certify failed joint interpolation, and adding any eighth agreeing node preserves that failure. Conversely, any eight base nodes admitting a blended degree-at-most-five decoder but no joint explanation give an actual sixteen-node MCA support by taking all fibers. A hypothetical joint degree-at-most-ten pair on those full fibers must be even by the same argument, and must descend to F43 by vanishing of its imaginary parts. It would give the forbidden base explanation.

Thus the exact whole-field MCA census reduces to 43 scalars and all C(11,8)=165 base supports. The main checker interpolates the two received rows on the first six nodes of each support and tests their two residual equations at the last two nodes. It checks all 7095 scalar/support cases. The independent checker instead uses quotient syndromes and direct augmented Vandermonde ranks.

Both computations give exactly the displayed 23-element bad set. Gamma=29 has two qualifying supports; each of the other 22 scalars has one. Every other scalar has none. All 165 base supports fail joint explanation. There are 24 qualifying scalar/support pairs, and no additional bad scalars from other pencils. The error probability on this particular received line is therefore exactly 23/1849 at radius 3/11, giving a lower bound 23/1849 on the worst-case MCA error for this finite instance.

## Exact characteristic boundary for this literal certificate

Lift the displayed B,C,c_i coefficients and the 24 displayed root labels to ordinary integers. Evaluate the corresponding integer polynomial c_i dot (B cross C) at each indicated root. The gcd of the absolute values of all 24 integer evaluations is exactly

    43.

Thus the same literal integer frame, points, and root incidences cannot remain valid in any other prime characteristic. In particular this certificate does not transfer unchanged to the certified production prime. This is not an exclusion of other parameter choices in larger characteristics or other domains.

## Reproduction

Run the two standalone standard-library checkers from the repository root:

```sh
python3 scripts/probes/astra_mca_f43_common_domain_check.py
python3 scripts/probes/astra_mca_f43_common_domain_census_check.py
```

The [construction checker](../../scripts/probes/astra_mca_f43_common_domain_check.py) returns
`PASS_ACTUAL_F43_SQUARED_SIX_PENCIL_23_SCALARS` and prints the exact frame,
received pair, domain, all 24 witness supports, and the full census as JSON.
The [independent checker](../../scripts/probes/astra_mca_f43_common_domain_census_check.py) implements
separate polynomial and extension-field arithmetic, checks all 1848 nonzero
field inverses, and returns `PASS_INDEPENDENT_F43_QUADRATIC_SIX_MCA`.
It obtains full-code design rank 11 and both augmented ranks 12 over F43[i]
for every witness, and reproduces the complete 7095-case census. Both probes
check that the literal integer incidence gcd is exactly 43. Independent
agent review also checked the written completeness and cover arguments;
this is not external human peer review or Lean formalization.

This closes the proposed domain-only six-pencil exclusion in the negative at this even-b, characteristic-43 instance. The production question must retain an additional production-field/domain or birationality condition; neither this example nor the accompanying covering lemma resolves that remaining case.
