# Saturated cancellation fibers force a birational production locator map

This is a written general lemma about the actual balanced-locator reconstruction. It is not Lean-formalized and does not settle the remaining birational case. Its proof has an independent mathematical audit.

## Statement

Use an actual common squarefree domain Omega of n=6b-2 finite K-rational nodes, with the six degree-2b monic locators W_i, their primitive three-dimensional span w, and balanced degree-b homogeneous syzygy rows B,C. Write W_i=c_i dot w. Let

    phi=[w]:P1 -> P2,
    phi=eta after rho,
    nu=degree rho,

where eta parametrizes the normalization of the image. Let r_i(gamma) denote the number of roots x of W_i carrying cancellation direction gamma in P1(K), including infinity. Then

    nu divides b,
    nu divides r_i(gamma) for every i and every projective gamma.

Here a saturated pencil has b distinct finite directions of multiplicity
at least two. Those directions consume all 2b roots, so each has
multiplicity exactly two and no roots carry other directions.

Consequently even one direction occurring exactly twice forces nu|2. In particular, one saturated pencil forces nu|2. When b is odd, one saturated pencil forces nu=1: the full locator map is birational, with no additional flat-weight hypothesis.

At production b=178956971 is odd. Thus this applies to any saturated pencil in an actual equal-core, full-cover, noncollinear six-pencil configuration, rather than only the previously considered incidence models having a flat of weight two.

An over-budget union from these six pencils has at least 6b-1 directions.
Since each pencil supplies at most b, at least five pencils must be
saturated. Thus every such production certificate is necessarily
birational. This does not classify arbitrary MCA witnesses as six pencils.

## Descending the homogeneous frames

The normalization factorization and bundle-degree argument are the ones established in the [balanced-bundle argument](astra_mca_six_locator_birationality-2026-09-04.md). Over K, Luroth gives a rational normalization. Write eta^*O(1)=O(e). If its evaluation kernel splits as O(-a) plus O(-c), then pullback gives

    O(-b) plus O(-b) = O(-nu*a) plus O(-nu*c).

Uniqueness of splitting degrees gives a=c=b/nu, so nu|b. Write m=b/nu. Choose homogeneous degree-m rows B0,C0 giving a basis of that descended kernel, and represent rho by coprime homogeneous forms R0,R1 of degree nu.

The rows B0(R0,R1),C0(R0,R1) have degree b and form a basis of the pulled-back kernel. The actual B,C are another such degree-b basis. Since the global sections of the kernel twisted by O(b) have dimension two, the two bases differ by a constant GL2(K) matrix. In particular no X-dependent change of cancellation parameter is introduced.

For x over y under rho, evaluating R0,R1 chooses a representative of y multiplied by a nonzero scalar. Homogeneity gives the SAME scalar power on B0 and C0 because they have the same degree m. This common evaluation factor disappears in projective direction comparisons. The argument remains valid when y is the point at infinity on the normalization: homogeneous evaluation uses (1,0), rather than an affine coordinate denominator.

The residual-direction formula proved in the [reconstruction note](astra_mca_locator_reconstruction-2026-09-05.md) says

    c_i is proportional to T*C(x)-S*B(x)

for the unique cancellation direction [S:T] at a root of W_i. The constant frame change and the common evaluation scale show that this direction depends only on y=rho(x). Thus it is constant on every rho-fiber contained in the locator roots.

## Every relevant cover fiber consists of exactly nu domain nodes

Let ell_i=c_i dot Z be the linear section of O_P2(1) defining the i-th locator line, and let eta^*ell_i be its descended section on the normalizing P1. The zero divisor of the degree-2b homogenization of W_i is the pullback of the zero divisor of eta^*ell_i. Take any root y of that descended section, and any geometric x over y. Then W_i(x)=0 and

    1=ord_x(W_i)=e_x(rho)*ord_y(eta^*ell_i).

The first equality uses squarefreeness of the actual locator. Both factors on the right are positive integers, so both equal one. The degree formula for the pullback of a point now shows that this entire geometric fiber contains exactly nu distinct points. This argument also rules out an inseparable contribution; separability need not be assumed beforehand.

All these preimages are roots of W_i. Since W_i splits on the actual finite K-rational domain, every one is K-rational. No preimage can be the source point at infinity, because the monic degree-2b locator is nonzero there. Thus the entire fiber is a nu-element subset of Omega. This checks the full fiber, not merely a single chosen rational preimage.

Combining this with direction constancy, each projective direction fiber is a disjoint union of nu-element cover fibers. Hence nu divides every r_i(gamma), including the infinity direction.

## A quantitative bound for the selected six pencils

Let E_i be the finite directions with multiplicity at least two. Each such fiber has size at least max(2,nu), while the total slot count is 2b. Therefore

    |E_i| <= floor(2b/max(2,nu)),
    |union_i E_i| <= 6*floor(2b/max(2,nu)).

This counts only scalars supplied by the six selected pencils. It does not bound additional pencils of the received pair.

At production no integer from 2 through 58 divides b, while

    b=59*3033169.

Thus every nontrivial cover degree nu dividing b is at least 59. Any such nonbirational configuration supplies at most

    6*floor(2b/59)=36398028

finite bad scalars through these six pencils. The bound supplies no new estimate when nu=1.

## A sharp even-b control on a genuine common domain

The companion [common-domain construction](astra_mca_f43_common_domain_counterexample-2026-09-05.md) and its [checker](../../scripts/probes/astra_mca_f43_common_domain_check.py) construct an actual b=4, n=22 RS example over F43 squared with six saturated pencils and 23 distinct finite bad scalars. Its frame is a degree-two pullback of a primitive balanced degree-two frame. The base first and second locators have gcd Y-20, so their common-zero fiber has degree one and the base locator map is birational. The full map therefore has covering degree exactly two.

Every base slot is duplicated twice, exactly as the lemma predicts. In particular nu=2 cannot be excluded at even b, even with a genuine common domain, all six saturated pencils, pairwise absence intersections b-2, and an over-budget scalar union. This control is in characteristic 43 on a non-cyclotomic domain, not at the production field or length.

The checker also verifies the integer divisibility and scalar-count arithmetic above. The general covering lemma is the written proof, not a conclusion inferred from the finite control.

Reproduce the exact degree-two control and production divisor arithmetic with
`python3 scripts/probes/astra_mca_f43_common_domain_check.py`. The independent full-code and census checker is
`python3 scripts/probes/astra_mca_f43_common_domain_census_check.py`.
