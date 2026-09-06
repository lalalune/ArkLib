# Nested odd steps from a quadratic six-locator example are impossible

The [genuine b=4, n=22 example over F43 squared](astra_mca_f43_common_domain_counterexample-2026-09-05.md) cannot be extended to b=5, n=28 merely by retaining every old locator root and adding new roots. This obstruction allows the six target coefficient points to move. It already follows from the target common-domain, span, primitivity, and balance conditions; it does not need saturation or a scalar-overlap hypothesis.

A second, general agreement bound shows that with the coefficient configuration fixed up to one projectivity, a b=4 to b=5 extension must change the two-incidence condition at at least nine of the 22 old nodes. Retaining all old roots in that more restrictive family excludes every new b from 5 through 13.

These are written algebraic obstructions, independently audited and supported by exact finite controls. There is no new odd-b MCA candidate and no production conclusion. In particular, neither statement excludes extensions that sufficiently change the old absence incidences.

## General balanced-map agreement bound

Let w and v be primitive triples of homogeneous binary forms of degrees 2b and 2c, respectively. They define morphisms P1 -> P2. Assume both triples are balanced: w has two independent homogeneous syzygies B,C of degree b, and every nonzero homogeneous syzygy of v has degree at least c. Require the corresponding condition after interchanging w and v. A balanced Hilbert--Burch frame, or the invertible square coefficient map in the [reconstruction theorem](astra_mca_locator_reconstruction-2026-09-05.md), supplies these conditions.

If the two projective maps are distinct, their number R of distinct geometric agreement points satisfies

    R <= min(2b+c,b+2c) = b+c+min(b,c).

To prove this, work over an algebraic closure if necessary, and let H be the product of the R linear forms for the agreement points. At each such point B dot v and C dot v vanish. Hence

    B dot v = H p, C dot v = H q,
    deg p = deg q = b+2c-R

when these homogeneous polynomials are nonzero. If the displayed degree is negative, both products vanish identically. If p=q=0, rational independence of B,C implies v is rationally proportional to w. Primitive homogeneous coordinate triples representing the same map differ by a nonzero constant and have the same degree; this is the excluded identical-map case.

Otherwise qB-pC is a nonzero syzygy of v. It is nonzero because B,C are independent over the rational function field. Its homogeneous degree is 2b+2c-R. Balance of v implies c<=2b+2c-R, giving R<=2b+c. Reverse the roles to obtain the other inequality. The use of homogeneous H includes source infinity without an affine degree exception.

An invertible constant target change preserves all hypotheses. Thus the bound also applies after any one global target projectivity. It does not identify two independently moving six-point configurations.

For the old b=4 locator map and a distinct new b'=5 map, R<=13. At an old node where two independent old coefficient rows annihilate both maps, their projective values agree: those rows cut out one point in P2. All 22 old nodes in the fixture originally have at least two such incidences. At least nine must therefore lose this condition in a fixed-configuration extension. Each affected node loses at least one old absence incidence, and a triple node may require more.

More generally, if all 22 old incidences are retained and b'>4, then 22<=8+b', so b'>=14. The first odd b not excluded by this particular fixed-configuration bound is 15. This is only a necessary condition, not an existence claim at 14 or 15.

## General one-step theorem, allowing target-point motion

Let K be a field and r>=1. Let psi(X) be monic quadratic. Let Lambda be 6r-1 distinct K-rational base nodes such that every fiber psi(X)=y, for y in Lambda, consists of two distinct finite K-rational points. Thus the old domain Omega has 12r-2 points.

Suppose six pairwise nonproportional degree-2r polynomials F_i(Y), split and squarefree on Lambda, have a primitive three-dimensional span with basis w0. Assume:

1. w0 has a balanced degree-r syzygy basis B0,C0.
2. Every five of the F_i span three dimensions. As shown below, this also follows from their balance and common base domain of size 6r-1.
3. At every base node y, at least two independent coefficient rows c_i, defined by F_i=c_i dot w0, vanish on w0(y).

Set old W_i(X)=F_i(psi(X)), corresponding to old b=2r. There do not exist six pairwise nonproportional target locators L_i satisfying all the following:

* deg L_i=4r+2=2b', with b'=2r+1;
* L_i divide one squarefree domain polynomial V' of degree 12r+4=6b'-2;
* the L_i span three dimensions, have overall gcd one, and have balanced syzygy degree b';
* every old locator is retained as a divisor: W_i divides L_i, with the same labeling.

No separate pairwise gcd bound, saturation, finite-chart, or scalar-overlap assumption is needed. The target extra nodes are arbitrary. The target coefficient rows may change freely; they need not be projectively equivalent to the old rows.

### Balance bounds pairwise gcds; the actual domain excludes five on a line

Any two independent degree-2b' members L_i,L_j of a balanced target span have gcd degree at most b'. Indeed, extend them to a basis of that span. If G is their gcd, then (L_j/G,-L_i/G,0) is a nonzero syzygy of degree 2b'-deg G. Balance forces that degree to be at least b'. A constant basis change does not change syzygy degrees.

Five distinct equal-degree d polynomials in a two-dimensional pencil have one common pairwise gcd G: any two independent pencil members generate the same ideal. Their quotients by G are pairwise coprime. Therefore the lcm of the five has degree

    5d-4*deg G.

For the target d=2b' and deg G<=b', this is at least 6b'=deg V'+2, impossible when all five divide V'. Thus no five of the target projective coefficient rows lie on a line. Their rows are pairwise distinct by the stipulated pairwise nonproportional target locators.

The same argument applies to the base span with syzygy degree r. Five degree-2r base locators in a pencil would have lcm degree at least 6r, exceeding the 6r-1 base nodes. Thus the old five-span condition is automatic from the other hypotheses; it is listed explicitly to make the rank-two case easy to check.

This is where actual common-domain membership is used. Arbitrary square resultants do not imply this restriction.

### Separate the even-module and odd-module parts

Choose a primitive polynomial basis v(X) of the target span and write L_i=d_i dot v. Because psi is monic quadratic, K[X] is a free K[Y]-module with basis 1,X under Y=psi(X). Leading degrees 2j and 2j+1 give the unique decomposition

    v(X)=E(Y)+X O(Y), deg E<=2r+1, deg O<=2r.

The nesting F_i(psi) | L_i implies divisibility of each module component:

    F_i | d_i dot E, F_i | d_i dot O.

Since deg F_i=2r, there are constants lambda_i with

    d_i dot O = lambda_i F_i.

Let s be the dimension of the K-span of the three component polynomials of O.

If s=2, the annihilator of O is one projective point. At most one of the six distinct target rows d_i annihilates O. At least five nonzero lambda_i F_i would therefore lie in a two-dimensional polynomial space, contradicting assumption 2.

If s=1, all nonzero polynomials d_i dot O are proportional. Since the six F_i are pairwise nonproportional, at most one lambda_i is nonzero. At least five target rows then lie in the projective line annihilating O, contradicting the actual-domain consequence above.

If s=3, no lambda_i vanishes. The span of O equals the span of the F_i, so O=G w0 for an invertible constant matrix G, and

    d_i G=lambda_i c_i.

Write E0=G^{-1}E. The first component divisibilities give F_i | c_i dot E0. At every base node, two independent old coefficient rows annihilate E0(y) and w0(y). Consequently E0(y) is proportional to w0(y), allowing E0(y)=0. Both B0 dot E0 and C0 dot E0 vanish at all 6r-1 base nodes, but their degrees are at most

    r+(2r+1)=3r+1 < 6r-1, since r>=1.

They vanish identically. The primitive cross product then gives E0=h(Y)w0 for a polynomial h of degree at most one. Hence

    v(X)=G[(h(psi(X))+X)w0(psi(X))].

The scalar factor h(psi(X))+X is nonconstant: its coefficient of X in the free module basis is one. This contradicts overall gcd one.

Finally, if s=0, the target basis is E(psi). Three outer polynomials of degree at most 2r+1 have a nonzero syzygy of degree at most r, because the coefficient map has source dimension 3(r+1) and target dimension at most 3r+2. Substitution gives a nonzero target syzygy of degree at most 2r<b'=2r+1, contradicting target balance.

All four cases fail. This proves the theorem in every characteristic satisfying the stated split, squarefree quadratic-domain hypotheses. The proof itself uses module decomposition, so it does not assume that psi is X^2 plus a constant.

## The F43 squared fixture meets every old hypothesis

Take r=2, psi=X^2+2 and

    B0=((10,18,19),(36,37,40),(17,0,9)),
    C0=((6,32,1),(30,3,17),(9,12,20)),

with ascending coefficients per component, and the six rows and root sets from the established example. The base union is

    {0,1,15,20,22,29,32,34,36,39,42}.

Each of nine nodes has two incidences, and 20 and 32 have three. Every five locators span three dimensions. The degree-two balance matrix has rank six. The two branch values 2 and infinity are absent; all 22 preimages split over F43[i], i^2=-1. The lifted degree-four balance matrix has rank twelve.

It follows that no b=5,n=28 locator certificate with the requested common-domain, balance, saturation, pairwise gcd<=3, and at-most-one-overlap conditions can contain all six old locators as divisors. This remains true after arbitrary motion of the six coefficient points. The theorem excludes the necessary locator data, so there is no new received pair or no-joint claim to verify. The original b=4 same-support/no-joint witnesses remain the previously certified example.

## Exact controls and sharpness

Run `python3 scripts/probes/astra_mca_nested_odd_extension_check.py`. The deterministic JSON output has status `PASS_NESTED_ODD_STEP_OBSTRUCTION_CONTROLS`. It checks the actual old domain, both balance matrices, every five-locator span, and the divisibilities used above.

It also computes the complete fixed-configuration linear incidence spaces. For a vector v of maximum degree D retaining all old roots, the nullities are 3,5,7,9,13 at D=10,12,14,16,18. The space is the polynomial module generated by

    w, C cross A, A cross B,

where A dot w=V. Its generator degrees are 8,18,18, and the leading coefficient matrix is invertible. Indeed, if B dot v=Vp and C dot v=Vq, subtracting p(C cross A)+q(A cross B) leaves a polynomial multiple of primitive w. The determinant of the generator matrix is V^2. These checks expose the first nontrivial fixed-configuration incidence deformations at degree 18; balance still excludes those as new b=9 configurations by the general agreement bound.

Two controls show that the general agreement bound is sharp. Over F43, w=(1,X,X^2) and v=(1+X,2X,3X^2-X) are balanced degree-two maps agreeing exactly at 0,1,infinity, attaining R=3 for b=c=1. The checker includes the homogeneous infinity condition.

For unequal degrees, put H=X(X-1)(X-2)(X-3) and v=(1+H,X,X^2+H). It is primitive and balanced of degree four, and agrees with w exactly at 0,1,2,3, attaining R=4 for b=1,c=2. To see balance directly, a degree-at-most-one syzygy forces its first and third coefficients to sum to zero from the degree-four and degree-five terms. The remaining identity is R0(1-X^2)+R1 X=0, which has no nonzero solution with both coefficients of degree at most one. These sharp controls concern projective maps only; they are not asserted to be MCA instances.

Independent agent review audited the balanced agreement proof and each of the four target-motion rank cases. A separate finite-field implementation also checked both sharp examples and eighty bounded balanced-map pairs. This is not Lean formalization or external human peer review.
