# Exact reconstruction from balanced common-domain six locators

This is a written algebraic converse to the [necessary locator conditions](astra_mca_six_locator_consistency-2026-09-04.md) and [balanced-syzygy conditions](astra_mca_six_locator_birationality-2026-09-04.md). It is not Lean-formalized, a production construction, or an exclusion. It retains the actual common squarefree domain polynomial; the [unconstrained six-square countermodel](astra_mca_six_square_countermodel-2026-09-05.md) does not satisfy its hypotheses. The accompanying standard-library checker verifies bounded controls, not the general theorem.

## Precise input certificate

Let K be any field, b>=1, n=6b-2, d=3b-2, and let V be the monic polynomial of n distinct K-rational domain nodes Omega. Suppose six distinct monic polynomials W_i satisfy:

1. Each W_i divides V and has degree 2b.
2. Their K-linear span has dimension three, and gcd(W_1,...,W_6)=1.
3. For one polynomial basis w=(w_1,w_2,w_3)^T of that span there are rows B,C of polynomial degree at most b such that B cross C=w. A nonzero constant multiple may be absorbed into B.

Write W_i=c_i dot w with constant nonzero row c_i. Condition 3 is a concrete certificate for the balanced syzygy splitting already proved necessary in the six-locator birationality note. As w has degree 2b, the degree-b leading vectors of B,C are independent. The primitive cross product makes B,C independent at every finite geometric point; their leading vectors give independence at infinity.

These hypotheses are sufficient to construct two received words and six distinct polynomial pairs of component degree at most d whose exact joint cores are Omega minus the roots of W_i. Their full configuration is noncollinear over K(X). No additional interpolation-kernel existence hypothesis is required.

The balanced condition also has a single exact determinant certificate: the square coefficient map

    T_w: (K[X]_{<=b-1})^3 -> K[X]_{<=3b-1}, R -> R dot w

of size 3b is invertible if and only if condition 3 holds. Given B,C, the polynomial-syzygy argument below shows that there is no nonzero syzygy of degree less than b, proving invertibility. Conversely, at degree b there are 3b+3 unknown coefficients and at most 3b+1 equations, so the kernel contains two K-linearly independent rows. If these are dependent over K(X), both are polynomial multiples of a common primitive row; two independent multiples force that row's degree to be at most b-1, contradicting invertibility of T_w. Hence two rows B,C are independent over K(X). Their cross product is h w with h in K[X], by primitivity of w; degrees at most 2b force h to be a nonzero constant. Rescaling gives condition 3. This supplies a finite certificate for a particular locator triple, not a uniform production nonvanishing theorem. At production the matrix has 536870913 rows.

## Bounded Bezout row exists

Put t=4b-2 and consider the K-linear map

    L: (K[X]_{<=t})^3 -> K[X]_{<=6b-2},   A -> A dot w.

Every polynomial syzygy R dot w=0 has a unique representation R=aB+cC with a,c in K[X]. Over K(X) the representation is unique because B,C are independent and span the orthogonal complement of w. To see its coefficients are polynomials, localize at each irreducible q: one coordinate of w is a unit there, since gcd(w)=1; the corresponding two-by-two minor of B,C is a unit. Solving with those two coordinates puts a,c in K[X]_(q). Thus they have no irreducible denominator.

The independent leading vectors imply

    deg(aB+cC)=b+max(deg a,deg c)

for a nonzero combination. In particular, the kernel of L has dimension 2(t-b+1)=2(3b-1). Its rank is therefore

    3(t+1)-2(t-b+1)=6b-1,

which is exactly the target-space dimension. Hence L is surjective. Choose A with deg A<=4b-2 and A dot w=V. This is an explicit finite coefficient linear system, not an additional assumption.

## Adjugate reconstruction and all degree bounds

Set N to have rows A,B,C and put M=adj(N). Then

    det N=A dot (B cross C)=V,
    NM=MN=V I,
    det M=V^2.

The columns of M are w, C cross A, A cross B, with degrees at most 2b,5b-2,5b-2. Define Q_i=c_i M. Its first component is W_i.

At a domain node x, rows B(x),C(x) are independent and det N(x)=0, so N(x) has rank exactly two. Thus M(x) has rank exactly one. Its first column w(x) is nonzero and spans its image, so every row combination c_i M(x) vanishes whenever W_i(x)=c_i w(x)=0. Since W_i is squarefree and splits, W_i divides all three components of Q_i. Consequently

    Q_i=W_i(1,f_i,g_i),
    deg f_i,deg g_i <= (5b-2)-2b=3b-2.

At each x, some W_j(x) is nonzero. The rank-one matrix with first column w(x) has a unique presentation M(x)=w(x)(1,u_0(x),u_1(x)). All present pairs therefore agree with u at x.

Exactness of each absence is also automatic. The polynomial identity Q_i N=V c_i gives

    W_i(A+f_i B+g_i C)=V c_i.

At an absent node x, differentiating and then using any present owner yields

    W_i'(x)[(f_i(x)-u_0(x))B(x)+(g_i(x)-u_1(x))C(x)]=V'(x)c_i.

Both derivatives are nonzero, and c_i is nonzero. Hence the residual pair is nonzero. Each exact core has n-2b=4b-2 nodes. Distinct W_i give distinct exact cores, hence distinct pairs. Three independent c_i have determinant of their Q rows equal to a nonzero constant times V^2. Dividing by W_i proves that the corresponding three pairs are noncollinear over K(X).

## Reconstruction choices do not hide extra freedom

If A_tilde is another row of the same degree bound with A_tilde dot w=V, the kernel description gives

    A_tilde=A+aB+cC,    deg a,deg c<=3b-2.

The adjugate changes every pair by the same translation

    (f_i,g_i) -> (f_i-a,g_i-c),

and changes the received word by that same translation. Every residual vector is unchanged. Thus the choice of the bounded Bezout solution has no influence on cancellation directions, saturation, or bad-scalar overlap. Likewise any other degree-b syzygy basis differs by a constant GL_2(K) change, so it only changes the common projective chart on residual directions.

## Exact scalar and no-joint conclusion

For every absent node, define gamma_i(x)=-e_0(x)/e_1(x) if e_1(x)!=0 and gamma_i(x)=infinity otherwise. The displayed derivative identity computes this direction from B,C,c_i alone: c_i is proportional to C(x)-gamma B(x) for a finite gamma, with the corresponding projective interpretation at infinity.

No pole-free chart is asserted for an arbitrary field. If |P^1(K)|>12b, there is a projective direction outside the at-most-12b absent slots; sending it to infinity by a common GL_2(K) change makes every absent direction finite. This field-size condition holds at production. The following criterion retains infinity explicitly and does not require that optional chart change.

For finite gamma, let r_i(gamma) be the number of absent nodes carrying it. Then f_i+gamma g_i has exactly 4b-2+r_i(gamma) agreements. It gives an MCA witness at support 4b exactly when r_i(gamma)>=2.

For the no-joint clause at the exact target size, take S to consist of the whole exact joint core and any two absent nodes carrying gamma. It has size 4b. Any candidate joint explaining pair of degree at most d agreeing with the received pair on S must equal (f_i,g_i), by polynomial uniqueness on the core of size 4b-2>d. Its additional absent nodes make this impossible. The same argument also applies to the full agreement support. Thus each counted scalar is a genuine same-support/no-joint witness at size 4b.

Define E_i={finite gamma: r_i(gamma)>=2}. These sets certify at least n+1 distinct bad scalars exactly when |union E_i|>=6b-1. This does not assert that these are all bad scalars of the constructed received pair; other pencils could supply additional ones. As each |E_i|<=b, the original at-most-one deficit/overlap condition remains necessary for the six pencils to certify that count. In particular at least five have b distinct finite fibers, each of size exactly two; resultant squares alone still omit splitting, squarefreeness, infinity, and cross-pencil overlap checks.

Together with the previously proved forward implication, this gives an exact locator-and-direction certificate for an over-budget configuration of this equal-core, full-cover, noncollinear six-pencil form. It does not reduce every possible production counterexample to this form.

## Explicit bounded controls

For b=1,2,3,4 choose a field containing mu_(4b), four values r in mu_4, and use

    B=(1,X^b,0), C=(0,1,X^b), w=(X^(2b),-X^b,1),
    c_(r,s)=(1,r+s,rs),
    W_(r,s)=(X^b-r)(X^b-s),

for all six unordered pairs {r,s}. Set Omega to mu_(4b) together with 2b-2 arbitrary distinct extra field elements. This is an actual common domain of exactly n nodes. Each locator divides its V and the six span three dimensions. The checker solves the bounded Bezout system rather than assuming its solution, constructs M and every pair, and checks exact cores, polynomial degrees, both adjugate identities, derivative directions, and each finite bad scalar against the original no-joint linear-rank condition.

For each pair, one group of b slots has gamma=-1/r and the other has gamma=-1/s. At b=1 there are no bad scalars. At b=2 all six pencils are saturated, but their scalar sets overlap and their union has only four values. At b=3,4 each supplies two values with slot multiplicity b, again only four values in the union. Thus these are positive reconstruction controls, and explicitly fail the over-budget condition. The b=2 control is useful: actual domain membership plus all six full square conditions does not eliminate the need to check cross-pencil scalar overlap.

The fields are the certified production prime for b=1,2,4 and F_37 for b=3. Only b=1 uses the complete dyadic subgroup as its whole Omega; the others use the displayed common domain with added nodes. No small-field or arbitrary-domain conclusion about the production subgroup is inferred.

Run `python3 scripts/probes/astra_mca_locator_reconstruction_check.py`. It returns PASS_BALANCED_DOMAIN_LOCATOR_CONVERSE, with coefficient-map ranks 5,11,17,23, reconstructs 24 polynomial pairs, and independently checks 36 same-support/no-joint MCA witnesses. The bounded Bezout dimensions and the general converse are proved above, not by those finite controls.

An independent agent audit verified the converse and the determinant equivalence. Its separate arithmetic reconstructed b=1 over F7 and b=2 over F17 on different domains, checking both adjugate products and 21 exact-support no-joint witnesses across two charts. This is independent agent review, not external human peer review or Lean formalization.

The [common-composition exclusion](astra_mca_near_power_locator_exclusion-2026-09-05.md)
rules out all 27 production binary scales with a positive proper remainder
factor, when all six locators have that factorization at the same scale.
The balanced determinant condition also rules out a pure common quadratic
composition because production b is odd. These restrict possible input
certificates; they do not show that every certificate has either shape.
