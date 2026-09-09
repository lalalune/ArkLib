# Two-source first-step closure by a normalized rational-function list

2026-09-08. Written proof and exact arithmetic; not Lean verified. Parameters n=4s, k=2s, t=3s-1, s>=52, over any field and n distinct evaluation points. The production parameter s=2^28 meets this bound. Assume there exist two distinct joint codeword pairs with cores of size at least t. No assumption excludes additional high-core pairs. This proof does not settle cases with no such pair or only one.

Let z_0=(p_0,q_0), z_1=(p_1,q_1) be the two selected sources, with exact joint cores A_0,A_1 of size at least t. Put B_cov for actual MCA scalars admitting a witness decoder projected from either selected source, and B_exc=B\B_cov. The source-core-plus-one argument gives |B_cov|<=2(s+1); a polynomial projection collision of the two sources is itself covered.

## Primitive carrier and near-total core coverage

Factor the componentwise gcd:

    z_1-z_0 = H(A,B),  gcd(A,B)=1,
    d=max(deg A,deg B), deg H+d<=k-1.

The cores overlap on at least 2t-n=k-2 points. At each such point H vanishes, because the primitive carrier A,B has no simultaneous zero. Hence deg H>=k-2 and d<=1. Moreover

    |A_0 intersect A_1|<=k-1-d,
    |U|=|A_0 union A_1| >= 2t-(k-1-d)=n-1+d.

On U define a scalar word w by

    (u,v)-z_0 = w(A,B).

It is well-defined because (A(x),B(x)) is never the zero vector. The two known polynomial profiles are 0 and H; on their respective source cores, w equals those polynomials.

When d=1, the inequalities force U=D, |A_0|=|A_1|=t, |A_0 intersect A_1|=k-2 and deg H=k-2. When d=0, U misses at most one point.

## Constant carrier d=0

Outside B_cov, T_gamma=A+gamma B is a nonzero constant, since T_gamma=0 would make the two source projections collide. Choose one original MCA witness support S_gamma and decoder f_gamma for each exceptional gamma. The polynomial

    R_gamma=(f_gamma-p_0-gamma q_0)/T_gamma

has degree at most k-1 and agrees with the fixed word w on S_gamma intersect U, at least t-1=3s-2 points. Distinct such polynomials have agreement-set intersections at most k-1. There are at most four such polynomials: the five-set incidence inequality already fails on n points, since

    5(3s-2)^2 - (4s)((3s-2)+4(2s-1))
      = s^2-36s+20 > 0  (s>=52).

Using n rather than |U| only weakens this upper bound.

For each such R, the pair z_R=z_0+R(A,B) is a valid joint codeword pair. On U, projection agreement at a scalar with T_gamma nonzero implies joint agreement with z_R. An original MCA witness projected from z_R must therefore have a point outside U at which the joint residual is nonzero and the scalar residual cancels. If U=D this is impossible. Otherwise there is just one outside point o, and for each fixed R its nonzero residual at o cancels at at most one scalar. Thus |B_exc|<=4, and

    |B|<=2(s+1)+4<=n.

## Linear carrier d=1: normalize all decoders, not only exceptional ones

Here U=D, so the scalar word w is defined on the entire domain. A,B are linearly independent over F: if dependent and d=1, they would have a common linear factor. Thus every T_gamma=A+gamma B is a nonzero polynomial of degree at most one. For distinct gamma,delta, T_gamma and T_delta are coprime, and at least one is nonconstant.

Choose one original MCA witness support S_gamma and decoder f_gamma for **each actual bad scalar**, choosing a source-projected witness for those in B_cov. Form the rational function

    R_gamma=F_gamma/T_gamma,
    F_gamma=f_gamma-p_0-gamma q_0, deg F_gamma<=k-1.

At points of S_gamma where T_gamma is nonzero, R_gamma=w. There are at least t-1 such points, because T_gamma has at most one root. If a common factor cancels in the rational function, this assertion remains valid; extra removable points are not needed.

Consider the set L of these rational functions, together with the two known polynomial profiles 0,H. Every profile in L has a representation with numerator degree at most k-1 and denominator degree at most one, and agrees with w at at least

    r=t-1=3s-2

domain points where it is defined. For two distinct rational functions, the cross-multiplied numerator is a nonzero polynomial of degree at most k. Their agreement sets therefore intersect in at most k points. Five distinct profiles would violate the ordinary incidence bound, because

    5r^2-n(r+4k)=s^2-52s+20>0  (s>=52).

Consequently L cannot contain five distinct elements, so it is finite and **|L|<=4**, even if the ambient field is infinite. L contains the distinct profiles 0 and H. This is a list bound for a single fixed scalar word, not an assumed rational family of decoders.

### Liftable profiles

Call a profile R liftable if it is a polynomial of degree at most k-2. Then

    z_R=z_0+R(A,B)

is a valid joint RS pair. Its exact joint core is exactly {x:w(x)=R(x)}, because the primitive carrier is nonzero at each point. That core has size at least r=t-1. The two base profiles have core size at least t.

If all bad scalars have liftable profiles, then every witness decoder is a projection of such a source. At every coordinate the received pair and every source z_R lie on the same carrier line. The MCA same-support obstruction supplies a point where the residual pair is nonzero but its projection vanishes. Thus each bad gamma solves

    A(x)+gamma B(x)=0

at some x in D. At each x there is at most one such gamma. Hence |B|<=n, without requiring a core cover by the additional sources.

### Nonliftable profiles each cost only one scalar

A nonliftable rational profile can occur at **at most one scalar**. Indeed, if R=F_gamma/T_gamma=F_delta/T_delta for distinct gamma and delta, write R in reduced form. Its denominator divides both coprime T_gamma and T_delta, so R is a polynomial. At least one of T_gamma,T_delta has degree one; since its product with R has degree at most k-1, R has degree at most k-2. This contradicts nonliftability.

This also handles the possible scalar at which T_gamma is constant: a high-degree polynomial profile there is nonliftable, but cannot recur at a different scalar.

If a nonliftable profile exists, at most three of the at most four profiles are liftable. Since 0,H are already liftable, there is at most one additional liftable profile. The two base source pencils contribute at most 2(s+1) bad scalars. The possible additional source, with core at least t-1, contributes at most s+2: the ordinary source residual-root count does not require its core to reach t. Finally there are at most two nonliftable profiles, hence at most two nonliftable bad scalars. Therefore the deliberately loose bound is

    |B|<=2(s+1)+(s+2)+2=3s+6<=n.

The profile-cap constraint would allow a slightly sharper constant; none is needed.

## Outcome

For s>=52, **the full original same-support MCA scalar count is at most n whenever two distinct such high-core joint pairs exist**, for either primitive-carrier degree. Together with the [three- and four-source arguments](astra_mca_first_step-2026-09-08.md), the unhandled high-core-list cardinalities are zero and one. Agent10 independently reviewed this entire proof and found no gap, including the constant-denominator edge case and rational evaluation domains. This is a reviewed written proof awaiting formalization; it is not a universal first-step theorem.

The proof only uses the two selected pairs. It therefore subsumes the earlier
three- and four-source branches; this strengthened scope was independently
reviewed as well.
