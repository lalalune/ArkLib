# One high core and a second core one point shorter already imply safety

2026-09-08. Written proof, not Lean verified. Let n=4s, k=2s, t=3s-1, s>=94, over any field and n distinct evaluation points. Suppose two distinct joint codeword pairs z_0,z_1 have exact joint cores of size at least t and t-1, respectively. Then the number of original same-support MCA-bad scalars is at most n.

This weakens the second-core assumption in the published two-source theorem by one point. It does not assert existence of that second core in the singleton case.

The coordinator and two independent agents reviewed the full written argument.
The rational-list inequalities and polynomial intersection step are now proved in
[Lean](../../scripts/probes/astra_mca_rational_list.lean), including
`degree_two_rational_profile_list_le_four`. Source lifting and the MCA case split
remain written mathematics. The [exact arithmetic check](../../scripts/probes/astra_mca_near_source_check.py)
and [review](../../scripts/probes/receipts/astra_firststep_next_20260908/near-source-review.md)
record their separate verification scopes.

## Shared geometry and rational list

Factor z_1-z_0=H(A,B), with coprime A,B, and d=max(deg A,deg B). The core intersection has size at least t+(t-1)-n=k-3. Hence deg H>=k-3, d<=2, and every pair of codeword sources with this same primitive carrier has core-intersection bound k-1-d, provided its scalar profiles have degree at most k-1-d.

The union U of the selected cores satisfies

    |U| >= t+(t-1)-(k-1-d)=n-2+d.

Let O=D\U and h=|O|<=2-d. On U define the fixed scalar word w by (u,v)-z_0=w(A,B). The known profiles 0,H agree with w on at least t and t-1 points.

For each actual bad scalar gamma choose one original witness support S_gamma and decoder f_gamma. If d>=1, A,B are linearly independent over the field, so T_gamma=A+gamma B is a nonzero polynomial of degree at most d. Define

    R_gamma=(f_gamma-p_0-gamma q_0)/T_gamma.

This rational function agrees with w at every point of S_gamma intersect U where T_gamma is nonzero, hence on at least t-h-d>=t-2=3s-3 points. Add 0,H to the set L of these profiles. Each profile has numerator degree at most k-1 and denominator degree at most d<=2. Distinct profiles have agreement-set intersection at most k+1, by cross multiplication. Therefore five profiles would contradict

    5(3s-3)^2 - n((3s-3)+4(k+1))
      =s^2-94s+45>0.

Thus L is finite with |L|<=4, including its two known distinct profiles.

Call a profile liftable if it is a polynomial of degree at most k-1-d. It defines a valid joint source z_R=z_0+R(A,B) with actual joint core at least t-2. Every nonliftable profile occurs at at most one scalar: for distinct gamma,delta the polynomials T_gamma,T_delta are coprime, and at least one has degree exactly d. A common rational profile must consequently be a polynomial of degree at most k-1-d. This argument includes exceptional lower-degree T_gamma.

For a fixed valid source with actual joint core of size c, its projected original-MCA witnesses account for at most n-c distinct scalars. Indeed a same-support joint-agreement failure supplies a nonzero affine residual cancellation at a point outside that core. No assumption c>=t is needed for this count.

## Degree zero

If d=0, at most one scalar has T_gamma=0. For every other scalar, normalization is a polynomial of degree at most k-1 agreeing with w on at least t-h>=t-2 points. The same five-list estimate, with its deliberately larger pair-intersection bound k+1, bounds the distinct profiles by four.

Every normalized profile defines a valid source. On U a nonzero constant T_gamma makes projection agreement imply joint agreement. Any original MCA witness must therefore contain a nonzero source-residual cancellation at a point of O. Each profile accounts for at most h<=2 scalars. Including the possible zero T_gamma gives |B|<=4h+1<=9<=n.

## Degree two, or degree one with no hole

If d=2 then h=0. The following argument also applies when d=1 and h=0.

If all profiles are liftable, the received pair and every source lie on the same carrier line at every domain point. Any original MCA witness gives a nonzero residual cancellation, hence T_gamma(x)=0 at some coordinate x. Coprimality means each coordinate supplies at most one scalar, so |B|<=n.

If a nonliftable profile exists, at most three profiles are liftable. Beyond the two selected sources, there is at most one extra source, whose core is at least t-2. There are at most two nonliftable profiles, each accounting for one scalar. The source root counts give

    |B| <= (s+1)+(s+2)+(s+3)+2=3s+8<=n.

## Degree one with one hole

It remains to treat d=1 and O={o}. A liftable profile is called strong if its actual joint core is at least t-1; otherwise it is weak. The two selected profiles are strong.

Each weak profile contributes at most one bad scalar. To see this, its core has size at most t-2, so a witness of size at least t has at least two points with nonzero joint residual from this source. Within U such residuals are parallel to (A,B) and projection agreement requires T_gamma(x)=0, which occurs at at most one point. Therefore the witness must contain o with nonzero residual cancellation. For a fixed source this determines at most one gamma.

Nonliftable profiles also contribute at most one scalar. If there are at most three strong profiles, the two selected sources and the possible additional strong source contribute at most

    (s+1)+(s+2)+(s+2),

while the at most two other profiles contribute at most two scalars. Thus |B|<=3s+7<=n.

Suppose instead that there are four strong profiles. Then all profiles are liftable and their four sources have cores of sizes at least t,t-1,t-1,t-1. Their pairwise intersections are at most k-2, since their scalar polynomials have degree at most k-2 and the carrier is primitive.

At least one of these four cores contains o. Otherwise all cores lie on N=n-1 points. Write r_x for their membership multiplicity and R=sum_x r_x. Then

    R>=t+3(t-1)=12s-7,
    sum_x binom(r_x,2)<=6(k-2)=12s-12.

But the integer inequality binom(r,2)>=2r-3 holds for every r=0,1,2,3,4. Consequently

    sum_x binom(r_x,2)>=2R-3N>=12s-11,

a contradiction. This integer incidence bound is stronger here than the continuous Cauchy estimate.

Thus the four cores cover D: U is already covered by the first two and one of the four covers o. The received pair is now on the same carrier line as all sources at every coordinate. Every chosen bad witness is a projection of one of them. The same coordinate direction count gives |B|<=n.

## Consequence for the remaining singleton branch

At production parameters, an unsafe instance with a source core at least t can have **no distinct joint source with core at least t-1**. This is an unconditional reduction of the remaining singleton problem, not a proof that such a source must exist.
