# First-step MCA safety: covered scalars, a safe branch, and genuine exceptions

2026-09-08. Repository HEAD inspected: `7941e60694f77346c0e375548737f8301695b8b3`.
Reviewed written proofs and exact arithmetic probes establish the first-step bound when the full high-core list has two, three, or four sources. Zero-source and singleton cases with dense directions remain open. No Lean verification is claimed for these safety arguments.

## Parameters and security target

Let `P=365375409332725729550921208179070755120141565953`,
`n=2^30=4s`, `s=2^28`, and `k=2s`. Let `D` be the certified subgroup,
and `C=RS(D,k)` with polynomial degree strictly below `k`.
The integer bad-scalar budget is **exactly n**:

`n*2^128 < P < (n+1)*2^128`.

At radius `delta_1=(s+1)/n`, the MCA support threshold is
`t=3s-1=805306367`. This is the first support threshold not covered by
the existing UDR theorem plus its half-open Hamming plateau. The existing
safe plateau ends at `delta_1`; its endpoint safety is not established here.

## A precise covered-decoder theorem

The theorem below holds over **any field**, on **any n distinct evaluation
points**, for `n=4s`, `k=2s`, `s>=10`, and `t=3s-1`.

Fix arbitrary received polynomials-as-words `u,v : D -> F`. A joint source is
a pair `(p,q)` of polynomials of degree below `k` whose joint core

`A(p,q)={x in D : (u(x),v(x))=(p(x),q(x))}`

has at least `t` points. Let `J` be the set of all such pairs. A **covered bad
scalar** is an MCA-bad scalar gamma for which some MCA witness decoder is
`p+gamma*q` for a pair `(p,q)` in `J`.

**Theorem. There are at most n covered bad scalars.**

This bounds a subset of the actual MCA-bad set; it is not a universal safety
claim. It is stronger than a conditional statement requiring an a priori
chosen source family, since `J` contains every high-core pair in the full code.

### 1. At most four joint sources

Distinct source pairs agree jointly on at most `e=k-1=2s-1` points, by
applying the polynomial root bound to a nonzero component difference.
For `L` subsets of a ground set of size `N`, each of size at least `t`, with
pairwise intersections at most `e`, the standard incidence argument gives

`L*t^2 <= N*(t+(L-1)*e)`.

For completeness, if `r_x` is the number of sets containing x, then
`sum r_x >= L*t` and `sum r_x(r_x-1) <= L(L-1)e`.
Equivalently, trim each set to exactly t points. Then Cauchy gives
`(L*t)^2/N <= sum r_x^2 <= L*t+L*(L-1)*e`, which is the stated inequality.

For five sources on all n coordinates the necessary inequality fails:

`5*t^2-n*(t+4e)=s^2-10s+5 > 0` for `s>=10`.

Thus `|J|<=4`. The field size does not enter this bound.

### 2. Three sources cost less than n

For a fixed source, every bad witness decoder `p+gamma*q` must have a point
x at which the received pair differs from the source pair but the scalar
projection agrees. Such a point is outside its joint core. The affine
equation `(u-p)(x)+gamma*(v-q)(x)=0` has at most one solution gamma when
the residual pair is nonzero. Therefore each source contributes at most
`n-t=s+1` bad scalars. If `|J|<=3`, their union has size at most
`3(s+1)<4s=n`.

### 3. Four cores cover the whole domain

If a coordinate belonged to no source core, puncture it and apply the
four-set incidence inequality on `n-1` points. It would give
`4*t^2 <= (n-1)*(t+3e)`, whereas exactly

`4*t^2-(n-1)*(t+3e)=s>0`.

Hence, if there are four sources, every coordinate belongs to at least
one of their cores.

### 4. Source points are collinear at every coordinate

For any three source pairs `z_i=(p_i,q_i)`, the determinant polynomial

`H(X)=det(z_1(X)-z_0(X), z_2(X)-z_0(X))`

has degree at most `2k-2=n-2`. At a coordinate contained in r of these
three cores, it has root multiplicity at least `max(r-1,0)`:
two coincident source vectors force one linear factor, and three force
one factor in each row, hence two factors. Thus total forced multiplicity
is at least the sum of core sizes minus the union size, namely

`3t-n=5s-3 > 4s-2=n-2`.

So `H=0`. This holds for every source triple, in every characteristic;
there is no derivative/divided-factorial assumption. Consequently all
source vectors at any fixed coordinate are collinear in `F^2`.

When there are four sources, the received vector at every coordinate is
one of them by step 3. All nonzero source residual vectors at that point
are therefore parallel. The equation `a+gamma*b=0` has at most one gamma
across all those residuals (and none if the common residual direction has second component zero). Each coordinate supplies at most one covered bad scalar.
There are n coordinates. This proves the theorem.

## Actual-domain obstruction: a high-core cover is not universal

The next construction works on the actual production subgroup, and indeed
on any n distinct field points. It refutes a naive extension of both the
UDR handed-pair collapse and a universal high-core-pair cover.

Choose any `R subset D` of size `k-1=2s-1`; define
`c(X)=product_{r in R}(X-r)`. Partition `D\R=A disjoint_union B`, with
`|A|=s` and `|B|=s+1`. Choose `a in A`. Set

* `u(x)=c(x)` on A and `u(x)=0` elsewhere;
* `v(a)=1`, and `v(x)=0` for `x!=a`.

The zero source pair jointly agrees with `(u,v)` on `D\A`, of size
`3s=t+1`. At gamma=0, the codeword c agrees with u on exactly
`S=R union A`, of size `3s-1=t`.

No codeword q can agree with v on S: q would vanish at the `t-1=3s-2`
points of `S\{a}`, at least k points for `s>=2`, forcing q=0, while
`q(a)=1`. Thus `(gamma=0,S,c)` is an original same-support MCA witness.
Its decoder is c, whereas the supplied zero-pair projection is zero.

**Claim: J={(0,0)}.** Let (p,q) have a joint core T of size at least t.
At every point of T other than possibly a, q vanishes. Thus q has at least
t-1=3s-2>=2s=k roots and degree less than k, so q=0. Since v(a)=1, a is
not in T. If p were nonzero, the number of points of T outside A would be
at most k-1 by the root bound, and at most s-1 points of T could lie in A
because a is absent. Hence |T|<=(k-1)+(s-1)=t-1, a contradiction.
Thus p=0 too. Conversely (0,0) has core D\A of size 3s=t+1.

At gamma=0, c agrees with u on exactly S=R union A, of size t.
Any q agreeing with v on S would have at least t-1>=k roots but q(a)=1,
impossible. Therefore (0,S,c) is an original same-support MCA witness.

The only projection of a source in J is the zero decoder. At gamma=0,
its agreement set is D\A, and the pair (0,0) jointly explains every
subset of that set. Hence zero cannot be a bad-witness decoder at gamma=0.
Consequently **0 lies in B_exceptional=B\B_covered**.

Indeed **B_covered={-c(a)}**, and this scalar is nonzero. A witness decoded
by zero must include a, since away from a the second received component is
zero and (0,0) would explain any zero-line support. Agreement at a forces
gamma=-c(a). Conversely at this scalar, the zero decoder agrees on
(D\A) union {a}, of size t+2. The spike cannot be interpolated on this
support by a degree-less-than-k polynomial, so it is a genuine MCA witness.
This does not determine the full bad set or refute endpoint safety.

## Exact remaining obligation

For every received pair at the first step, split its actual bad set as
`B=B_covered disjoint_union B_exceptional`, where covered is defined using
the full high-core list J above. We proved `|B_covered|<=n`, but a valid
safety proof requires the stronger joint accounting

`|B_covered|+|B_exceptional|<=n`.

The displayed counterexample shows that setting `B_exceptional=empty` is
false even on the actual domain. A list-size-only argument cannot finish
this obligation. The current order-16 unsafe construction at
`7/24+1/(3n)` is compatible with all statements here.

Sources inspected: `Errors.lean`, `MCAUDRBound.lean`, `MCAUDR2Bound.lean`,
`docs/wiki/deltastar-programme.md`, and the actual order-16 construction.
No historical 1/3 or Paley cancellation claim is used.


## Additional first-step results

The following are written polynomial arguments; the four-source branch was
independently reviewed. No Lean verification is claimed for this note.

## 1. The full |J|=4 branch is safe

**Lemma (projection collisions are covered).** If distinct sources z_i=(p_i,q_i), z_j have identical polynomial projection p_i+gamma q_i=p_j+gamma q_j, then gamma belongs to B_cov.

Proof: their cores A_i,A_j cannot be nested: a pair agreeing on at least k points is uniquely determined. Choose x in A_j\A_i. The common projected decoder agrees on A_i union {x}, which has at least t points. Any joint pair on that support equals z_i by its agreement on A_i (size at least k), but z_i disagrees at x. This is an original same-support MCA witness.

Consequently, outside B_cov all projections of J are pairwise distinct. An exceptional decoder is different from each projection; otherwise its own witness makes the scalar covered. If |J|=4, there would therefore be five distinct RS codewords each agreeing with the projected word on at least t points. Their pairwise agreement sets intersect in at most k-1 points. The incidence inequality gives

    5 t^2 <= n(t+4(k-1)),

but the difference of its left and right sides is s^2-10s+5>0. Contradiction. Thus **|J|=4 implies B_exc is empty and |B|<=n**, using the independently established covered budget. Agent07 independently checked this argument.

More generally, outside B_cov any decoder list contains |J| distinct projections, and its total size is at most four. This controls decoders at a fixed scalar; it does not bound the number of exceptional scalars.

## 2. Every four-codeword configuration has quadratic cross-ratio

Let f_0,...,f_3 be four pairwise distinct polynomials of degree below k, with agreement sets S_i of size at least t against one word. Define the nonzero polynomials

    U=(f_0-f_1)(f_2-f_3),
    V=(f_0-f_2)(f_1-f_3),
    W=(f_0-f_3)(f_1-f_2),

so U-V+W=0 and each has degree at most 2k-2=n-2.

At a domain point contained in r of the S_i, each product U,V,W has a root of multiplicity at least max(r-2,0): for r=3 every pairing contains an equal pair; for r=4 each pairing contains two equal pairs. This uses polynomial factor divisibility, valid in every characteristic. Therefore their common gcd G has

    deg G >= sum_x max(r_x-2,0)
          >= sum_i |S_i| - 2n
          >= 4t-2n = n-4.

It follows that **U/G, V/G, W/G all have degree at most two**. Equivalently the polynomial cross-ratio U/V is represented by numerator and denominator of degree at most two. Constant or degree-one cross-ratios are allowed.

This applies to the three projected high-core sources plus any exceptional decoder when |J|=3. It is an unconditional structural restriction on every such witness. It is not a bound on how many gamma have such a witness: the residual quadratic polynomials may depend on gamma.

## 3. Four agreement sets have only six units of low-multiplicity defect

For the same four codewords and r_x as above,

    sum_x binom(r_x,2) <= 6(k-1),
    sum_x r_x >= 4t.

Using binom(r,2)-3r+6=(r-3)(r-4)/2 gives

    6 N_0 + 3 N_1 + N_2 <= 6,

where N_j counts points of multiplicity exactly j. Moreover N_0=0: the four-set puncture inequality fails by s>0 if a point were uncovered. Thus **3N_1+N_2<=6**, and at all but six points at least three of the four codewords agree with the received word.

For |J|=3 and an exceptional witness S, put r_0(x)=number of the three source cores containing x. Then at all but six points, r_0(x)+1_S(x)>=3. In particular, there are at most six points with r_0<=1, and S must contain all but at most six of the coordinates where exactly two source cores agree. These are support constraints, not a global exceptional-scalar budget.

## 4. Three joint sources have a carrier of degree at most one

For any three distinct sources z_0,z_1,z_2 in J, the determinant det(z_1-z_0,z_2-z_0) has degree at most n-2 and forced root multiplicity at least 3t-n=5s-3>n-2, hence vanishes identically.

Write z_1-z_0=H_1(A,B) with A,B coprime, and set d=max(deg A,deg B). Polynomial coprimality and the vanishing determinant give z_2-z_0=H_2(A,B) with H_2 polynomial. The cores of z_0,z_1 intersect on at least 2t-n=k-2 distinct points. At each such point H_1 vanishes, since coprime A,B cannot both vanish. Thus deg H_1>=k-2. On the other hand deg H_1+d<=k-1, so **d<=1**.

Hence every three-source joint family admits

    z_i=z_0+H_i(A,B),  max(deg A,deg B)<=1,

with coprime A,B and the required RS degree bounds. Projection has carrier A+gamma B, of degree at most one. This substantially narrows a future discriminant/pencil calculation. The source polynomials H_i still have production-scale degree.

## 5. Exact small-cofactor form relative to any high-core source

Subtract a source (p,q), put A=its exact joint core, E=D\A, m=|E|<=s+1. If gamma has a witness decoder f distinct from p+gamma q, then

    h=f-p-gamma q != 0,
    |S intersect A| >= t-m,
    |S intersect E| >= t-(k-1)=s.

Therefore m>=s. In particular, a joint source with **|A|>=3s+1=t+2** rules out all exceptional decoders at every scalar and directly gives |B|<=m<=s-1.

In the remaining m=s or s+1 cases, h has at least k-1 or k-2 roots in A, respectively. Factoring those distinct roots gives

    h=product_(x in S intersect A)(X-x) * L(X),

where deg L<=0 for m=s and deg L<=1 for m=s+1. Every exceptional witness uses at least s of the at most s+1 outside points. For m=s it uses all E and has exactly k-1 roots on A; for m=s+1 it can omit at most one point of E.

This is the low-cofactor reduction requested by the task. It does not bound the number of admissible root subsets in A or the number of exceptional gamma.


## Three-source first-step closure

2026-09-08. Written proof; exact algebra checked below, not yet Lean formalized. This proves the full original-MCA bound in the |J|=3 branch for s>=20 (in particular production s=2^28).

Parameters: n=4s, k=2s, t=3s-1. J is the full list of joint pairs with exact core size at least t. Assume |J|=3. As before B_cov are bad scalars admitting a decoder projected from J, B_exc=B\B_cov.

### Preliminary facts

1. |B_cov|<=3(n-t)=3(s+1).
2. Outside B_cov, the three source projections are pairwise distinct, and any exceptional witness decoder is distinct from all three (the projection-collision lemma above).
3. Source pairs have common primitive carrier:

       z_i=z_0+H_i(A,B),  i=0,1,2, H_0=0,
       gcd(A,B)=1, d=max(deg A,deg B)<=1,
       deg H_i<=k-1-d.

   This follows from the determinant multiplicity and core-intersection argument in the primitive-carrier argument above. At every domain point in the union U of the three cores, the received pair lies on this same pointwise affine line z_0(x)+F(A(x),B(x)).
4. Each exceptional witness, together with the three source cores, forms four distinct-codeword agreement sets. Therefore its four-set multiplicities obey N_0=0 and 3N_1+N_2<=6 (the four-set defect argument above).

Let r_0(x) denote membership multiplicity in the three source cores. Define

    Z={x:r_0(x)=3}, M={x:r_0(x)=2},
    L={x:r_0(x)<=1}, O=D\U={x:r_0(x)=0}.

Existence of one exception implies |L|<=6. Indeed r_0<=1 remains at most two after adding its witness support and thus uses at least one unit of the defect budget. It also implies |O|<=2: those points must belong to the witness support by N_0=0, so each has new multiplicity one and costs three defect units.

Pairwise source-core intersections have size at most k-1-d, since H_i-H_j is a nonzero polynomial of that degree and the primitive carrier has no simultaneous zero. Hence

    3|Z|+|M| <= 3(k-1-d).

Since n=|Z|+|M|+|L|, |L|<=6 yields |Z|<=s+1 and |M|>=3s-7 (a bound valid for both d=0 and d=1).

Every exceptional witness support S_gamma omits at most six points of M: each omitted point has four-set multiplicity two and costs one defect unit.

### Two exceptions force one common fourth polynomial source

Choose one original MCA witness support and decoder for each exceptional scalar, once and for all. A projected witness for each scalar suffices for the final count; uniqueness of decoders is not assumed.

Suppose gamma and delta are distinct exceptional scalars. Write

    T_gamma=A+gamma B,
    F_gamma=f_gamma-(p_0+gamma q_0),

where f_gamma is a chosen original MCA witness decoder. Its degree is at most k-1. On M the received residual pair is aligned with (A,B). Therefore

    T_delta F_gamma - T_gamma F_delta

vanishes on M intersect S_gamma intersect S_delta, a set of size at least

    |M|-12 >= 3s-19 > 2s=k

for s>=20. Its degree is at most k, so it is identically zero. No rational dependence of the witness family has been assumed: this identity follows from two actual supports.

If d=0, each T_gamma is a nonzero constant: a zero polynomial would make the original source projections collide, making gamma covered. Thus F_gamma/T_gamma is a polynomial H of degree at most k-1, common to all exceptional gamma once there are two (apply the same identity against one fixed exceptional scalar).

If d=1, A,B are linearly independent over F; otherwise their common linear factor contradicts gcd(A,B)=1. For distinct gamma,delta, T_gamma,T_delta are coprime, because any common root would be a common root of A,B. At least one of these two polynomials is nonconstant. The identity implies F_gamma=T_gamma H and F_delta=T_delta H for a polynomial H of degree at most k-2. The same fixed-base identity gives F_eta=T_eta H for **every** exceptional eta.

In either case

    z_* = z_0 + H(A,B)

is a valid joint RS codeword pair, and every chosen exceptional witness decoder is its projection. It is distinct from each source in J; equality would make the corresponding scalar covered.

### Constant carrier: at most two exceptions

If d=0 and there are at least two exceptions, use the common source z_* just proved. For an exceptional gamma, its MCA witness cannot jointly agree with z_* everywhere. Thus at some point of its support the residual pair from z_* is nonzero but its gamma-projection vanishes.

That point cannot belong to U: there every residual pair is a multiple of the constant nonzero carrier (A,B), and T_gamma is nonzero. It must therefore belong to O. Every fixed point in O supplies at most one scalar for a nonzero residual pair. Consequently |B_exc|<=|O|<=2.

The same bound trivially holds if fewer than two exceptions exist. Thus

    |B| <= 3(s+1)+2 <= 4s=n.

### Linear carrier: a large exceptional set fills the fourth core

If |B_exc|<=2, the preceding numerical bound already proves safety. Suppose |B_exc|>=3. Construct z_* as above, with deg H<=k-2.

At most |O|<=2 exceptional scalars can cancel a nonzero residual from z_* at a point of O. Choose an exceptional gamma outside that set. At every point of its support where joint agreement with z_* fails, the point therefore lies in U, and the nonzero residual is parallel to (A,B). Projection agreement forces T_gamma(x)=0. The nonzero polynomial T_gamma has degree at most one, so this occurs at at most one domain point. Hence the exact joint core A_* of z_* has

    |A_*| >= |S_gamma|-1 >= t-1.

All four sources z_0,z_1,z_2,z_* have the same primitive carrier with d=1 and scalar polynomials of degree at most k-2. Every pair of their exact joint cores intersects on at most k-2 points.

**Their four cores cover D.** Otherwise work on N=n-1 points. Let R be the total membership count in the four cores. Then R>=3t+(t-1)=12s-5, and

    sum_x r_x(r_x-1) <=12(k-2).

Cauchy implies R^2<=N(R+12(k-2)). Since R^2-NR is increasing for R>=N/2, the lower bound for R would imply

    (12s-5)^2 <= (4s-1)(36s-29).

But the left side minus the right side is **32s-4>0**. Contradiction.

At every domain point, the received vector therefore equals at least one of the four source vectors. Since all four vectors lie on the same carrier line, every nonzero residual from any source is parallel to (A(x),B(x)). All actual bad scalars have a witness decoder from these four sources: those in B_cov by definition, and those in B_exc by the common-H identity. The original MCA obstruction supplies a nonzero residual cancellation point for that source. Thus every bad scalar satisfies

    A(x)+gamma B(x)=0

at some x in D. Coprimality means A(x),B(x) cannot both vanish, so each coordinate supplies at most one scalar. Therefore **|B|<=n**.

### Conclusion and remaining scope

For any field and distinct evaluation domain, n=4s, k=2s, t=3s-1, s>=20, the full same-support MCA scalar count is at most n whenever the full high-core joint list has cardinality three. The cardinality-four case was proved above. The |J|<=2 cases remain open here. This written proof was independently reviewed by a second agent, with no gap found; it still requires formalization; no global first-step safety theorem is claimed.

Independent review: agent10 read the full proof and checked each main step on 2026-09-08, finding no gap. Its symbolic/arithmetic audit receipt is maintained in its separate assigned directory. This review is not Lean verification.

## Two-source and sparse-direction extensions

The [two-source proof](astra_mca_two_source-2026-09-08.md) now also bounds the
full bad set by n for |J|=2. Dividing actual decoders by the primitive linear
carrier produces at most four rational profiles; every profile that fails to
lift to a valid joint pair occurs at most once. This argument was independently
reviewed, and its exact inequalities are checked by a standalone probe.

The [sparse-direction proof](astra_mca_sparse_direction-2026-09-08.md) gives
at most four bad scalars for a one-point direction and at most n when the
direction lies within floor(n/18) of the code, regardless of J. The actual
singleton spike is therefore safe, despite its genuine exceptional scalar.
The remaining universal cases are J empty or singleton with dense directions.
These extensions are reviewed written proofs, not Lean results.
