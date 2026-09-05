# A differential carrier for the fixed-word scalar list

Fixing the received word removes the varying MCA scalar from the
interpolation problem. A first-order differential relation then defines a
curve in two variables. Its truncated Taylor reconstruction gives an actual
curve in polynomial coefficient space, whose degree can be bounded.

The written argument below gives, for every received word and every set of
262144 distinct nodes over a field of characteristic 2130706433,

```text
deg f<=131071, agreements>=181353
    ==> number of candidate polynomials <= 12546010856.       (1)
```

For the companion field K=F_(2130706433^6), this is below the required
list budget 274980728111395087. The exact projection argument transfers
(1) to every positive interleaving arity. **This is a written mathematical
argument with finite controls, not a Lean-verified result or an independently
reviewed prize submission.** It does not bound MCA at the same radius, solve
the companion ProtocolClaim, or determine either grand-challenge threshold.

## A fixed-word interpolation space

Let x_1,...,x_n be distinct nodes over K, let v be any received word, and
let 2<=w<A<=n. Choose positive integers m,D and a nonnegative R cap s.
Use the K-vector space spanned by

```text
X^a Y^i R^j,
a+w*i+(w-1)*j<D, 0<=j<=s.
```

At node x_l impose contact order at least m after the substitution

```text
X=x_l+t, Y=v_l+t*R+z,
weight(t,z,R)=(1,2,0).
```

These are linear conditions on the source coefficients: all coefficients
of t^a z^b R^c with a+2b<m must vanish. The symbol z here is the local
contact deviation, not an MCA line parameter.

The coefficient dimension C and exact rank L of a single node's map are

```text
C=sum_(j=0..s, i>=0) max(0,D-w*i-(w-1)*j),

L=sum_(h>=0, 0<=r<m, r+(w-1)*h<D)
      min(max(0,min(h,r)-max(0,h-s)+1), m-r).             (2)
```

Both sums are finite. Translation in X and Y preserves this downward-closed
coefficient space, in both directions, so the rank is independent of x_l
and v_l. At the centered node write h=i+j and r=a+i. The output terms of
X^a Y^i R^j are

```text
binomial(i,b)*t^(r-b)*z^b*R^(h-b),  r+b<m.
```

Different (h,r) give disjoint output blocks. The column indices i form
the consecutive interval max(0,h-s),...,min(h,r). The first consecutive
Pascal rows have determinant one on a square consecutive-column block;
the rank is therefore exactly the minimum in (2), in every characteristic.
This is the no-line-parameter version of the
[earlier local rank calculation](astra_hasse_order_two-2026-09-05.md).

If C>nL, the simultaneous kernel contains a nonzero Q(X,Y,R), uniformly
for every received word. No independence between different nodes is needed:
the rank of their combined map is at most nL.

For a polynomial f of degree at most w, agreement at x_l implies

```text
f(x_l+t)-v_l-t*f'(x_l+t) is divisible by t^2.
```

Consequently Q(X,f,f') has a root of multiplicity at least m there.
Its degree in X is less than D. If D<=mA and f agrees at at least A nodes,
the root bound proves the polynomial identity

```text
Q(X,f(X),f'(X))=0.                                      (3)
```

Thus the interpolation step supplies a genuine common differential relation
for the complete scalar list, without assuming a common factor in advance.

## Turning a differential curve into a coefficient carrier

Work first over L=K(X), with its usual derivation in X. Let F in L[Y,R]
be an irreducible factor of Q of total degree d>=1 in Y,R. Assume
char K=0 or char K>max(w,d). The characteristic hypothesis w<char K is
essential for Taylor reconstruction; it must not be replaced by merely
requiring F_R nonzero.

First consider a factor with H=F_R nonzero. In the coordinate ring of
F=0 with H inverted, put

```text
G=-F_X-R*F_Y,
delta(X)=1, delta(Y)=R, delta(R)=G/H.
```

This derivation preserves F=0. For j>=2 one has

```text
delta^j(Y)=N_j/H^(2j-3),
deg_(Y,R) N_j <= (2j-3)*(d-1)+1.                        (4)
```

Indeed N_2=G has degree at most d. For h=2j-3, the next numerator is

```text
N_(j+1) = H^2*(N_j,X+R*N_j,Y) + H*G*N_j,R
 - h*N_j*(H*(H_X+R*H_Y)+G*H_R).
```

Every term increases total Y,R degree by at most 2d-2, proving (4).
Differentiating a coefficient in K(X) does not change Y,R degree.

With U a new independent polynomial variable, define

```text
q(U)=sum_(j=0..w) delta^j(Y)/j! * (U-X)^j.               (5)
```

The coefficients of q define a rational map from the curve F=0 to the
affine coefficient space of degree-at-most-w polynomials. All coordinates
can be put over H^(2w-3), with numerator degree at most

```text
E(d)=(2w-3)*(d-1)+1.                                   (6)
```

For an actual solution f of (3) belonging to this factor, with
H(X,f,f') not identically zero, specialization commutes with delta. Formula
(5) therefore specializes to the exact Taylor identity q(U)=f(U), since
deg f<=w<char K. These actual coefficient points are in the image of (5).
Here regularity is generic in X: H(X,f,f') may vanish at agreement nodes
and still be invertible as a nonzero element of K(X).
There is no need to assume that every point of the source curve gives a
polynomial solution of F=0.

All rational functions and derivatives above are formed over K(X).
Only afterward are the curve and rational map base-changed to an algebraic
closure. No derivation on the entire algebraic closure of K(X) is assumed.

The closure of the image has dimension at most one and total component
degree at most d*E(d). To see the degree bound, homogenize all map
coordinates to degree E(d). A generic target hyperplane pulls back to a
degree-E(d) equation on a source curve of degree d. Bezout bounds its
intersection degree by d*E(d); removing base points cannot increase it.
The generic degree of a nonconstant map is at least one, also for
inseparable maps. Constant image components contribute one point each,
at most the number of source components and hence at most d*E(d).

Apply the [scalar carrier lemma](astra_carrier_dimension_bound-2026-09-05.md)
over that algebraically closed field, with k=w+1. Agreement at any k nodes
still forces coefficients in K by interpolation. The regular solutions
belonging to F therefore contribute at most

```text
d*E(d)*(n-w)/(A-w)                                     (7)
```

list members. This supplies an actual carrier and its degree; unlike the
previous conditional carrier lemma, it does not leave carrier existence
as an extra hypothesis at this scalar profile.

## Singular solutions and factors independent of R

For an irreducible factor F with F_R nonzero, F and F_R have no common
curve component, including after base change. Equivalently, F is primitive
and separable as a polynomial in R over K(X,Y); char K>d suffices here.
Bezout bounds their common points by d*(d-1). The map

```text
f -> (f(X),f'(X))
```

is injective on K-polynomials, because X is transcendental. Thus at most
d*(d-1) additional list members have H(X,f,f') identically zero. This is
singularity of the implicit R projection, not necessarily a singular point
of the curve itself.

If F_R=0 identically, the degree and characteristic hypotheses force F to
be independent of R. The univariate polynomial F(Y) has at most d roots
in K(X), so it contributes at most d candidate polynomials. It must not
be counted as a regular differential curve. A factor of degree zero in
Y,R is a unit in K(X) and contributes no solution.

Write d_0 for the total Y,R degree of Q. Factorization in K(X)[Y,R] and
(3) assign every list member to at least one irreducible factor. Summing
the preceding bounds, using sum d_i<=d_0, E(d_i)<=E(d_0), and
sum d_i*(d_i-1)<=d_0*(d_0-1), gives the uniform bound

```text
list size <= floor(
  d_0*((2w-3)*(d_0-1)+1)*(n-w)/(A-w) + d_0*(d_0-1)).   (8)
```

Factors independent of R fit the first term because E(d_0)>=1 and
(n-w)/(A-w)>=1. Repeated factors need only be counted once; retaining their
degrees in d_0 is a safe overestimate. If d_0=0, (3) permits no list member.

## Exact companion arithmetic

Take

```text
n=262144, w=131071, A=181353, m=99, s=30,
D=m*A=17953947,
d_0 <= floor((D-1)/(w-1))=136.
```

The dimensions and resulting degree budgets are

| Quantity | Exact value |
|---|---:|
| Source coefficients C | 30638265433 |
| Single-node contact rank L | 116870 |
| Positive nullity lower bound C-nL | 1496153 |
| Reconstruction numerator degree E(136) | 35388766 |
| Coefficient-carrier degree bound | 4812872176 |
| Additional singular allowance | 18360 |
| Scalar carrier incidence ratio | 131073/50282 |
| Integer list bound from (8) | 12546010856 |
| Companion budget floor(q/2^128) | 274980728111395087 |

The characteristic p=2130706433 exceeds w and 136. For q=p^6 the exact
separation gate also holds:

```text
binomial(12546010856+1,2)=78701194205707931796 < q.
```

The [interleaving transfer](astra_interleaved_projection-2026-09-05.md)
therefore gives the same bound at every positive arity, including eight,
at Hamming error radius 80791/262144. It uses coefficients in F_(p^6),
not just projections over the prime subfield.

This is a bound at one radius and one length/dimension profile, not an
identification of the sharp scalar or interleaved threshold. The grand
production instance has a different length and a much smaller budget n;
the displayed result does not cover its 1/3 predecessor radius. Nor does a
scalar list bound imply MCA at the same radius: the distinctions and known
losses are described in [ABF26, Section 5](https://eprint.iacr.org/2026/680).
The companion MCA/root-counting gap and complete ProtocolClaim remain open.

## Reproduction and proof status

Run `python3 scripts/probes/astra_scalar_differential_carrier_check.py`.
The checker compares the scalar local-rank formula with direct substituted
matrices, checks the production dimensions in two summation orders and
against successive total-cap differences in the existing API, and verifies
the exact budget and interleaving gate.

It also reconstructs all three members of a complete F17 seven-node list
using a nonsingular conic differential relation and exact cleared-denominator
identities, checks the independent-of-R and singular-projection cases, and
demonstrates why Taylor reconstruction needs w<char K. These controls do
not generate the 30-billion-column production interpolation kernel or
mechanize the geometric degree argument. Independent mathematical review
and a complete Lean formalization are still outstanding.
