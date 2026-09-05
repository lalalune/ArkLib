# Root-safe coefficient extraction cannot improve the dimension certificate

Taking the highest second-derivative coefficient of a trimmed Hasse source
cannot produce a positive uniform dimension certificate unless one of its
first-order coefficient slices already has a positive certificate. This is
a linear-algebra consequence of the contact filtration, not a bounded search
over second-order parameters.

At the companion parameters, an exact finite calculation also excludes
positive first-order certificates with R cap at most nine and multiplicity
at most 500, for **every** weighted cutoff D<=m*A and **every** residual total
cap T. Together these rule out the corresponding root-safe extraction route
to a lower-R proper cut. They do not exclude actual nonzero kernels, larger
multiplicities, other supports, or the original untrimmed second-order route.
There is no improved prize bound. The proof below is written and the
calculations are reproducible; independent review and Lean integration remain
outstanding.

This continues the derivative-trimming attempt in the
[component-splitting note](astra_hasse_component_split-2026-09-05.md).

## The coefficient filtration

Let w>=2. Use the full second-order source box

```text
Xexp+w*Yexp+(w-1)*Rexp+(w-2)*Sexp < D,
Yexp+Rexp+Sexp+Zexp <= T,
Rexp <= r, Sexp <= s.
```

Initially assume s<m and char(K)>s. At each node the second-order contact
substitution is

```text
X=x_i+t, Y=u0_i+Z*u1_i+t*R-t^2*S+v,
weight(t,v,R,S,Z)=(1,3,0,0,0).
```

Write C2 for the coefficient-space dimension and L2 for the exact local
constraint rank. For j=0,...,min(s,T), put

```text
Dj=D-j*(w-2),  Tj=T-j,  mj=m-j.
```

Let Cj,Lj be the corresponding first-order coefficient dimension and local
rank with parameters `(Dj,w,Tj,mj,r)`. Empty coefficient boxes have Cj=Lj=0.
Then

```text
C2 = sum_j Cj,
L2 >= sum_j Lj,
C2-n*L2 <= sum_j (Cj-n*Lj).                             (1)
```

### Proof

Filter the second-order box by the degree in the original S variable.
For a polynomial of S degree at most j, let Pj be its highest coefficient.
In local coordinates,

```text
partial_(S,original) = partial_(S,local) + t^2*partial_v.
```

This operator lowers contact order by at most one. Its j-th power is
`j!*Pj`, which is nonzero when Pj is nonzero. Therefore, if the original
polynomial has contact at least m, Pj has second-order contact at least
m-j, and its support is the first-order box specified above.

For a polynomial independent of the original S variable, second-order and
first-order contact orders agree exactly. Indeed, pass from the first-order
local variable v1, of weight two, by `v1=v-t^2*S`. On its initial weighted
form this sends v1 to `-t^2*S`. Different v1 powers give different S powers,
so a nonzero initial form cannot cancel. This proves the claimed equality
of orders, including in positive characteristic.

At one node, taking Pj maps the j-th filtered local kernel into the
first-order local kernel of dimension Cj-Lj. Its kernel is the preceding
filtered local kernel. Summing dimensions gives

```text
dim(local second-order kernel) <= sum_j (Cj-Lj).
```

The coefficient spaces split exactly by S powers, so C2=sum Cj. Subtracting
the kernel-dimension inequality proves the rank inequality and then (1).
The same local ranks apply at every node: translating X and replacing Y by
`Y+u0_i+Z*u1_i` are invertible transformations preserving these source boxes.

## Why the trimming condition matters

Assume A>w-2 and impose the root-safe cutoff

```text
D <= m*A-s*(A-w+2).                                    (2)
```

For every nonempty slice j<=s this implies

```text
Dj <= (m-j)*A.
```

Thus a global first-order slice of contact m-j annihilates every degree-w
candidate with A agreements, by the ordinary root bound. A positive
second-order margin in (1) forces a positive first-order margin for at least
one such valid slice. The conclusion compares **uniform dimension
certificates**; an actual global kernel can be larger because constraints
at different nodes are dependent.

The restriction s<m loses nothing for the bounded production corollary
below. If a formal cap s>=m satisfies (2), then for every j>=m,
`Dj<=(m-j)*A<=0`. Those coefficient slices are empty, and the actual S
degree is below m. In production char(K)>m throughout the bounded range.

The motivation was to obtain a nonzero first-order P of R degree below ten.
Such a P would give a proper cut on an irreducible factor of R degree ten,
without needing to compare their total degrees. The remaining degree-budget
and phase obligations would still have to be checked. Formula (1) means this
extraction mechanism cannot bypass the existence certificate for its
first-order slices.

This does not apply to the untrimmed
[positive production sources](astra_hasse_rank_profile-2026-09-05.md), which
use D=m*A. Their highest S coefficients generally have too large a weighted
cutoff to invoke the required candidate root bound after differentiation.
Direct properness of those sources remains open.

## Exact production exclusion for the lower-R certificate class

Fix

```text
n=262144, w=131071, A=181353, char(K)=2130706433.
```

The C++ checker proves the following finite arithmetic statement for the
standard first-order box and local rank formula:

```text
1<=m<=500, 0<=r<=9, 1<=D<=m*A, T>=0
    implies coefficientCount(D,w,T,r)-n*localRank(D,w,T,m,r) <= 0.  (3)
```

In particular, combining (1)--(3) excludes a positive uniform certificate
for **any** second-order S cap and total cap in this multiplicity/R-cap
range when (2) is imposed. This is an exclusion of this certificate class,
not of actual interpolants or of the prize conjecture.

### How all D and unbounded T are covered

For h=Yexp+Rexp, write

```text
Ch(D)=sum_(j=0..min(r,h)) max(0,D-w*h+j),
Lh(D,m)=sum_(q=0..m-1; q+(w-1)*h<D)
          min(max(0,min(h,q)-max(0,h-r)+1),m-q).
```

This is the [exact first-order rank formula](astra_hasse_order_two-2026-09-05.md),
including the D cutoff. Its local blocks are consecutive-column Pascal
matrices with a unit maximal minor; no assumption about generic received
values or independence between different nodes enters the count.

The source margin is `sum_(h<=T) (T+1-h)*(Ch-n*Lh)`. Put
`H(D)=floor((D+r-1)/w)`, beyond which both channels vanish, and define

```text
B(D)=sum_h (Ch-n*Lh),
M(D)=sum_h h*(Ch-n*Lh).
```

For T>=H(D) the margin is exactly `(T+1)*B(D)-M(D)`. It suffices to check
`B(D)<=0` and `(H(D)+1)*B(D)-M(D)<=0`.

As an integer function of D, Ch changes slope at D=w*h-j, Lh jumps at
`D=q+(w-1)*h+1`, and H changes at `D=w*h-r+1`. The checker includes all
these events and D=m*A. Between consecutive events, B and the margin at H
are affine, with H fixed. Checking each interval's two integer endpoints
therefore covers every D in the range; no arbitrary D grid is used.

For T<H(D), one has `D>=w*(T+1)-r+1`. Since m<=500 and r<=9,
`m<=w-r+1`, and consequently

```text
D > w*T,
D > (w-1)*T+m-1.
```

All coefficient widths at h<=T are then positive and every possible local
rank term at h<=T is already present. Increasing D to m*A leaves that local
rank fixed and increases the coefficient count. Thus this case is bounded
by the margin at D=m*A and the same T. The checker separately enumerates
all T<=H(m*A) at that endpoint. This completes the coverage argument for
unbounded T and every weighted cutoff D.

The run performs 438215244 interval-endpoint checks and 1735490 checks of
the remaining total caps, all with signed 128-bit arithmetic. These counts
include repeated endpoints; they are not counts of distinct source boxes.
It also compares the event method with direct enumeration on 342 small
controls, 103 of which have positive certificates. Those positive controls
ensure that the implementation is not simply rejecting every input.

## Contact-rank and production controls

The Python checker independently expands 28 small local matrices and their
first-order slices over F2,F5,F17, and the companion characteristic, skipping
cases where the S cap reaches the characteristic. All rank inequalities are
strict in these controls. It also checks four production rows:

| Trimmed source (m,S1,S2,T) | Second-order margin | L2 minus sum Lj |
|---|---:|---:|
| (80,24,6,1042) | -4922770342480 | 5337770 |
| (99,30,1,4156) | -1545990052948 | 525393 |
| (166,51,1,42105) | 84317578 | 9106260 |
| (60,9,12,1000) | -8641612426271 | 19169209 |

The positive third row has first-order slice margins -9878943152949 and
12266178891967. Its R cap is 51, outside (3), and its positive slice is
consistent with (1). Thus the result is not a claim that every trimmed
source fails.

## Reproduction and boundary

```text
python3 scripts/probes/astra_root_safe_filtration_check.py
c++ -O3 -std=c++17 scripts/probes/astra_root_safe_filtration.cpp -o /tmp/astra-root-safe-filtration
/tmp/astra-root-safe-filtration
```

Both checkers use exact arithmetic and no external packages. The finite
search does not cover multiplicities above 500 or alternative support
shapes. Node correlations could still yield actual kernels despite every
tested margin being nonpositive. The next direct properness argument must
use information beyond this root-safe coefficient extraction certificate;
the untrimmed second-order approach is unaffected by the exclusion.
