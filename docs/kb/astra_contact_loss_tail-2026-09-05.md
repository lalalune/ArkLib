# Contact loss and an unbounded exclusion of low-R dimension certificates

A Hasse coefficient-extraction argument supplies an analytic tail for the
earlier finite first-order audit. At the companion parameters, no full
first-order source with R cap at most nine has a positive uniform dimension
margin, for **any** multiplicity, cutoff D<=m*A, or total-degree cap. The
finite audit up to m=500 covers every multiplicity outside the new tail.

This also excludes all root-safe derivative-trimmed second-Hasse dimension
certificates with R cap at most nine, without a multiplicity bound. Omitting
the first derivative entirely makes higher-derivative contact equivalent
to ordinary multiplicity contact on each coefficient; higher derivatives
alone cannot yield a positive uniform margin here.

These exclude dimension certificates, **not** actual kernels or general
properness, and give no improved prize bound. The written proof and exact
controls await independent review and Lean formalization. The positive
production sources have larger R caps and are not excluded.

## Coefficient extraction and local rank

For derivative order d>=1 use variables R1,...,Rd and local coordinates

```text
Y=u0+Z*u1+t*R1-t^2*R2+...+(-1)^(d+1)*t^d*Rd+v,
weight(t)=1, weight(v)=d+1, weight(Rj)=weight(Z)=0.
```

If Q has R1 degree at most r and contact at least m, every coefficient
q_i in Q=sum_i R1^i*q_i has contact at least m-d*r. Let D_R^[j] be the
j-th Hasse derivative in the original R1 variable, at fixed original Y.
Locally this takes the coefficient of epsilon^j in

```text
(R1,v) |-> (R1+epsilon, v-t*epsilon).
```

A term differentiating v a times has a factor t^a and loses at most
d*a<=d*j contact. Now use the polynomial identity

```text
q_i=sum_(j=i..r) binom(j,i)*(-R1)^(j-i)*D_R^[j] Q.       (1)
```

Multiplication by R1 has weight zero, so (1) proves the bound. The identity
is the binomial theorem coefficientwise and uses no factorial inverses;
the argument works in every characteristic.

For an R1-independent polynomial, the invertible filtered change

```text
R1_new=R1+sum_(j=2..d) (-1)^(j+1)*t^(j-1)*Rj
```

makes the Y substitution u0+Z*u1+t*R1_new+v. Expand in powers of
Y-u0-Z*u1. The coefficient of R1_new^j*v^0 is t^j times the j-th
coefficient; every other term from that power has greater or equal
contact weight. Contact >=M is therefore equivalent to ordinary
multiplicity >=M in (X-x,Y-u0-Z*u1), coefficientwise in R2,...,Rd.

Consequently every coefficient of Q in **all** derivative variables has
ordinary contact at least M=m-d*r. For a full box with weighted cutoff D,
total cap T, and derivative caps, the coefficient of R1^i1...Rd^id has

```text
D_i=D-sum_j (w-j)*ij,    T_i=T-sum_j ij.
```

For 1<=d<=w these satisfy D_i<=D. When M>=1, let C_i,L_i be the ordinary
coefficient source's dimension and local rank at multiplicity M. The
kernel inclusion just proved implies

```text
C=sum_i C_i,    L_d>=sum_i L_i.                         (2)
```

Empty coefficient sources contribute zero. This is a local rank inequality
on the complete box; no independence of different nodes is assumed.

## Ordinary-source bound with integer rounding

Suppose positive integers n,w,B satisfy

```text
1<=w<B<n, delta=n*w-B^2>=0,
kappa=delta+w*(n-B)-floor(w^2/4)>0.                     (3)
```

Every nonempty full ordinary source at multiplicity M>=1, cutoff
0<D<=M*B, and total cap T>=0 has C-n*L<0. Its exact counts are

```text
C=sum_(j=0..T) (T+1-j)*max(0,D-w*j),
L=sum_(j=0..T) (T+1-j)*max(0,min(D-w*j,M-j)).            (4)
```

Translation in X and in Y by u0+Z*u1 preserves the box in both directions,
so the local rank is counted at the origin.

If D<=M*w, every nonzero coefficient length D-w*j is at most w*(M-j),
with j<M. Its excess over n times its local rank is negative, whether
or not the rank has saturated. This proves the assertion in this case.

For M*w<D<=M*B, the local rank for j<M is M-j and the layer excess is
e_j=D-n*M+(n-w)*j, which increases with j. For j>=M the excess is
max(0,D-w*j), hence nonnegative. The layers have at most one sign change,
from negative to nonnegative. Define C_star(K)=sum_(j>=0)max(0,K-w*j).
For K=M*B with remainder s modulo w, exact summation gives

```text
2w*(n*M*(M+1)/2-C_star(M*B))
  =M^2*delta+M*w*(n-B)-s*(w-s)
  >=kappa>0.                                           (5)
```

Thus the total layer excess is negative even at D=M*B, and hence for
every smaller D in this case. With the single sign change, every prefix
sum is negative. The margin (4) is the sum of its first T+1 prefix sums,
so it too is negative. This covers unbounded T and every smaller D.

## Production thresholds and the finite bridge

At the companion parameters,

```text
n=262144, w=131071, A=181353,
B=floor(sqrt(n*w))=185363,
B-A=4010, delta=34455, kappa=5768895146.
```

For a d-th order source with D<=m*A and R1 cap r, equations (2)--(5)
exclude a positive uniform margin whenever

```text
m>=ceil(d*r*185363/4010),    m>=1.                     (6)
```

This is exactly m*A<=(m-d*r)*B, and implies m-d*r>=1 when r>0.
All coefficient sources satisfy the ordinary bound; summing and applying
(2) proves the exclusion. There is no bound on the other derivative
caps or on T. For r=0 it applies to every m>=1.

| R1 cap r | First order: excluded for m>= | Second order: excluded for m>= |
| ---: | ---: | ---: |
| 1 | 47 | 93 |
| 2 | 93 | 185 |
| 3 | 139 | 278 |
| 4 | 185 | 370 |
| 9 | 417 | 833 |

For first order and r<=9, every multiplicity below (6) is included in the
[earlier bounded audit](astra_root_safe_filtration-2026-09-05.md): m<=500,
every D<=m*A, and every T. Its source,
[`astra_root_safe_filtration.cpp`](../../scripts/probes/astra_root_safe_filtration.cpp),
is unchanged since commit `29ecd8a06cad69dac83897971183cbee385d8136`.
Both the normal and UBSan receipts record 438215244 endpoint checks and
1735490 total-cap checks, following 342 independent small controls.
Together that audit and (6) cover **all m>=1**.

## Consequence for the root-safe second-order filtration

Suppose the second-Hasse source has R cap r<=9 and S cap s, with

```text
D<=m*A-s*(A-w+2).                                      (7)
```

In the filtration by S degree, the leading coefficient in degree j has
first-order contact >=m-j. This holds in every characteristic: the j-th
Hasse derivative in S extracts the leading coefficient exactly, and
locally S translation changes v by t^2 times the translation, losing at
most j contact. An S-independent polynomial has the same contact as in
first-order coordinates, because the free S variable detects the terms
of weight two in v-t^2*S.

The coefficient source has D_j=D-j*(w-2), T_j=T-j, and

```text
D_j<=(m-j)*A-(s-j)*(A-w+2)<=(m-j)*A.
```

If it is nonempty then m-j>=1; otherwise D_j<=0. The unbounded first-order
exclusion applies to every nonempty slice. The kernel filtration bounds
the second-order local rank below by the sum of the slice ranks, while
dimensions add exactly. Hence (7) has no positive uniform margin for any
m,s,T when r<=9. This does not exclude the untrimmed sources.

## Verification and remaining scope

```sh
python3 scripts/probes/astra_contact_loss_tail_check.py
```

The checker compares full local-kernel constraints with ordinary
coefficient constraints for orders one through three over F2, F5, F17,
and F_2130706433. It tests Hasse coefficient extraction beyond the small
characteristics, integer rounding, ordinary source margins, and all
displayed production thresholds. The receipt explicitly identifies the
separate finite first-order audit; this new checker does not rerun it.

Actual global kernels can exist with negative uniform margin because node
constraints can be dependent. These exclusions do not rule out such
kernels, alternative support shapes, or proper equations obtained another
way. General production properness and the prize targets remain open.
