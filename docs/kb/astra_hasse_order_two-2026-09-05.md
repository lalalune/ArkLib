# Exact finite ranks for Hasse derivative order two

Order two gives a strict finite interpolation gain in one fixed comparison.
At length 64, message degree at most 15, contact order 8, and total candidate
degree cap 16, the count below certifies a nonzero interpolant at 34 agreements.
The order-one boxes with these same budgets first pass at 35 agreements.
This is a comparison of the stated dimension certificates, not a proof that
every order-one interpolation method fails at 34.
This example is inside the ordinary Johnson regime, since A^2=1156>n*w=960;
it improves the fixed finite interpolation certificate and is not a
beyond-Johnson decoding advance.

The same small order-two box does not pass at the companion production
parameters. No root-finding bound, selected-family argument, universal-divisor
statement, or prize claim follows from this interpolation gain.

## Taylor identity and the common support budget

The starting identity is equations (8), (13)--(15) in
[BCPZZ revision 1](https://eccc.weizmann.ac.il/report/2026/164/revision/1/download).
Write H_j(f) for the j-th Hasse derivative. They satisfy

    f(alpha+t) = f(alpha) + t*H_1(f)(alpha+t)
                 - t^2*H_2(f)(alpha+t) mod t^3.

This holds in every characteristic. In particular, Y2 represents a Hasse
derivative, not an ordinary second derivative divided by two.

Let f have degree at most w, with w>=2. For arbitrary received words u0,u1
on n distinct nodes, treat Z as the line parameter. Use monomials

    X^a Y0^i Y1^j Y2^k Z^z,
    a+w*i+(w-1)*j+(w-2)*k < D,
    i+j+k+z <= T, j<=S1, k<=S2.                         (1)

At each node alpha substitute

    X=alpha+t,
    Y0=u0(alpha)+Z*u1(alpha)+t*Y1-t^2*Y2+v,

and require all coefficients of contact weight below m to vanish, where
weight(t)=1, weight(v)=3, and Y1,Y2,Z have weight zero. This is equivalent
to the paper's order-two local conditions: its remainder variable appears
as t*E with E divisible by t^2.

The order-one comparison removes Y2, substitutes Y0=u0+Z*u1+t*Y1+v, and
uses weight(v)=2. It keeps D,T,m and the Y1 cap unchanged. Thus both the
specialized X-degree budget and the total candidate degree budget coincide;
the additional derivative variable changes the polynomial space.

For either construction, a nonzero Q satisfying these constraints gives

    Q(X,f(X),H_1(f)(X),H_2(f)(X),z)=0

whenever f agrees with u0+z*u1 at A nodes and D<=m*A. Indeed, every such
node supplies a zero of order at least m, while the specialized degree is
less than D. This proves an annihilating identity, not a bound on how many
polynomials or line parameters can satisfy it.

## An exact local rank formula

Write C2 for the number of monomials in (1). Direct summation gives

    C2 = sum_(i+j+k<=T, j<=S1, k<=S2)
           (T+1-i-j-k)*max(0,D-w*i-(w-1)*j-(w-2)*k).    (2)

The triangular translations X -> X+alpha and Y0 -> Y0+u0+Z*u1 preserve
the support space in (1), as do their inverses. Therefore the local rank
is independent of alpha,u0,u1. Compute it at alpha=u0=u1=0.

The centered substitution preserves the two gradings

    h=i+j+k, r=a+2*i+j.

Its output monomial t^ell v^e Y1^J Y2^K has

    h=e+J+K, r=ell+2*e+J, contact weight=r+e-J.

Different (h,r,z) therefore occupy disjoint rows. The global weight bound
becomes r+(w-2)*h<D and is constant on each block.

Define M_(h,r) as follows. Its columns have i,j,k>=0, i+j+k=h,
j<=S1,k<=S2 and a=r-2*i-j>=0. Its rows have e,J,K>=0,
e+J+K=h, ell=r-2*e-J>=0 and r+e-J<m. For a column, set
u=J-j and q=i-e-u. The entry is zero if e,u,q are not nonnegative;
otherwise it is

    binomial(i,e)*binomial(i-e,q)*(-1)^q.               (3)

Here q counts chosen -t^2*Y2 factors in (t*Y1-t^2*Y2+v)^i.
All entries are reduced in the field of calculation.
The exact local rank is

    L2 = sum_(0<=h<=T) (T+1-h)
           * sum_(0<=r<m+h, r+(w-2)*h<D) rank M_(h,r). (4)

No rows survive when r>=m+h, since J<=h. Thus (4) uses small finite
matrices even when the global X widths are large. Gaussian elimination
over F_p computes their ranks exactly; the ranks remain the same over any
extension of F_p. This does not assume a characteristic-zero rank.
Each order-two block in the fixed comparisons below has at most 15 columns,
since its column is determined by j=0,...,4 and k=0,...,2.

For order one put h=i+j and r=a+i. In an eligible block the column
indices i form the interval

    max(0,h-S1) <= i <= min(h,r).

The row indices are e=0,...,m-r-1 and the entries are binomial(i,e).
A consecutive-column Pascal minor in its first rows has determinant one,
so the rank equals the smaller of the column count and m-r, in every
characteristic. Consequently

    L1 = sum_(h=0..T) (T+1-h)
           * sum_(0<=r<m, r+(w-1)*h<D)
             min(max(0,min(h,r)-max(0,h-S1)+1),m-r).    (5)

Formula (2) with S2=0 gives C1. Independently, restricting the order-two
input to S2=0 gives exactly the order-one contact conditions and rank.

At n nodes the total rank is at most n*Ld. Therefore Cd>n*Ld proves a
nonzero interpolant for every received line. No assertion of independence
between different nodes is used.

## Fixed finite improvement and a production control

Use the companion characteristic p=2130706433. It admits 64 distinct
subgroup nodes; all statements also hold over its degree-six extension.
Fix m=8,T=16,S1=4 and, for order two, S2=2.

| n | w | A | D=mA | Order | Coefficients | Exact local rank | C-nL |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 64 | 15 | 34 | 272 | 1 | 106665 | 1690 | -1495 |
| 64 | 15 | 34 | 272 | 2 | 269845 | 4162 | 3477 |
| 262144 | 131071 | 181353 | 1450824 | 1 | 384899595 | 1690 | -58123765 |
| 262144 | 131071 | 181353 | 1450824 | 2 | 898433625 | 4143 | -187628967 |

For the finite n=64 comparison, the checker also evaluates every order-one
cap S1=0,...,16. None passes at any A<=34; S1=4 passes at A=35 with
margin 3345. The fixed order-two box first passes at A=34. These are exact
finite comparisons at fixed m and T, not an optimization over arbitrary
monomial sets or other multiplicities.

The negative production margins mean these particular dimension arguments
do not certify a production interpolant. They do not prove nonexistence of
interpolants, and do not supersede the existing larger companion source
construction. New derivative variables would also require fresh downstream
factor and list analyses; matching the total degree cap does not supply them.

## Reproduction

The [rank-profile follow-up](astra_hasse_rank_profile-2026-09-05.md) reuses
this block formula to give positive second-Hasse certificates at the actual
companion radius. Its existence argument does not yet prove a proper extra
cut or a stronger MCA count.

Run `python3 scripts/probes/astra_hasse_order_two_check.py`.
The [checker](../../scripts/probes/astra_hasse_order_two_check.py) verifies
the displayed counts and finite thresholds. It independently constructs
36 direct local substitution matrices over F2,F5 and the companion prime,
at centered and translated received points, and compares their dense ranks
with (4) and (5). It also checks the S2=0 restriction and the Hasse--Taylor
cancellation. No production global matrix or decoded list is enumerated.
The general implications follow from the polynomial and rank arguments
above; they are not Lean-formalized.
