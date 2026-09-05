# Positive second-Hasse sources at the companion production radius

Exact rank profiles give positive second-derivative interpolation certificates
at the actual companion parameters. One source uses

```text
n=262144, w=131071, A=181353, p=2130706433,
m=80, S1=24, S2=6, T=1042, D=m*A=14508240.
coefficient dimension C = 106458223810750,
exact single-node rank L = 406103404,
C-n*L = 653072574 > 0.
```

Thus, for every received line over a field of characteristic p, a nonzero
polynomial Q in this source space annihilates every degree-at-most-w
polynomial agreeing at A nodes, when evaluated on its first two Hasse
derivatives. This is a dimension certificate and a written interpolation
argument, not a constructed production matrix or a Lean theorem.

The corresponding order-one certificate at the same m=80,S1=24 fails for
every total cap T. The earlier negative order-two search covered m<=24;
these sources lie outside that family. Neither comparison proves that an
actual order-one kernel is zero.

**No MCA count, improved score, or ProtocolClaim follows yet.** To use Q as
an additional cut, its pullback must be proved proper on the components being
counted. The numerical attraction and that missing condition are recorded
below. Independent review and Lean formalization remain outstanding.

## Source and local blocks

Use the [existing second-Hasse source](astra_hasse_order_two-2026-09-05.md):

```text
X^a Y0^i Y1^j Y2^k Z^z,
a+w*i+(w-1)*j+(w-2)*k<D,
i+j+k+z<=T, j<=S1, k<=S2.
```

At each node alpha substitute

```text
X=alpha+t,
Y0=u0(alpha)+Z*u1(alpha)+t*Y1-t^2*Y2+v,
weight(t,v,Y1,Y2,Z)=(1,3,0,0,0),
```

and kill every coefficient of weight below m. The translations preserve the
source space in both directions, so their rank is independent of the node
and received values. The Hasse--Taylor identity makes the substituted v have
order at least three along an agreeing polynomial. Consequently D<=m*A
forces the specialized Q to vanish identically by the ordinary root bound.

The centered local blocks are indexed by h=i+j+k and r=a+2i+j. At fixed h,
temporarily use homogeneous variables U,V,W0 and the transformation

```text
Y0 -> U+V-W0, Y1 -> V, Y2 -> W0.
```

For each j<=S1,k<=S2,j+k<=h, put i=h-j-k. Its column is
`(U+V-W0)^i V^j W0^k`, with input degree d=2i+j. The row U^e V^J W0^K
has e+J+K=h and output weight v_out=J-e. Its coefficient is

```text
binomial(i,e)*binomial(i-e,J-j)*(-1)^(i-e-J+j),
```

when all indicated counts are nonnegative, and zero otherwise. The local
block keeps exactly the columns d<=r and rows v_out>r-m. The other row
condition, 2e+J<=r, is automatic on a nonzero entry of a kept column:
`2e+J<=2i+j<=r`.

## One ordered elimination gives every cutoff rank

Sort columns by increasing d and rows by decreasing v_out. Process rows in
that order, eliminating at their leftmost nonzero column using earlier rows.
Record each pivot as `(d_p,v_p)`.

For every prefix of the rows, these operations preserve its span, and the
nonzero echelon rows have distinct leading columns. After restriction to a
column prefix, a row survives precisely when its leading column lies in that
prefix; the surviving rows remain independent. It follows that every
northwest submatrix has rank equal to the number of its recorded pivots.
In particular, in the field of calculation,

```text
rank M_(h,r) = number of pivots p with d_p<=r<m+v_p.        (1)
```

This proves the rank-query rule, rather than inferring it from a numerical
pattern. Ties in either ordering are harmless because the cutoffs include
their entire weight groups. The full transformation is invertible on the
polynomial ring, so the capped input columns are independent before
truncation and every column receives a pivot.

There is also an exact shift. Once h>=h0=S1+S2, every input polynomial has
the common factor `(U+V-W0)^(h-h0)`. The input degree shifts by 2(h-h0).
For output weights `weight(U,V,W0)=(-1,1,0)`, this factor has leading term
V^(h-h0), so multiplication shifts weighted degree by h-h0 exactly. Products
of nonzero leading forms cannot cancel in a polynomial domain. Thus the
whole rank filtration is obtained from h0 by

```text
(d_p,v_p) -> (d_p+2*(h-h0), v_p+h-h0).                    (2)
```

It suffices to eliminate matrices for 0<=h<=S1+S2. This does not assume a
characteristic-zero rank; all entries and pivots are computed in F_p, and
ranks persist over extensions of that field.

## Summing the exact dimensions

Put B_h=D-(w-2)h. Each input column permits `max(0,B_h-d_p)` X exponents.
Summing (1) over the eligible integer r gives

```text
C_h = sum_p max(0,B_h-d_p),
R_h = sum_p max(0,min(B_h,m+v_p)-d_p).                    (3)
```

The column input degrees can be read from the pivots because every column
has one pivot. Formula (3) removes the need to eliminate a new matrix for
each r and m. With H=floor((D-1)/(w-2)), the global counts are

```text
C(T)=sum_(h<=min(T,H))(T+1-h)*C_h,
L(T)=sum_(h<=min(T,H))(T+1-h)*R_h.
```

As in the [earlier all-T search](astra_hasse_production-2026-09-05.md), write
b_h=C_h-n*R_h, B=sum b_h and M=sum h*b_h. For T>=H the surplus is
`(T+1)*B-M`. Check all smaller T explicitly; if none passes and B>0, the
first passing T in the affine range is `max(H,floor(M/B))`.

Four exact production witnesses are:

| m | S1 | S2 | First passing T | C(T) | L(T) | C-nL |
|---:|---:|---:|---:|---:|---:|---:|
| 80 | 24 | 6 | 1042 | 106458223810750 | 406103404 | 653072574 |
| 99 | 30 | 8 | 1031 | 251781244332003 | 960462396 | 1789994979 |
| 99 | 30 | 1 | 4156 | 249336238924268 | 951142005 | 69165548 |
| 99 | 30 | 2 | 2270 | 200387154562542 | 764415510 | 215109102 |

For the first row, B=863615144 and M=900097522618. Its predecessor T=1041
has surplus -210542570. The full source rank at n nodes is at most nL;
no independence between different nodes is assumed.

With S2=0 the same calculation recovers the first passing T=217071 for
m=99,S1=30, and T=7159 with margin 228451639 for m=166,S1=51. For
m=80,S1=24,S2=0 the slope is -22039275 and every T fails the strict
dimension inequality. The new positive result is not an extrapolation from
the earlier small-field example inside the Johnson regime.

## The possible extra cut, and the unresolved containment case

Let F(X,Y,R,Z) be the regular factor being counted, H_F=F_R, and
G_F=-F_X-R*F_Y. On a polynomial solution, f''=G_F/H_F. Since p is odd,
the second Hasse derivative is G_F/(2H_F). Clear denominators in Q:

```text
B_Q=(2H_F)^S2 * Q(X,Y,R,G_F/(2H_F),Z).                    (4)
```

For every selected regular polynomial solution, B_Q vanishes identically.
For an F with cumulative R/YR/total caps `(r,y,t)`, (4) has caps

```text
Rcap <= S1+(r+1)*S2,
YRcap <= H+(y-1)*S2,
totalcap <= T+(t-1)*S2.                                 (5)
```

Here H is the source's maximum h from (3). These follow term by term from
the caps `(r-1,y-1,t-1)` of H_F and `(r+1,y,t)` of G_F.

At the binding cumulative flag `(10,47,2364)`, the first source gives the
raw cut flag `(14834,296,90)`. Using the current first-tail flag, the same
mixed-degree bookkeeping assigns

```text
flagMixed(Fflag, firstTailFlag, B_Qflag) = 11696018394652.
```

The one-second-derivative-cap source gives the smaller conditional number
5313045624744, with raw cut flag `(6337,141,41)`. Both are much smaller
than the existing singleton allowance 283403712362442072. They are
**conditional degree calculations**, not new bounds on the selected family.
To count with such a cut, properness on the relevant regular first-tail
components must be established, together with the source-to-budget bridge.
The entire phase recurrence would then need to be reevaluated.

Finding a nonzero Q does not prove any of those conditions. The cleared B_Q
can vanish identically, be divisible by F, or contain a first-tail component.
The new kernel could contain equations implied by existing relations. The
remaining task is to handle components on which every available B_Q vanishes,
or prove their total contribution small enough. None is excluded here.

The [full-kernel containment construction](astra_hasse_containment-2026-09-05.md)
exhibits this failure in a separate source: its entire second-Hasse kernel
is nonzero, its matching first-order kernel is zero, and its pullback is
still a multiple of the old regular factor. That construction has total
degree one and nonpositive uniform dimension margin. It does not refute
properness for the positive production profiles above.

The subsequent [component split](astra_hasse_component_split-2026-09-05.md)
weakens the sufficient geometric condition: it allows B_Q to contain
first-tail components, provided B_Q is nonzero on the irreducible surface
being counted. It uses the degree of B_Q for contained components and the
existing weighted divisor certificate for components of large multiplicity.
All four source degree bounds fit its conditional binding-cell allowance.
Surface properness and the complete phase/Lean integration remain open.

## A limited Z-degree obstruction to trivial multiples

There is a useful constraint on the raw differential relation

```text
L_F=2F_R*Y2+F_X+R*F_Y.
```

Assume char(K)!=2, each of deg_X F, deg_Y F, deg_R F is below the
characteristic, and F has positive contact at at least one node. Then

```text
L_F != 0,  deg_Z(L_F) >= deg_Z(F)-deg_Y(F).               (6)
```

To prove this, write F=sum_j Z^j f_j(X,Y,R). For j>deg_Z(L_F), the Y2
coefficient gives `(f_j)_R=0`. The degree restriction makes f_j independent
of R. The remaining equation `(f_j)_X+R*(f_j)_Y=0` then makes f_j constant
in X and Y as well. If d=deg_Z(F)>deg_Z(L_F)+deg_Y(F), its leading Z
coefficient is therefore a nonzero constant. Substitution at the contact node,
`Y=u0+Z*u1`, cannot cancel that coefficient: all nonconstant coefficient
terms have Z degree at most deg_Z(L_F)+deg_Y(F). This contradicts positive
contact. The same reasoning excludes L_F=0, since then F would be a
nonzero polynomial in Z alone. The bound is sharp for
`F=Y^b-Z^b+X*R` at node zero with u0=0,u1=1, where deg_Z(L_F)=0.

If the **actual** total degree of F is 2364 and its YR degree is at most 47,
then deg_Z(F)>=2317, and (6) gives deg_Z(L_F)>=2270 under its contact
hypotheses. A nonzero Q with total degree 1042 or 1031 therefore cannot be
a polynomial multiple of F or of the raw L_F. This observation does not
establish properness in (4): cancellation in a combination of the two
relations, a primitive relation after removing common factors, or containment
modulo F remains possible. An upper cap of 2364 without actual degree
attainment would also not justify the stated lower Z-degree bound.

The [containment example](astra_hasse_containment-2026-09-05.md) explicitly
realizes cancellation between these two relations with arbitrarily large
Z degree and a total-degree-one Q. Its high-Z factor has contact and a
regular selected solution but lacks the old first-order kernel provenance.

## Reproduction

Run `python3 scripts/probes/astra_hasse_rank_profile_check.py`, or add `--scan`
to reproduce the bounded 528-profile search. That scan uses the explicit
sets of m,S1,S2 in the script and has 123 passing profiles; its best T is not
a global optimum claim. Its sorted-key JSON profile digest is
`3716560c6d39d65ae32673385d63ff1149f6bd3e16cb8ee6e4528f252fb59966`.

The checker compares (1) and (2) with 4480 older sparse block ranks over
F2,F5,F17 and F_p, checks 20 nontrivial production-sized blocks against the same
independent expansion routine, and reproduces the full 1426-profile exclusion
digest from the previous search. It verifies all four source counts, the
order-one calibrations, predecessor failures, and the conditional mixed
numbers by an independent polarization formula. No full production matrix,
large-field list, proper cut, or complete prize theorem is constructed.
