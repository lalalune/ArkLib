# A full second-Hasse kernel whose pullback gives no extra cut

An actual second-Hasse source can have a one-dimensional full kernel while
the matching first-order source has zero kernel, yet every second-Hasse
interpolant vanishes identically on an earlier regular factor after pullback.
The example includes independent received words modulo the code and a genuine
singleton MCA-bad family. Thus an actual improvement in interpolation
existence does not, by itself, supply an independent equation.

This construction has total degree one, an R-degree-one old factor, and a
**nonpositive uniform dimension margin**. It does not refute properness for
the [positive production sources](astra_hasse_rank_profile-2026-09-05.md),
realize the binding C2 flag, or improve any prize bound. It identifies a
failure mode that a properness argument must distinguish. The general proof
below has exact finite checks; independent review and Lean formalization
remain outstanding.

## Parameters and the old factor

Use the [full-kernel simple-tail construction](astra_contact_variation-2026-09-05.md).
Let n=A+e distinct nodes lie in a field of characteristic p>n, with e>=1
error nodes and A remaining nodes. Assume

```text
w>=2,  w+3e<=A.
E=product of the error-node factors,
W=product of the A remaining node factors,
L=X-xi, where xi is outside all nodes,
u0=0 on the A nodes and nonzero on the error nodes,
u1(x)=1/L(x) at all nodes.
```

The earlier full first-order kernel at contact order two and weighted cutoff
`D1=A+2e+w+1` is spanned by E^2 F, where

```text
F=(W-LW')Y+LW R+W'Z.
```

The assumptions above imply the hypotheses of that earlier construction.
F is primitive and irreducible, and H=F_R=LW is nonzero. The nearby family
is exactly `(f,gamma)=(0,0)`; it is MCA-bad, and u0,u1 are independent modulo
the degree-at-most-w code. These conclusions follow from the earlier root
bounds and do not presume the existence of a nonzero seed direction.

## The entire new kernel

Put S=Hasse_2(f)=f''/2, and use the complete source box

```text
X^x Y^i R^j S^k Z^z,
x+w*i+(w-1)*j+(w-2)*k<D2=2A+3e+w,
i+j+k+z<=1.
```

Require contact order three at all n nodes using

```text
Y=u0+Z*u1+t*R-t^2*S+v,  weight(t,v,R,S,Z)=(1,3,0,0,0).
```

Define J=(W')^2-W W''/2. The full kernel is precisely K*Q, where

```text
P=(LJ-WW')Y+(W^2-LWW')R+LW^2 S-JZ,
Q=E^3 P.                                                  (1)
```

Each Y,R,S term of Q has weighted degree at most D2-1, and the Z term has
smaller weight. Also D2<=3A. The explicit local equations below show contact
order at least three, so Q annihilates all degree-at-most-w candidates with
A agreements. Its S coefficient is nonzero.

For membership directly, its R and S coefficients satisfy (2). At a root x
of W, write t=X-x and W=t*h. If a,d denote the displayed Y,Z coefficients
of P, then

```text
a+L(x)*d=t*J-W*W'=t^3*((h')^2-h*h''/2).
```

This proves all three Z-channel conditions. The constant channel is zero,
and E^3 supplies the required order at every error node.

### Why this describes the full kernel

An arbitrary member has the form `a0 Y+b0 R+c0 S+d0 Z+e0`, with coefficients
in K[X]. At gamma=0,f=0, contact at the A nodes makes W^3 divide e0.
Since deg(e0)<D2<=3A, e0=0. At each error node, u0 is nonzero, so the
constant channel makes a0 divisible by the node factor cubed. The R,S,Z
channels then give the same divisibility for b0,c0,d0. Divide by E^3 and
write the quotient as `aY+bR+cS+dZ`. Its bounds are

```text
deg a<=2A-1, deg b<=2A, deg c<=2A+1, deg d<=2A+w-1.
```

At each root x of W, the R and S channels say

```text
b(x)=0, (b'+a)(x)=0, (b''/2+a')(x)=0,
c(x)=c'(x)=0, (c''/2-a)(x)=0.                             (2)
```

Consequently c=W^2 t with deg(t)<=1. Since a=t(W')^2 modulo W,
the first two R equations give

```text
b=-tWW'+B W^2,  B in K.
```

The value and derivative equations for a in (2) then agree with those of
`tJ-BWW'` at every root of W. Both have degree at most 2A-1, so their
difference, divisible by W^2, is zero:

```text
a=tJ-BWW'.                                                (3)
```

It remains to use the Z channel. The rational graph
`Y=Z/L, R=-Z/L^2, S=Z/L^3` agrees at every root of W and is regular there.
Its second-Hasse contact residual has order at least three. Substituting in
the quotient and clearing L^3 therefore makes W^3 divide

```text
N=L^3 d+L^2 a-L b+c.
```

Its degree is at most 2A+w+2<3A, since A>=w+3e and e>=1. Thus N=0.
Evaluating at X=xi gives t(xi)W(xi)^2=0, so t=lambda L. Substitute this into
N=0 and divide by L to get

```text
L^2(d+lambda J)+(lambda-B)W(LW'+W)=0.
```

A second evaluation at X=xi gives B=lambda, and then d=-lambda J.
Equations (3) and these identities give precisely lambda P. This proves
full-kernel uniqueness, not just membership of the displayed Q.

### The matching first-order kernel is zero

An order-three first-order contact polynomial, independent of S, also has
second-Hasse contact order three: replace its contact residual v_old by
`v-t^2*S`, whose weight is at least two. Thus its kernel embeds in the full
second-Hasse kernel at the same D2 and total cap one. Every nonzero member
of the latter has the nonzero S coefficient E^3 LW^2. Hence the first-order
kernel is zero. This is a statement about the actual global kernels, not
just their dimension lower bounds.

## Every new equation is already a differential consequence

Let delta be the polynomial derivation with
`delta(X)=1, delta(Y)=R, delta(R)=2S, delta(Z)=0`. Then

```text
delta(F)=-LW''Y+2W R+2LW S+W''Z,
P=(W/2)*delta(F)-W'*F.                                   (4)
```

Both identities hold coefficient by coefficient. On the regular F surface,
substituting `S=-(F_X+R F_Y)/(2F_R)` kills delta(F), so every Q pulls back
to zero modulo F. More explicitly, the cleared pullback is

```text
(2H)*Q(X,Y,R,-(F_X+R F_Y)/(2H),Z)=-2H E^3 W' F.           (5)
```

It therefore gives no proper cut of F or of any of its first-tail components.
The coefficients of the second-Hasse source are not all zero; the failure is
containment in the existing differential relations.

### A Z-degree gap alone also does not force properness

For any d>=2 put `F_d=F+W^2*Z^d`. The same P satisfies

```text
P=(W/2)*delta(F_d)-W'*F_d,
```

because the new Z^d coefficient is `(W/2)*(W^2)'-W'*W^2=0`.
Consequently the whole kernel K*Q also gives no proper pullback cut of F_d.
Here F_d and its raw differential relation both have Z degree d, while Q
has total Y,R,S,Z degree one. This is an explicit cancellation between the
two relations, the case left open by the limited Z-degree lemma in the
production-source note.

F_d remains irreducible and regular: its Y and R coefficients have gcd one
in K[X], and it is linear in Y,R over K(X,Z). It has contact at least two
at the A nodes, retains the selected solution (0,0), and its R derivative is
still LW. However, for d>=2 it is **not** a divisor of the earlier complete
first-order kernel K*E^2 F. This variant establishes a limitation of contact,
regularity, and the Z-degree gap; it does not supply the missing first-order
kernel provenance for F_d.

## Exact controls and the dimension-certificate boundary

Run `python3 scripts/probes/astra_hasse_containment_check.py`.

| p | n | w | e | D2 | New columns | New rank | New nullity | Matching first-order nullity |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 17 | 9 | 2 | 1 | 21 | 102 | 101 | 1 | 0 |
| 17 | 6 | 2 | 1 | 15 | 72 | 71 | 1 | 0 |
| 17 | 10 | 2 | 2 | 24 | 117 | 116 | 1 | 0 |
| 19 | 11 | 3 | 2 | 27 | 129 | 128 | 1 | 0 |

The first geometry is also checked at characteristics 257,65537,2130706433.
These checks build the entire contact matrices, verify the explicit vector,
check the local coefficients separately, recheck the old order-two kernel
dimension and line independence, and verify (4)--(5) as polynomial identities.
The companion characteristic is included with small n,w; this is not the
production geometry or an extrapolation of a small-field count.

Each local matrix has rank 12. The complete box has `5D2-3w+3` columns, so
its uniform dimension margin is

```text
C-12n=-2A+3e+2w+3<=3-3e<=0.                             (6)
```

The actual one-dimensional kernel results from dependencies between the
node constraints. In particular, (6) does **not** realize the strictly
positive uniform dimension margins of the new production sources. A
properness theorem could still use that stronger condition, their higher
degree flags, or an effective bound on the subspace of differential
consequences. Neither such a theorem nor its negation is proved here.

The [component-splitting follow-up](astra_hasse_component_split-2026-09-05.md)
shows that properness on each first-tail curve is unnecessary if the extra
equation is proper on the original surface. The examples here still have
zero restriction on that surface, so they do not satisfy the weaker
condition either.

The [squarefree-denominator follow-up](astra_squarefree_denominator-2026-09-05.md)
extends the rational direction to 1/L with arbitrary squarefree L. At its
specified degree cutoff, the contained subspace is exactly one-dimensional,
while a positive margin forces the full source to have dimension at least
two. Thus that structured extension cannot furnish a positive-margin
containment counterexample. Arbitrary production properness remains open.
