# A full interpolation kernel with a simple selected tail intersection

A one-dimensional **full** interpolation kernel can contain a genuine bad
MCA seed while the extracted factor's first two tails meet with multiplicity
one. The construction below includes an irreducible universal
factor, independence of the two received words modulo the code, a genuine bad
MCA seed, and positive factor contact at every selected agreement node. Its
tail intersection is still transverse.

This factor has R degree one and a singleton selected family. It does **not**
realize the binding C2 flag `(10,37,2317)`, invalidate a bound restricted to that
flag, or improve the companion numerical allowance. The written arguments
below have exact finite controls; independent review and Lean formalization
remain outstanding.

The [positive-margin follow-up](astra_positive_kernel_factor-2026-09-05.md)
adds a strictly positive uniform source dimension certificate in four exact
finite controls. The complete first-order kernel still has a universal
regular factor and a simple selected tail intersection. A separate positive
second-order source does escape that factor in those controls.

This continues the [C2 local countermodel](astra_c2_geometry_contact_obstruction-2026-09-04.md)
and the [far-word kernel analysis](astra_far_word_kernel-2026-09-05.md). The
former attained the binding flag without full-kernel provenance. The present
example adds that provenance at a different degree flag; these are two
separate examples, not one example satisfying both sets of hypotheses.

## Relation to the existing Jacobi constraint

The [selected-graph Jacobi note](astra_selected_family_constraint-2026-09-05.md)
already proves that a contact sum greater than c+1 kills every fixed-seed
polynomial infinitesimal variation, and that any remaining seed direction
must interpolate u1 on at least `contact_sum-c+w-1` nodes. Its numerical
benchmark requires an actual upper bound on c; c_min cannot supply that.
Those results are not new claims of this note.

The examples below add full-kernel provenance and independence of the received
words to the singleton controls. They have no nonzero polynomial infinitesimal
variation, yet all selected higher tails vanish and the first two meet simply.
Thus this rigidity does not supply the missing multiplicity improvement.

## An actual full-kernel example

Choose n distinct nodes in a field K of characteristic p>n, an error set E0
of size e>=1, and its complement S of size A=n-e. Assume

```text
1<=w<=A-3,  D=n+e+w+1<=2*A.
```

Choose a outside the nodes, and write

```text
E(X)=product_(x in E0)(X-x), W(X)=product_(x in S)(X-x), L=X-a.
u0=0 on S, with arbitrary nonzero values on E0;
u1(x)=1/L(x) on all n nodes.

F=(W-L*W')*Y + L*W*R + W'*Z,
Q=E^2*F.                                                  (1)
```

Use the complete coefficient box

```text
Xexp+w*Yexp+(w-1)*Rexp<D,
Yexp+Rexp+Zexp<=1,
```

and contact order two at every node. Q lies in this box: its Y and R terms
have weighted degree at most n+e+w=D-1, and its Z term has smaller degree.
At nodes in E0 the E^2 factor supplies order two. At a node of S, F has order
two for Y=Z/L(x)+t*R+v. The coefficient of v there is -L(x)W'(x), nonzero.
Thus F has exact contact order two on S and exact order zero on E0; Q has
exact order two everywhere.

### The full contact kernel is exactly K*Q

Every member P of this box has the form

```text
P=A0(X)*Y+B0(X)*R+C0(X)*Z+D0(X).
```

At gamma=0 and f=0, the contact conditions on S force W^2 to divide D0.
Since deg(D0)<D<=2*A, D0=0. At an error node, u0 is nonzero. The constant
and first-order contact equations then give A0=A0'=B0=B0'=C0=C0'=0 there.
Consequently E^2 divides all three coefficients.

After division the box has D_*=D-2e=A+w+1. Write the quotient as
a0*Y+b0*R+c0*Z. On S its contact equations are

```text
b0=0 mod W, a0+b0'=0 mod W,
c0=-a0/L mod W, c0'=-a0'/L mod W.                          (2)
```

The degree caps are deg a0<=A, deg b0<=A+1, deg c0<=A+w. Write b0=W*b,
deg b<=1, and L*c0+a0=W*T, deg T<=w+1. Differentiating and using (2) gives
c0=W'*T mod W, while a0=-W'*b mod W. Since W' is invertible mod W,
b=L*T mod W. Both sides have degree below the number of nodes in S, because
w+2<A. Thus b=L*T exactly, and T is a constant kappa. Finally

```text
c0=kappa*W'+W*h,
a0=kappa*(W-L*W')-L*W*h.
```

The degree bound on a0 forces h=0. The quotient is kappa*F, proving that the
full source kernel is one-dimensional, not merely exhibiting one of its
members.

### Universal factor, regularity, and the actual MCA bad set

The three coefficients of F have gcd one. At a root of W, W' is nonzero;
at the root a of L, W-LW'=W(a) is nonzero. Any common divisor would divide
LW and is excluded by these two observations. Since F is primitive and
linear in Y,R,Z, it is irreducible over K[X,Y,R,Z], and geometrically linear
over K(X). It divides every member of the full kernel. Its selected solution
is f=0,gamma=0, and F_R=LW is nonzero as a polynomial in X. Regularity here
is generic in X; its zeros at individual nodes are allowed.

For gamma!=0, agreement on S with a polynomial f of degree at most w gives
a root of L*f-gamma. That nonzero polynomial has degree at most w+1. Hence
there are at most w+1+e<A agreements in total. For gamma=0 a nonzero f also
has fewer than A agreements. Thus the complete nearby family consists
exactly of gamma=0,f=0.

No degree-at-most-w polynomial agrees with u1 on A nodes: L*f-1 has at most
w+1 roots. There is therefore no joint codeword pair on an A-node support,
and gamma=0 is genuinely MCA-bad. The two received words are independent
modulo the code: any relation alpha*u0+beta*u1=f restricts on S to
L*f=beta, forcing beta=f=0, and then alpha=0. Any selected-pencil cardinality
bound of e+1 is also satisfied by this singleton family.

## The tail intersection remains simple

Form the contact derivation over K(X) first, with delta X=1, delta Y=R,
delta Z=0 and delta R=-(F_X+R*F_Y)/F_R. On F=0 put

```text
kappa=(L*Y-Z)/W.
```

Direct differentiation gives delta(kappa)=F/W^2=0. Thus (kappa,Z) are
coordinates on the plane, and

```text
Y=kappa*(W/L)+Z/L.
```

Write W=L*P+W(a), with P monic of degree A-1. Put d=w+1 and
b_j=(-1)^j*j!/L^(j+1). The first two tail equations, up to nonzero scalar
factors in K(X), have coefficient rows

```text
(P^(d)+W(a)*b_d, b_d),
(P^(d+1)+W(a)*b_(d+1), b_(d+1))
```

in (kappa,Z). Their determinant is

```text
-(b_d/L) * (L*P^(d+1)+(d+1)*P^(d)).                       (3)
```

The polynomial in parentheses has degree A-1-d and leading coefficient
A*(A-1)*(A-2)*...*(A-d), which is nonzero since p>n>=A and d<=A-2.
The determinant is therefore nonzero. The first tail is a reduced line and
the second cuts it transversely at the selected origin. Both multiplicities
are exactly one, while every higher tail still vanishes at that origin.

The companion's `globalTailCut(j)` differs from delta^j(Y) by the units
`(-X)^j*H^(2j)` on this regular generic surface, as recorded in the earlier
C2 countermodel. These units do not change the local conclusion. Only after
forming these equations do we extend scalars to an algebraic closure; no
derivation through a purely inseparable extension is assumed.

## Finite verification and remaining boundary

Run `python3 scripts/probes/astra_contact_variation_check.py`.

| Field | n | w | e | A | Source columns | Full rank | Nullity |
|---|---:|---:|---:|---:|---:|---:|---:|
| F17 | 9 | 2 | 1 | 8 | 49 | 48 | 1 |
| F17 | 10 | 2 | 2 | 8 | 57 | 56 | 1 |
| F17 | 8 | 1 | 1 | 7 | 43 | 42 | 1 |

The checker builds each full contact matrix, verifies the explicit kernel
vector and rank, independently checks its local coefficients, exhausts every
field parameter and polynomial for the actual bad-set census, verifies
independence modulo the code, and compares the direct rational tail recurrence
with its closed formula as polynomial identities. It also finds full rank in
the polynomial variation equations, so these examples have no nonzero
polynomial infinitesimal variation at all. The determinant checks concern
formal polynomials, not only their values on F17.

A contrasting control uses
`F=W*R-W'*Y+(W'*g0-W*g0')*Z`, with `g0=3+2X+X^2` on eight F17 nodes.
Every node has ord(H)=1, and the variation space has dimension one, generated
by `(g,eta)=(g0,1)`. This family has the joint codeword pair `(0,g0)`; it is not
an MCA counterexample. It checks that the variation criterion permits a real
inhomogeneous direction rather than asserting that every variation vanishes.

These checks refute a parameter-independent multiplicity-two shortcut even
after adding full-kernel provenance and a bad MCA seed. An argument for the
binding C2 case would still have to exploit its higher R degree, a large
selected family, or further relations specific to its production sources.
This example does not reduce the current moving budget.

The [second-Hasse follow-up](astra_hasse_containment-2026-09-05.md) uses the
same received words to construct a full order-three contact kernel. It can
be nonzero when the matching first-order source is empty, yet every new
polynomial is a differential consequence of F and supplies no extra cut.
Its uniform dimension margin is nonpositive, so it does not refute the
strictly positive production second-Hasse certificates.
