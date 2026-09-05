# Preserving useful acceleration coordinates with a jet repair

The acceleration field degree is not invariant under the constant-codeword
normalization used in the
[extension criterion](astra_acceleration_extension-2026-09-05.md). A rational
acceleration can acquire arbitrarily large algebraic degree after such a
shift. The first result below weakens the zero-direction restriction, so
many useful coordinate systems can be retained. The second shows, using
complete positive first-order kernels, that low acceleration degree cannot
be inferred just from full-kernel provenance.

These are a written repair argument and exact finite controls. Neither
settles the remaining production case or improves a prize bound.
Independent mathematical review and Lean integration remain outstanding.

## Repairing the zero-direction nodes without changing coordinates

Use the same full second-Hasse source box and contact orders as in the
extension criterion. Let w>=2 and char(K)!=2. Let

```text
I0={i : u1_i=0}, z0=|I0|, and assume z0<=w-2.             (1)
```

If G in K[X,Y,R,S] has positive S degree and is primitive as a polynomial
in S over K[X,Y,R], then G cannot divide every member of a nonzero full
source kernel. Thus the acceleration-extension properness criterion remains
valid under (1); requiring every u1_i to be nonzero was stronger than needed.

Here is a proof including the needed degree estimate. As before, primitivity
implies `X-x_i` does not divide G. At every node outside I0, the injective
change `Y=u0_i+u1_i*Z` therefore gives contact order zero.

Let nu_i be G's contact order at the remaining nodes, and let
c=weightedDegree_(1,w,w-1,w-2)(G). We claim

```text
sum_(i in I0) nu_i <= c.                                  (2)
```

Choose the interpolation polynomial g0 of degree less than z0 with values
u0_i at these nodes, and put `E0=product_(i in I0)(X-x_i)`. When I0 is
empty take g0=0 and E0=1. Over a field with three independent
indeterminates a,b,c0, set

```text
g=g0+E0*(a+bX+c0*X^2).
```

Condition (1) gives degree(g)<=w. The matrix taking a,b,c0 to the three
Hasse jets `(g,g',g''/2)` has columns the jets of E0, X*E0 and X^2*E0.
Its determinant is E0^3. This follows either by the product rule and
triangular row operations, or by factoring the jet matrix for E0 from
the jet matrix for 1,X,X^2. Consequently the substitution is an invertible
affine change of three variables over K(X), and

```text
H(X)=G(X,g,g',g''/2)
```

is not the zero polynomial over K(a,b,c0).

At a node in I0, g has the prescribed value. Its backward Taylor residual

```text
g(x_i+t)-u0_i-t*g'(x_i+t)+t^2*g''(x_i+t)/2
```

has order at least three. Substituting these jets into G therefore gives
H a root of order at least nu_i. Also degree_X(H)<=c by the weighted
degree definition and the bounds on the derivatives of g. The ordinary
root bound proves (2).

Now let m be the source contact order and put

```text
P(X)=product_(i in I0)(X-x_i)^min(m,nu_i).
```

This repair has degree at most c and residual total degree zero. If G
divided all source polynomials, choose a nonzero Q of minimum residual
total degree and write Q=G*Q0. Additivity of contact orders shows that
P*Q0 retains all required contacts. Additivity of weighted degrees, (2),
and the fact that P is a polynomial in X alone show it remains in every
cap of the full source box. Its residual total degree is strictly smaller
than that of Q, a contradiction.

The use of the three formal parameters proves nonvanishing of H; it does
not assume that one of finitely many sampled codewords avoids G. As in
the original descent argument, arbitrary projected subspaces need their
own closure justification.

## How many constant shifts does this permit?

After subtracting a constant c from the direction, the zero nodes are
exactly `{i:u1_i=c}`. Distinct values of c have disjoint level sets. Hence
at most

```text
floor(n/(w-1))
```

constants violate (1). At n=262144,w=131071 this is two. In any coordinate
system with at most 131069 zero direction entries, one may apply the
acceleration-extension criterion without another normalization.

This does not guarantee a shift with both a small acceleration degree and
the needed zero count. In particular, a favorable degree can occur at an
exceptional shift.

## The zero-count boundary for this repair is real

The root-count inequality (2) can already fail at z0=w-1. Let E0 be any
squarefree polynomial of degree z0>=1, let the nodes in I0 be its roots,
and set u0_i=u1_i=0 on those nodes. Put

```text
J=(E0')^2-E0*E0''/2,
G=E0^2*S-E0*E0'*R+J*Y.
```

G is primitive: J is nonzero at every root of E0, so its coefficients
have gcd one. For w=z0+1 its weighted degree is 3*z0-1, attained by the
S coefficient. Its second-Hasse contact order is exactly three at every
root of E0. Expanding E0=t*h proves the order-three lower bound, and the
v coefficient at t=0 equals E0'(x_i)^2, proving equality. Thus

```text
sum_(i in I0) nu_i=3*z0 > 3*z0-1=weightedDegree(G).
```

Indeed G annihilates every `g=E0*(a+bX)`, the entire two-parameter family
of degree-at-most-w polynomials with those zero values. This is a boundary
counterexample to the proposed repair inequality, not a positive full-kernel
containment example or a refutation of properness by some other argument.

## A coordinate change can turn rational acceleration into full degree

For an integer h>=2 consider

```text
F=R-Y*Z^h.
```

It is irreducible, being monic linear in R. Over K(X,Y,R), it has degree h
in Z, while its acceleration is

```text
a=R*Z^h/2=R^2/(2Y).
```

Thus rho=1 and e=h in these coordinates. The permitted transformation
Y->Y+cZ, with c nonzero, gives

```text
F_c=R-Y*Z^h-c*Z^(h+1),
a_c=R*Z^h/2,
Z=(R^2-2*a_c*Y)/(2*c*a_c).
```

The last identity follows directly from F_c=0. The new extension has
degree h+1, but a_c generates it: e=1 and rho=h+1. The source-box degrees
are preserved, whereas the acceleration field degree changes. Therefore
the degree hypothesis must be checked in the same coordinates in which
the properness argument is applied. The repair in (1) can preserve an
original coordinate system when a small number of its direction entries
are zero.

## Full-kernel provenance does not force rho<=2

The following data give complete finite controls in characteristics 257,
65537, and 2130706433:

```text
n=9,w=2,A=5,m=3,D=15,T=6,R cap=1,
nodes=0,...,8,
u0=(0,0,0,0,0,1,1,1,1),
u1=(238,84,40,219,30,215,254,215,247).
```

Use first-order contact weights `(t,v)=(1,2)`. In each field the full
source has 532 columns, local rank 59 and global rank 531. Its uniform
margin and actual kernel dimension are both one. The unique generator F
is primitive and irreducible, with R degree one, Z degree six, and
residual total degree six. Hence F divides the entire nonzero full kernel.
All direction entries are already nonzero.

The selected solution f=0 at gamma=0 has five agreements, and F_R evaluated
on it is a nonzero polynomial. Exhausting the 84 quadratic interpolants on
triples of nodes gives maximum agreement three with u1 in each field.
Thus no quadratic agrees with u1 on five nodes, so the selected scalar is
MCA-bad. The same observation on the first five nodes, followed by the
four remaining nodes, proves that u0,u1 are independent modulo the code.
This does not claim the selected family contains only that one scalar.

In every control the acceleration has **generic algebraic degree six**
over K(X,Y,R), so E=L and e=1. The following exact specializations certify
the generic field-degree statement:

| Characteristic | Specialization (X,Y,R) | Degree in Z | Rank of 1,a,...,a^5 |
|---:|---:|---:|---:|
| 257 | (9,4,6) | 6 | 6 |
| 65537 | (9,1,6) | 6 | 6 |
| 2130706433 | (9,1,1) | 6 | 6 |

The checker verifies degree-six irreducibility at these points using
Rabin's criterion, checks the inverse of 2F_R, and computes the six powers
of a. The coefficient matrix is a specialization of a rational matrix
over K(X,Y,R); all its denominators are defined at the point. Its nonzero
determinant therefore proves generic rank six, not just a rank at a
sampled point. Since the generic extension already has degree six, rho=6.

Irreducibility of the whole F is checked separately. Write F=A0+B0*R in
K[X,Y,Z][R]. For each of X,Y,Z, the checker finds a specialization of the
other two variables which preserves both univariate degrees and makes
A0 and B0 coprime. If they had a common factor of positive degree in that
variable, preservation of the product degrees would preserve its degree,
contradicting the coprime specialization. The three certificates exclude
every possible nonconstant common factor. Gauss's lemma then proves
irreducibility of the primitive linear polynomial in R.

These certificates and matrix ranks persist over extensions of the
coefficient field. They do not realize the production degree flag:
the block length is nine and A^2=25>n*w=18, inside the Johnson range.
They refute an automatic rho<=2 deduction from positivity, universality,
regularity and an MCA-bad selected seed. They do not refute the
acceleration-extension criterion or general production properness.

## Reproduction and remaining scope

```sh
python3 scripts/probes/astra_acceleration_chart_check.py
python3 scripts/probes/astra_acceleration_extension_check.py
```

The first checker reconstructs all three complete first-order kernels,
checks every null vector, proves the stated finite irreducibility and
field-degree certificates, and verifies twelve generic-jet determinants.
Its zero-direction boundary controls have contact sum one greater than
their weighted degree. It also checks the generic-jet substitution on a
polynomial with positive contact at a zero-direction node. The second
checker revalidates the original extension controls after sharing the
contact expansion routine with the new first-order examples.

General high-degree acceleration, the actual production factor, the full
phase recurrence, independent review and Lean formalization remain open.

The [full-kernel properness follow-up](astra_full_kernel_properness-2026-09-05.md)
constructs proper second-Hasse pullbacks for these three degree-six factors.
Thus their failure of the low-degree sufficient condition is not a failure
of properness in these finite examples. General production properness
remains open.
