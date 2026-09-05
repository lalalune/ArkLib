# Properness in the squarefree-denominator construction

For the rational-direction family below, a positive uniform second-Hasse
margin forces a proper pullback. This holds for arbitrary parameters
satisfying the stated hypotheses, rather than only for the tested finite
examples. The key is that the subspace of contained equations has dimension
exactly one, whereas positivity and the agreement equations force the full
kernel to have dimension at least two.

This is a written argument with exact finite controls, pending independent
review and Lean formalization. It handles a structured extension of the
[earlier containment construction](astra_hasse_containment-2026-09-05.md).
It does not establish properness for arbitrary received directions or the
production sources, and gives no improved prize bound or score.

## Statement

Work over a field of characteristic different from two. Let n=A+e distinct
nodes be partitioned into A agreement nodes and e error nodes, with e>=1,
w>=2. Write W and E for their respective monic locator polynomials. Let
L be squarefree of degree ell>=1 and nonzero at every node. Set

```text
u0=0 at the A agreement nodes, and nonzero at every error node;
u1(x)=1/L(x) at every node;
D=2A+3e+ell+w-1 <= 3A.
```

Let V be the full source of polynomials

```text
Q=a0(X)Y+b0(X)R+c0(X)S+d0(X)Z+e0(X)
```

of weighted degree less than D, with variable weights (1,w,w-1,w-2,0),
satisfying second-Hasse contact at least three at every node. Thus the local
substitution is Y=u0+u1*Z+tR-t^2*S+v, with weight(v)=3.

Define the primitive first-order factor and its ordinary total derivative by

```text
F=(L'W-LW')Y+LW*R+W'Z,
delta(X)=1, delta(Y)=R, delta(R)=2S, delta(Z)=0.
```

The coefficients of Y and R in F are coprime: at a root of W the former is
-LW', and at a root of L it is L'W. Squarefreeness and disjoint roots make
these nonzero. Thus F is primitive and irreducible, being linear in R, and
F_R=LW is nonzero. On its regular graph use

```text
S=-(F_X+R*F_Y)/(2F_R).
```

Let V_cont be the subspace of V whose pullbacks vanish identically on F.
Then

```text
dim(V_cont)=1,
dim(V) >= w+4ell-A-1.                                  (1)
```

The uniform dimension margin is

```text
M=5D-3w+3-12n=-2A+3e+5ell+2w-2.                        (2)
```

If M>0, then dim(V)>=2, so some Q in V has a proper pullback. More
quantitatively, dim(V/V_cont)>=w+4ell-A-2>=1.

The same root argument as for the other second-Hasse sources applies:
every polynomial of degree at most w with at least A agreements satisfies
Q(X,f,f',f''/2,gamma)=0, since its degree is less than D<=3A. Properness here
therefore supplies an additional equation on the selected solutions for
this family.

## The full kernel's lower dimension bound

There are C=5D-3w+3 monomials, with 12 local contact equations at each node:
three t coefficients in each of the constant, Z, R, and S channels.

At the A agreement nodes, the 3A constant-channel equations involve only
e0. Their map has rank D: a polynomial of degree less than D with these
vanishings is divisible by W^3, hence is zero because D<=3A. Consequently
there are 3A-D dependencies among this subset of the full equations.
They remain dependencies in the complete matrix. Therefore

```text
dim(V) >= C-12n+(3A-D)=w+4ell-A-1.                     (3)
```

The root bound D<=3A gives A>=w+3e+ell-1. Combining it with M>0 first gives
ell>=e+1. Since all parameters are integers, (2) then implies

```text
2A <= 3e+5ell+2w-3 <= 8ell+2w-6,
A <= w+4ell-3.
```

Substitution in (3) gives dim(V)>=2. Merely counting the uniform margin
would miss this conclusion in the M=1 cases; the dependent agreement rows
are essential.

## Classifying every contained equation

The constant-channel argument already gives e0=0. At each error node,
u0 is nonzero, so a0 has order at least three there. The R, S, and Z
channels then force the same for b0,c0,d0. Divide Q by E^3 and write

```text
Q/E^3=aY+bR+cS+dZ,
deg a<=2A+ell-2, deg b<=2A+ell-1,
deg c<=2A+ell,   deg d<=2A+ell+w-2.                    (4)
```

At every root x of W, the R and S channels imply

```text
b(x)=0, (b'+a)(x)=0, (b''/2+a')(x)=0,
c(x)=c'(x)=0, (c''/2-a)(x)=0.
```

Put J_W=(W')^2-WW''/2. Successive division by W^2, using these value and
derivative equations and (4), gives polynomials t,B,C with

```text
c=W^2*t,                     deg t<=ell,
b=-tWW'+B W^2,               deg B<=ell-1,
a=t J_W-BWW'+C W^2,          deg C<=ell-2.              (5)
```

A negative degree bound means the zero polynomial. In particular, these
are forms for every full-kernel vector, before any containment assumption.

The rational function f=W/L, with Z=0, solves F=0. If Q is contained,
substitute f,f',f''/2 in (5) and clear L^3. With J_L=(L')^2-LL''/2 the
result is exactly

```text
W^3 * (t J_L-B L L'+C L^2)=0.                           (6)
```

Modulo L, J_L equals (L')^2 and is a unit because L is squarefree. Hence
L divides t. The degree bound makes t=lambda L for a scalar lambda.
Dividing (6) by L and reducing modulo L gives B=lambda L'; its strict
degree bound leaves no multiple of L. Substitution back gives
C=lambda L''/2.

The rational function f=1/L with Z=1 also solves F=0. Substitution now
forces d=-lambda J_W. Thus every contained Q is a scalar multiple of
E^3 P, where

```text
P=(L J_W-L'WW'+L''W^2/2)Y
  +(L'W^2-LWW')R+LW^2 S-J_W Z
 =(W/2)*delta(F)-W'*F.                                 (7)
```

Conversely, E^3 P belongs to V and is contained. The last identity proves
containment. Its degrees satisfy (4), and (5) gives the R and S contact
conditions. At a root x of W its Z channel is a+L(x)d. Expanding
W=t*h and L=L(x)+tL'(x)+t^2L''(x)/2+O(t^3) shows this is divisible by t^3.
The constant channel is zero, and E^3 supplies contact at error nodes.
Its S coefficient E^3 LW^2 is nonzero. This proves dim(V_cont)=1.

## Exact checks and limitations

Run with Python and NumPy:

```sh
python3 scripts/probes/astra_squarefree_denominator_check.py
```

The checker uses nodes 0,...,n-1, L=product_(j=1..ell)(X+j), and w=2.
It checks six geometries at each of characteristics 257, 65537, and
2130706433:

| e | ell | A | D | Uniform margin | Actual nullity | Contained dimension |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | 2 | 6 | 18 | 3 | 3 | 1 |
| 1 | 2 | 7 | 20 | 1 | 2 | 1 |
| 2 | 3 | 10 | 30 | 3 | 3 | 1 |
| 2 | 3 | 11 | 32 | 1 | 2 | 1 |
| 3 | 4 | 14 | 42 | 3 | 3 | 1 |
| 3 | 4 | 15 | 44 | 1 | 2 | 1 |

All 18 complete matrices are reconstructed and their full nullspaces
checked. Every direct matrix column at every node is compared with the
separate contact expansion routine: 37845 comparisons. All 45 returned
kernel basis vectors satisfy the coefficient forms (5) and identity (6).
The exact restriction map on the full kernel, obtained from the two
rational solutions, has kernel dimension one in every case. This tests
containment as a polynomial identity, without inferring it from zero
evaluations at sampled points. A separate integer scan checks 27420
parameter instances of the inequalities following (3).

The squarefree hypothesis is substantive: (6) uses invertibility of L'
modulo L. Repeated poles require a different analysis. The total source
degree is one, and these small geometries lie inside the Johnson range.
No argument here covers the general high-degree production factor, changes
the companion allowance, or closes the grand challenges.
