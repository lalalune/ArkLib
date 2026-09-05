# Selected agreements force an exact Jacobi divisibility constraint

A regular selected polynomial supplies information absent from the
[far-line quotient construction](astra_far_word_kernel-2026-09-05.md).
Its linearized polynomial deformations satisfy a new locator divisibility
identity. If the factor's total contact order on that polynomial's agreement
set exceeds its contact weight by more than one, no nonzero polynomial
deformation with the seed held fixed is possible.

This is a written mathematical lemma with bounded exact checks. It is not
Lean-formalized and does not reduce the moving allowance or bound the number
of isolated selected solutions. In particular, the current total-budget
excess of 17138836560697490 is unchanged by this note.

## Actual selected-graph hypotheses

Let F be a nonzero polynomial in K[X,Y,R,Z], of contact weight c for weights
(X,Y,R,Z)=(1,w,w-1,0), with w>=1. At distinct nodes x_i use the received
affine values u0_i+Z*u1_i and the contact substitution

    X=x_i+t, Y=u0_i+Z*u1_i+R*t+v,
    weight(t,v,R,Z)=(1,2,0,0).

Let nu_i be F's contact order, and let a selected pair (f,gamma) satisfy

    deg f<=w, F(X,f,f',gamma)=0,
    h(X):=F_R(X,f,f',gamma) != 0.

Write S for its agreement set, where f(x_i)=u0_i+gamma*u1_i, and put

    a(X)=F_Y(X,f,f',gamma), b(X)=F_Z(X,f,f',gamma),
    N_S=sum_(i in S) nu_i.

These are the polynomial-solution, degree, and regularity fields of
`RCN159.ResidualStage`, together with its actual agreement predicate. The
source pin is
[`032154395c51fd6f77715a7f42d9a987ab9fb48a`](https://github.com/proximity-prize/proximity-prize/blob/032154395c51fd6f77715a7f42d9a987ab9fb48a/ProximityPrize/SubmissionLower/PackedLegacyCore1.lean#L19154).
The proof uses neither geometric irreducibility nor a universal-divisor
assumption, so it also applies before or after those extra fields are supplied,
provided the actual polynomial, contacts, and selected graph are retained.

A polynomial Jacobi deformation is a pair (g,eta), deg g<=w and eta in K,
such that

    h*g' + a*g + eta*b = 0.                               (1)

Equivalently it is a first-order solution (f+epsilon*g,gamma+epsilon*eta)
of the full polynomial identity over K[epsilon]/(epsilon^2). The word
"deformation" here means this linear equation, not an assumed curve or a
family of distinct actual solutions.

## Local identities and exact divisor

At every i in S, with t=X-x_i, one has

    ord_i(h) >= max(0,nu_i-1),
    ord_i(h+t*a) >= nu_i,
    ord_i(b+u1_i*a) >= nu_i.                              (2)

To prove these statements, write the localized polynomial as F_tilde.
In its coordinates, the original derivatives are

    F_Y = partial_v F_tilde,
    F_R = partial_R F_tilde - t*partial_v F_tilde,
    F_Z = partial_Z F_tilde - u1_i*partial_v F_tilde.

The derivatives partial_R and partial_Z do not lower contact weight;
partial_v lowers it by at most two. Along the selected graph,

    v=f(x_i+t)-f(x_i)-t*f'(x_i+t)

is divisible by t^2, so contact lower bounds become ordinary t-adic bounds.
This proves (2), in every characteristic. It also gives ord_i(a)>=nu_i-2
when nu_i>=2. If nu_i=1 then h+t*a is divisible by t and a is a polynomial,
so h is divisible by t as well.

If g is nonzero and solves the fixed-seed equation h*g'+a*g=0, then

    product_(i in S)(X-x_i)^nu_i divides h*g.              (3)

At a node where g vanishes, this follows from its positive order and the
first bound in (2). If g does not vanish, both g and g-t*g' are local units.
The identity

    g*(h+t*a)=h*(g-t*g')

and the second bound in (2) then give ord_i(h)>=nu_i. Distinct node factors
are coprime, proving (3). Since h and g are nonzero, taking degrees gives

    N_S <= deg h+deg g <= c-(w-1)+w = c+1.               (4)

Consequently, if N_S>c+1, the fixed-seed polynomial Jacobi kernel is zero.
The projection (g,eta) -> eta is then injective on all solutions of (1),
so their K-vector-space dimension is at most one. This is a characteristic-
free conclusion; no integration or division by factorials is used.

## What the remaining seed direction must interpolate

Call an agreement node minimal when ord_i(h)=nu_i-1, and let M be the
number of such nodes. A minimal node necessarily has nu_i>=2: (2) excludes
nu_i=1, and nu_i=0 would ask for order -1. At a minimal node,
ord_i(a)=nu_i-2, with h=-t*a modulo t^nu_i. Similarly b=-u1_i*a modulo
t^nu_i. Substitution into (1) gives

    a*(g-t*g'-eta*u1_i) = 0 mod t^nu_i,

which forces

    g(x_i)=eta*u1_i.                                    (5)

Every nonminimal agreement node contributes at least nu_i roots to h;
every minimal node contributes nu_i-1. Thus

    M >= N_S-deg h >= N_S-c+w-1.                        (6)

When this lower bound exceeds w, a fixed-seed polynomial g must vanish,
recovering (4). If eta is nonzero, normalize it to one: then g interpolates
u1 on all M minimal nodes, and f-gamma*g interpolates u0 there.

For example, if u0 has fewer than A agreements with every degree-at-most-w
polynomial, a nonzero eta direction requires M<=A-1. Hence such a direction
also requires N_S<=deg h+A-1<=c-w+A. This conditional strict refinement
does not hold for an arbitrary selected point when its Jacobi space is zero.

## The critical arithmetic profile: a rigidity test, not an exclusion

For w=131071, an agreement set of size 181353, and the arithmetic profile
nu_i=34 on that set, N_S=6166002. The two explicit weight choices give:

| Specified actual c | Upper bound on deg h | Lower bound on M | M lower bound minus w |
|---:|---:|---:|---:|
| 6160327 | 6029257 | 136745 | 5674 |
| 6160337 | 6029267 | 136735 | 5664 |

Both imply dimension at most one for polynomial Jacobi deformations, and
zero dimension when the seed is fixed. These rows specify the actual weight
c; a lower bound c>=6160327 cannot be substituted for an upper bound on
deg h. The uniform order-34 profile is still not a constructed selected
family or universal factor, and actual profiles need not satisfy N_S>c+1.

For the other explicit profile with exactly H agreement nodes of contact 57
and the other 181353-H agreement nodes of contact 33, the same gate at
specified actual c=6160327 is

    33*181353+24*H > 6160328,
    equivalently H>=7320.

At H=7320 the minimal-node lower bound is 131072=w+1. At H=7319 it is
131048, which does not establish rigidity by this test. The hypothesis is
about high-contact nodes inside this selected polynomial's agreement set;
neither that count nor the two-level profile is automatic from the degree
flag or the existing global contact constraints.

The [earlier H-incidence inequality](astra_incidence_derivative_repair-2026-09-04.md)
only bounded sum_(i in S) max(0,nu_i-1) by c-(w-1). Here (3) supplies an
additional divisor whenever a nonzero fixed-seed deformation exists. It is
the existence qualifier, rather than any change to that earlier degree bound,
that yields the stronger conditional restriction.

## Bounded sharpness controls and where the proof stops

Let V=X^n-1 with distinct roots, and n>=w+2. The non-plane polynomial

    F_1=V'*(Y-Z)-V*R+(Y-Z)^2

has selected solutions f_gamma=gamma and received values u0=0,u1=1.
Every node has contact two. Along a selected graph, h=-V, a=V', b=-V',
and the degree-at-most-w Jacobi space is exactly the span of (g,eta)=(1,1).
Thus the dimension-one conclusion is sharp for the lemma's hypotheses.
This control has a codeword received origin and an affine pencil of solutions;
it is not a far-word/no-large-pencil witness.

A second control uses u0=1/x, u1=-1/x, selected gamma=1 and f=0. Put

    Phi=X*Y-1+Z,
    F_2=(V-X*V')*Y+X*V*R+(1-Z)*V'+Phi^2.

Again every node has contact two and the solution is regular. Here
h=X*V, a=V-X*V', b=-V', and the polynomial Jacobi space is zero: (5)
would require a nonzero eta direction to interpolate -1/x at all n nodes,
impossible when n>w+1. This control has a far origin but only a singleton
selected family and a direction dependent modulo the code. No universality
or binding C2 flag is asserted for either example.

Run the [checker](../../scripts/probes/astra_selected_family_constraint_check.py):

    python3 scripts/probes/astra_selected_family_constraint_check.py

It expands the contacts and checks all six Jacobi matrices for three fixed
small-field/node choices, then verifies the two critical arithmetic rows.
The general divisor proof is not inferred from those finite checks.

Finally, polynomial Jacobi rigidity does not bound the number of isolated
selected solutions. A universal divisor of a full source kernel does not,
by definition, supply a nonzero Jacobi deformation, nor does a large finite
selected set automatically supply a curve of solutions. Those would be
additional bridges, not consequences proved here. Moreover the generic
surface tangent direction used in the C2 moving count need not arise from a
polynomial g satisfying (1). Consequently no decrease of the quotient
allowance, moving budget, or selected-factor count follows from this lemma
alone. Further application must establish one of those missing connections
using the actual source and family, rather than equating local rigidity with
a cardinality estimate.

The [full-kernel follow-up](astra_contact_variation-2026-09-05.md) supplies
independent received words and a genuine singleton MCA-bad family whose full
source kernel is one-dimensional. Its extracted factor has zero polynomial
Jacobi space and transverse first two tails. That example has R degree one;
the binding C2 flag and a large selected family remain absent.
