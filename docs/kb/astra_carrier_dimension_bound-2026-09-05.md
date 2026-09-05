# Counting decodings on carriers of controlled dimension and degree

An actual algebraic carrier of dimension r and degree D gives a quantitative
list bound that uses the independence of Reed--Solomon evaluation equations.
For a fixed received word the bound is

```text
D * product_(j=1..r) (n-k+j)/(A-k+j).
```

There is a separate MCA bound, retaining the no-joint condition on the same
witness support. In the production predecessor instance, a single affine
plane carrying one witness per bad scalar would imply at most n-13 bad
scalars. **No such universal plane or other sufficiently small carrier has
been constructed.** These are written conditional counting lemmas, not a
prize solution or newly Lean-verified theorems.

## Degree convention and the hyperplane step

Work over an algebraic closure of the coefficient field K. For an irreducible
affine variety, degree means the degree of its projective closure. For a
reducible carrier use the sum of the degrees of all its irreducible components,
including zero-dimensional components. They cannot be omitted from the budget.

Intersecting an irreducible r-dimensional variety with a hyperplane that does
not contain it gives an empty set or components of dimension r-1 whose degrees
sum to at most its degree. Indeed, projective hyperplane section has the same
degree, counted with multiplicities; taking the reduced affine part can only
decrease it. This follows from the Hilbert-polynomial exact sequence for
multiplication by the hyperplane equation. See
[Vakil, Class 31, Exercise 1.8](https://math.stanford.edu/~vakil/0506-216/216class31.pdf).
All uses below are proper hyperplane sections; no transversality is assumed.

## Fixed-word scalar decoding

Let x_1,...,x_n be distinct field elements, let 1<=k<=A<=n, and identify
degree-less-than-k polynomials with affine coefficient space of dimension k.
Fix a received word v. The node equations are affine hyperplanes

```text
H_i: f(x_i)=v_i.
```

Let V be an irreducible carrier of dimension r>=1 and degree D. If c of the
H_i contain V, then c<=k-r. Any c<=k evaluation equations are independent,
so their common solution space, when nonempty, has dimension k-c. Any k
such equations determine at most one polynomial. This proves the assertion
also when considering a hypothetical c>=k.

Let L(V) be the number of points of V agreeing with v at at least A nodes.
This is finite: every such point is determined by any k of its agreement
nodes. In fact its polynomial coefficients are in K, by interpolation.
Define

```text
R_0=1,
R_r=product_(j=1..r) (n-k+j)/(A-k+j).
```

We claim L(V)<=D*R_r. For dimension zero, distinct points are counted by
degree. For r>=1, every counted point lies on at least A-c of the n-c
noncontaining hyperplanes. Apply the induction hypothesis to each proper
section and sum its component degrees:

```text
L(V)*(A-c) <= (n-c)*D*R_(r-1).
```

The ratio (n-c)/(A-c) is nondecreasing in c because A<=n. Substituting
c<=k-r proves the claim. Reducible carriers of dimensions at most r obey
the same bound with total component degree D, because R_j is nondecreasing
in j and points can be assigned to one component before summing.

Equivalently, the integer bound is

```text
L(V)<=floor(D*binomial(n-k+r,r)/binomial(A-k+r,r)).       (1)
```

For r=k and V the entire coefficient space, this is the usual MDS incidence
bound binomial(n,k)/binomial(A,k). For r=1 it is the earlier curve incidence
bound. The useful new input would be a proven small degree and dimension of
a carrier containing the full list; taking that list itself as a finite
carrier merely restates the unknown count.

## MCA witnesses: a different recurrence

For fixed received words u0,u1 use affine coordinates (gamma,f), of dimension
k+1, and node hyperplanes

```text
H_i: f(x_i)=u0_i+gamma*u1_i.
```

Assume k+1<=t<=n. Select one actual MCA witness point per distinct bad
scalar, retaining its same-support no-joint condition. Let the selected
points lie in a carrier V. The scalar formula (1) cannot be applied directly:
gamma varies, so this is not a list around a fixed word in the original code.

For a line component the selected scalar count is at most n-t+1. A vertical
line contributes at most one scalar. A nonvertical line containing two
K-rational selected points is a polynomial pencil f=f0+gamma*f1 over K;
otherwise it contributes at most one scalar. If its exact joint core has
c nodes, each selected point requires at least max(1,t-c) cancellations
outside the core. Each outside node cancels at at most one scalar. Hence

```text
#selected <= floor((n-c)/max(1,t-c)) <= n-t+1.
```

The final inequality follows separately from c>=t-1 and c<=t-1; in the
second case (n-c)/(t-c)<=n-t+1. The no-joint condition is what supplies the
extra one when the joint core is large.

For an irreducible nonlinear curve, at most k-1 node hyperplanes contain
it: k equations would place it in an affine line. The proper-section count
gives at most D*(n-k+1)/(t-k+1), which is at most D*(n-t+1), since

```text
(n-t+1)*(t-k+1)-(n-k+1)=(t-k)*(n-t)>=0.
```

These curve arguments are developed in the
[earlier decoding-curve note](astra_mca_decoding_curve_incidence-2026-09-04.md).
They supply the base case of the following higher-dimensional recurrence:

```text
Q_0=1, Q_1=n-t+1,
Q_r=(n-t+1)*product_(j=2..r) (n-k-1+j)/(t-k-1+j), r>=2.
```

An irreducible r-dimensional carrier with r>=2 is contained in at most
k+1-r node hyperplanes. The Vandermonde equations solve f as an affine
function of gamma once k nodes are specified, and before that each new
node imposes an independent equation. Induction on proper hyperplane
sections, exactly as above, gives

```text
#selected distinct bad scalars <= floor(D*Q_r).          (2)
```

For mixed-dimensional components use their summed degree and the maximum
dimension; Q_r is nondecreasing. Sections inherit the already selected
points, so one-per-scalar and the original witness no-joint condition are
preserved at every induction step.

At production n=6b-2=2^30, k=3b-1, t=4b, b=178956971,

```text
Q_2=(2b-1)*3b/(b+2)=n-13+30/(b+2),
floor(Q_2)=n-13=1073741811.
```

Thus an actual affine plane containing the selected witness points suffices
for this production predecessor cap. A degree-two surface would only give
twice this allowance by (2), which does not suffice. No plane extraction is
asserted, and neither a surface in differential coordinates (Y,R,Z) nor a
curve of polynomial pairs automatically gives the required coefficient-space
carrier or its degree.

## Numerical consumers and finite checks

At the production punctured scalar parameters n=1073741823,k=536870912,
A=715827883, a surface of degree D gives the explicit factor R_2 close to 9.
At companion n=262144,k=131072,A=181353 the surface factor is less than 7.
The checker computes the exact largest sufficient degree at each numerical
budget. These are conditional degree allowances, not established degrees.

Run `python3 scripts/probes/astra_carrier_dimension_check.py`.
It checks exact scalar lists on affine subspaces, a parabola, and a quadric
surface over F7, and an actual F17 MCA plane with three selected bad scalars.
The MCA check uses the full agreement support and independently tests whether
the two received words have joint codeword explanations there. The geometric
induction above is not inferred from these finite examples.

The subsequent [fixed-word differential construction](astra_scalar_differential_carrier-2026-09-05.md)
uses the r=1 scalar case to bound the complete list at the companion profile.
It supplies a curve carrier through a rational Taylor map, accounts separately
for singular solutions, and gives a written list bound below the numerical
budget. Independent proof review and Lean formalization are pending. It does
not supply the missing MCA carrier or the grand production rank bound.
