# Incidence bounds for curves carrying MCA decodings

This note gives an auxiliary degree bound, not a universal predecessor bound.
No low-degree carrier for arbitrary MCA events is constructed. The argument
applies to any Reed--Solomon evaluation domain of distinct field elements; it
does not use multiplicative-subgroup structure. It is not Lean-formalized.

Let the domain have size n, let C consist of evaluations of polynomials of
degree less than k, and fix received rows (u0,u1). Assume 1<=k<=t<=n. A decoding
point is

```text
(gamma,c0,...,c{k-1}) in affine (k+1)-space,
w(X)=sum_j c_j X^j.
```

For each evaluation point x define the affine hyperplane

```text
Hx: w(x)=u0(x)+gamma*u1(x).
```

A threshold-t MCA witness supplies a point lying on at least t of these
hyperplanes. Its chosen support must also fail `pairJointAgreesOn`, exactly as
in [Errors.lean](../../ArkLib/Data/CodingTheory/ProximityGap/Errors.lean).
Selecting one witness point per scalar makes their number equal to the number
of selected distinct scalars; several decoding points for one scalar cannot
increase that count.

## Nonlinear decoding curves

Let Gamma be an irreducible nonlinear curve over the algebraic closure in this
affine space. Its projective closure has degree D. Let U be the number of Hx
that contain Gamma. Then

```text
U<=k-1.
```

Indeed, any k of the equations Hx determine all k coefficients of w as affine
functions of gamma, by the invertibility of the evaluation Vandermonde matrix.
Their intersection is an affine line. An irreducible curve contained there
would be that line, contrary to nonlinearity.

Every other Hx intersects Gamma in at most D distinct geometric points. This
is the hyperplane-section degree formula, including multiplicities; points at
infinity can only reduce the number counted in the affine chart. A primary
reference is [Vakil, Foundations of Algebraic Geometry, Class 31,
Exercise 1.8](https://math.stanford.edu/~vakil/0506-216/216class31.pdf).

If B selected decoding points on Gamma each agree in at least t coordinates,
each contributes at least t-U incidences with the noncontaining hyperplanes.
Counting those incidences in both directions gives

```text
B*(t-U)<=D*(n-U),
B<=floor(D*(n-k+1)/(t-k+1)).
```

The second inequality follows because (n-U)/(t-U) is nondecreasing in U for
U<t<=n. This part uses the agreement condition alone, so it also bounds points
that happen not to be MCA-bad.

For the production predecessor,

```text
n=1073741824, k=536870912, t=715827884,
(n-k+1)/(t-k+1)=3-6/178956973.
```

Consequently every such degree-D curve carries at most 3D-1 selected distinct
bad scalars. In particular, a conic carries at most five and a cubic at most
eight. These are bounds conditional on the specified carrier, not claims
that a carrier exists.

## Line components and total degree three

A nonvertical affine line is a fixed polynomial pencil w=f+gamma*g. If it
contains two distinct field-rational decoding points, f and g have
coefficients in the field. A line with at most one such point contributes at
most one scalar anyway. A vertical line also contributes at most one scalar.

For a fixed field-defined pencil let U be its exact joint-core size. At each
coordinate outside that core the nonzero residual pair cancels at at most one
finite gamma, so the outside cancellation sets for different scalars are
disjoint. A threshold-t MCA witness decoded by this pencil needs at least

```text
max(1,t-U)
```

outside cancellations. The t-U term comes from agreement; the 1 comes from
the no-joint clause on the same support. Thus its scalar yield is at most

```text
floor((n-U)/max(1,t-U))<=n-t+1.
```

At the production predecessor n-t+1=(n-1)/3. A reduced pure one-dimensional
curve carrier of total projective degree at most three therefore suffices for
a scalar cap n-1:
three lines give n-1, a line plus a conic gives at most (n-1)/3+5, and an
irreducible cubic gives at most eight. Assign overlapping points to one
component before summing. Isolated components are not allowed as uncounted
additions to this degree budget. No existence theorem for such a carrier is asserted.

More generally, L line components and nonlinear components of total degree D
and number c give the bound

```text
L*(n-t+1)+3D-c
```

at these production parameters. This geometric degree budget could be checked
independently of counting the selected points if an auxiliary carrier were
constructed.

## A curve of pairs is a different object

A curve of pairs (f_lambda,g_lambda) in C^2 generally sweeps out the
two-dimensional set (gamma,f_lambda+gamma*g_lambda). The preceding
one-dimensional decoding-curve bound does not apply to that surface.

There is a separate incidence bound. On an irreducible nonconstant pair curve
of degree D, at most k-1 coordinates can be joint agreements identically along
the curve: k such coordinates would uniquely determine both polynomials and
make the curve a point. At each other coordinate at least one of the two
joint-agreement hyperplanes does not contain the curve; choose one. Any pair
that jointly agrees there lies on its degree-at-most-D section. Therefore the
number of distinct pairs having joint-core size at least q>=k is at most

```text
floor(D*(n-k+1)/(q-k+1)).
```

At q=715827883 the ratio is 3-3/178956972. An affine line of pairs has at most
two qualifying pairs, and a conic at most five. Summing five pencil yields
does not establish the desired n bound. A curve-of-pairs degree hypothesis
must not be silently substituted for a decoding-curve degree hypothesis.

## Why the actual event equations supply no carrier degree bound

The entire threshold-agreement locus is

```text
V_t = union over |S|=t of (intersection over x in S of Hx).
```

For t>=k, every intersection in this finite union is an affine line, a point,
or empty: the first k equations determine w affinely in gamma, and each
remaining equation either imposes no new condition or fixes gamma. Every
positive-dimensional component is therefore already an affine polynomial
pencil. The remaining decoding points are isolated arrangement points.

An MCA event may also occur at a point on a line component, using a support
that includes a nonzero residual outside that line's joint core. The no-joint
clause does not justify deleting all line components.

Thus a nonlinear carrier would have to be an independently constructed
auxiliary variety containing the isolated decoding points. The event equations
give no degree-three carrier automatically. Taking the degree of their finite
union would simply reintroduce the uncontrolled isolated-point count. The
attribution problem recorded in
[_SYZ29YieldLawD4Gluing.lean](../../ArkLib/Data/CodingTheory/ProximityGap/Frontier/_SYZ29YieldLawD4Gluing.lean)
remains open; this note does not discharge the universal predecessor census.
