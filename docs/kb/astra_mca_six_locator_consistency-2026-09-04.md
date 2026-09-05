# Locator consistency for an equal-core six-pencil example

This note records necessary polynomial identities beyond the incidence
conditions in the [six-pencil classification](astra_mca_six_pencil_types-2026-09-04.md).
The arguments have an independent mathematical review and are not
Lean-formalized. They do not by themselves exclude the remaining configurations. Work over a
field K on n distinct nodes, with six distinct polynomial pairs whose exact
joint cores have size `4b-2` and cover the domain, where

```text
n=6b-2, d=3b-2, |Di|=2b.
```

Assume their whole configuration is not affine-collinear over K(X). Let
`V=product_{x in Omega}(X-x)`, let Li be the locator of the core Ai, and let
`Wi=V/Li` be the monic degree-2b locator of its absence set Di.

## The six absence locators span exactly three dimensions

Set `Qi=Wi*(1,fi,gi)`, a row of three polynomials. The exact determinant
divisors proved in the [line-flat note](astra_mca_six_pencil_flats-2026-09-04.md)
give

```text
det(Qi,Qj,Qk) = a_ijk * V^2,     a_ijk in K.
```

Here a_ijk is zero precisely for a collinear triple; otherwise it is nonzero.
Choose three noncollinear pairs. Their Q rows form a basis over K(X), and
Cramer's rule expresses every other Q row in that basis with coefficients
equal to ratios of the constants a_ijk. Thus the six Q rows span a
three-dimensional vector space over K as well.

Projection onto the first polynomial component is injective on this K-space.
Indeed, suppose a constant linear combination has first component zero.
At each domain node, an absent row vanishes because Wi does, while every
present pair agrees with the received pair. The other two components of the
combination therefore vanish there as well. Each has degree at most
`2b+d=5b-2<n`, so the n distinct roots force it to be zero as a polynomial.
Thus the combination is the zero vector; equivalently, its coefficients in
the chosen three-row basis all vanish.

Consequently the six absence locators Wi span **exactly three dimensions over
K**, and their constant linear dependencies are precisely those of the Q
rows. Their triple-dependence pattern matches the rational affine
collinearity pattern of the polynomial pairs. Since all Wi are monic of the
same degree, they lie in an affine plane inside that three-dimensional
polynomial space.

This is a necessary condition on the actual root polynomials, not a conclusion
that arbitrary admissible subset sizes produce a suitable interpolation
kernel.

## Every collinear triple forces three dependent private locators

Take a collinear triple 1,2,3 and a configured pair Q off its line. The
complete-line-flat rule partitions the domain into

```text
T: all three absent,                size t;
Ui=Di\T: only i absent,             size 2b-t each;
E: all three present,               size 2t-2.
```

The three Ui are pairwise disjoint. Write their monic locators as Ui(X), and
the locators of T,E as T(X),E(X). Then

```text
L1=E*U2*U3,   L2=E*U1*U3,   L3=E*U1*U2,
V=T*E*U1*U2*U3.
```

Write differences along the triple's primitive polynomial direction v as
`Pi-Pj=hij*v`. Using Q off the line, exact determinant ratios give

```text
h12/h13 = nonzero constant * U3/U2,
h23/h13 = nonzero constant * U1/U2.
```

The identity `h12-h13+h23=0` therefore yields

```text
lambda1*U1 + lambda2*U2 + lambda3*U3 = 0,
every lambdai is a nonzero field constant.
```

The Ui are monic of the same degree, so also `lambda1+lambda2+lambda3=0`.
Their product divides V, and the remaining factor T*E has degree `3t-2`.
On a roots-of-unity domain V is `X^n-1`. The rational function U1/U2 thus
takes three specified projective values on the three disjoint Ui root sets,
covering `n-(3t-2)` domain points.

For the production one-triple incidence escape with t=4, this becomes

```text
degree(U1)=degree(U2)=degree(U3)=357913938,
U1*U2*U3 divides X^1073741824-1,
degree of the remaining factor=10,
a constant relation with all three coefficients nonzero.
```

The six full absence locators must additionally satisfy the common
three-dimensional-span condition above and all of the prescribed cross-pair
root intersections. Neither the incidence weights nor this necessary
relation establishes that such polynomials exist in the production field.

## What the existing SYZ results do and do not supply

The relation is exactly the constant-cofactor/level-set situation formalized
in [_SYZ48BalancedInterior.lean](../../ArkLib/Data/CodingTheory/ProximityGap/Frontier/_SYZ48BalancedInterior.lean)
and [_SYZ49CyclotomicGcd.lean](../../ArkLib/Data/CodingTheory/ProximityGap/Frontier/_SYZ49CyclotomicGcd.lean).
The latter's `combination_isRoot_iff_ratio` converts the relation to a rational
level set, and `gcd_natDegree_le_max` bounds that level set by the common
degree. Here the required level set attains that degree, so this inequality
alone gives no contradiction.

SYZ49 also records an explicit noncoset constant-syzygy witness on a proper
roots-of-unity subgroup over F37. Thus domain membership alone is not a
general exclusion theorem. [_SYZ50WitnessRealizability.lean](../../ArkLib/Data/CodingTheory/ProximityGap/Frontier/_SYZ50WitnessRealizability.lean)
separately distinguishes root-domain membership, support-size feasibility,
and lifting to an over-budget stack. Those examples do not establish a
witness or an exclusion for this dyadic production domain with ten remaining
points.

Finally, the later [_SYZ69ParityClassification.lean](../../ArkLib/Data/CodingTheory/ProximityGap/Frontier/_SYZ69ParityClassification.lean)
states its two-class law conditionally on the empty-middle input. A constant
syzygy is in the floor-attained branch, not an excluded middle-gap branch.
Sampled gap or scalar-yield tables in earlier files cannot be substituted for
a uniform production-field theorem here.

A next proof would need to exclude these actual production-domain locator
identities, or bound the scalar yield after imposing the remaining six-pencil
interpolation constraints. The source results reviewed above do neither.

The subsequent [cyclic-shift and cover analysis](astra_mca_cyclotomic_locator_constraints-2026-09-05.md)
shows that a common multiplicative power lift can have order at most two.
It also supplies an actual-prime length-16 example and explains why inversion,
the elementary elliptic-cover genus inequality, and the prime-field point count
do not give a production exclusion.
