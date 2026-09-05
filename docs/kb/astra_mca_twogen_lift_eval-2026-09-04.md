# A compact production evaluator for the two-generator construction

The recursive balanced partition and its two-point deletion can be evaluated
at `n=2^30` using fourteen rational summands per ordinary coordinate. The first
deleted pair, exponents `0,1`, is admissible in the actual production field.
Its four private directions are distinct and avoid the entire fourth-quarter
image. These exact checks support the construction at production size, but
**injectivity across all quarters remains unproved and unenumerated**.

The [two-generator bridge](astra_mca_two_generator_bridge-2026-09-04.md) proves the
conversion from distinct residual directions into actual MCA witnesses; the
[finite probe note](astra_mca_two_generator_probe-2026-09-04.md) records the
complete checks at n=16,64,256. The current note derives an
independent compact formula and checks it against dense polynomials at those
same sizes. It does not extrapolate their successful counts to n=2^30.

## Explicit old basis

Write `n=4^r`, `m=n/4`, let omega have order n, and put

```text
i=omega^m,  T=X^m,  Y=omega*X,
alpha=1, beta=i, gamma=-1, delta=-i, Q=T+i.
```

The top quarters T=1,i,-1 are assigned to AB, AC, BC. The quarter T=-i is
split recursively by the same first-non-3 base-four digit rule. In Y coordinates
its residual locators, up to nonzero constants, are

```text
a(Y)=product_(0<=j<r-1) (Y^(4^j)-i),
b(Y)=product_(0<=j<r-1) (Y^(4^j)+1),
c(Y)=(Y-1)*product_(0<=j<r-1) (Y^(4^j)+i).
```

Their roots are disjoint, and their product is a nonzero multiple of Q. Their
degrees are `(m-1)/3,(m-1)/3,(m+2)/3`. Define the unique polynomial H of degree
less than m taking values `i,i/2,0` on the roots of a,b,c respectively. This is
ordinary interpolation on m distinct points; the production characteristic is
larger than n.

Set `eA=1+i`, `eB=-2`, `eC=1-i` and

```text
P0=(T-i)/(1-i),   Q0=(1-T)/(1-i).
```

Two triples of local codewords, before deletion, are

```text
lambda=(0, (T-1)*(P0+eA*H), -(T-i)*(Q0+eB*H)),
kappa =(0, (T-1)*eA*Q,     -(T-i)*eB*Q).
```

Every polynomial has degree at most 2m. The identities
`P0+Q0=1`, `P0+i*Q0=T`, and
`eA+eB+eC=eA+i*eB-eC=0` show that the B-C differences are divisible by
`(T+1)c`. The stated H values give divisibility of the B and C polynomials by
`(T-1)a` and `(T-i)b` respectively.

These are exact pair-agreement statements for the *pairs* of codewords. On the
first three quarters the odd kappa value is nonzero. On the fourth quarter
kappa vanishes, but the odd lambda value is nonzero: direct substitution of
each of the three H values proves this. Thus no residual pair is zero and
there is exactly one absent core at every original coordinate.

## Logarithmic derivatives eliminate the interpolation array

For distinct roots y of Q, Lagrange interpolation gives

```text
H(X)/Q(X)=sum_y H(y)/(m*y^(m-1)*(X-y)).
```

Since `y^m=-i`, the nonzero H values and the logarithmic derivatives of a,b
give

```text
R0(X) := H(X)/(X^m+i)
 = -(1/m) * (sum_(j=0)^(r-2)
       4^j * [ z_j/(z_j-i) + z_j/(2*(z_j+1)) ] - (m-1)/2),
z_j=(omega*X)^(4^j).
```

This identity holds away from the fourth quarter. Every displayed denominator
is nonzero there: `z_j=i` or `z_j=-1` would imply
`Y^m=z_j^(m/4^j)=1`, hence `X^m=-i`, because `m/4^j` is divisible by four.
The derivative implementation also assumes X is nonzero, as every domain
point is.

The old ratio of lambda residual to kappa residual is

```text
R0(X)                  on T=1 or T=i,
R0(X)+i/2              on T=-1,
infinity                on T=-i.
```

For example, the B row ratio is `R0+P0/(eA*Q)`, and the C row ratio is
`R0+Q0/(eB*Q)`. Substituting the appropriate top-quarter value gives the
formula above. This normalization is fixed throughout this note and the probe.

## Deletion and its four private directions

Delete `xi=1` from AB and `eta=omega` from AC, assigning both to private A.
Let `a0=R0(xi)` and `b0=R0(eta)`. If a0 differs from b0, the new triples are

```text
f=(lambda-b0*kappa)/(X-eta),
g=(lambda-a0*kappa)/(X-xi),
```

where division is performed in every local polynomial. Both divisions are
exact: at eta the whole first triple vanishes, and at xi the whole second
triple vanishes. Degrees are at most `2m-1=k-1`. The remaining pair regions
have sizes `(n-4)/3,(n-4)/3,(n+2)/3`, and there are exactly two private A
coordinates. Each of the three agreement cores has size `(2n+1)/3-1`.

At every undeleted coordinate x, if `(u:v)` is its old projective residual,
the new residual direction is

```text
((u-b0*v)*(x-xi) : (u-a0*v)*(x-eta)).
```

On the fourth quarter this is simply `(x-xi:x-eta)`, an injective Mobius map.

The remaining four slots must be evaluated from the original row polynomials,
not by taking limits of an arbitrary rational extension of the nodewise old
map. Define

```text
Dx=R0'(xi)+m/(4*xi),
Dy=R0'(eta)+m/(4*eta).
```

The correction terms follow by differentiating `Q0/(eB*Q)` at xi and
`P0/(eA*Q)` at eta. The four directions are exactly

```text
private xi, absent B:  (0:1),
private xi, absent C:  (a0-b0 : (xi-eta)*Dx),
private eta, absent B: ((xi-eta)*Dy : a0-b0),
private eta, absent C: (1:0).
```

The axis directions are nonzero because the removed top-quarter factors have
simple roots. The other two are nonzero whenever a0 differs from b0, even if
one of the displayed derivatives vanishes.

## Exact production checks and their limit

The probe imports the exact prime and generator from
[`_PrizeShapePrimeP30.lean`](../../ArkLib/Data/CodingTheory/ProximityGap/Frontier/_PrizeShapePrimeP30.lean),
checks their literal values, the prime-shape identity, and the required root
order powers. It uses the existing primality theorem as source provenance; it
does not rebuild that Lean theorem.

At `n=1073741824`, `m=268435456`, it computes

```text
a0=351585789857814829854891670864551386874926411849,
b0=31300587996458992207605949362462566565649795004,
Dx=187588605762748120473075910644157930783215178347,
Dy=347524855029125429912862942045506827472697416856.
```

All four private directions are distinct. To check whether a projective
direction `(a:b)` belongs to the whole fourth-quarter image, there is no need
to enumerate that quarter. If a=b it has no finite preimage. Otherwise its
unique possible preimage is

```text
x=(a*eta-b*xi)/(a-b),
```

and membership is exactly `x^m=-i`. None of the four private directions passes
this test. Thus the construction has at least **268435460** distinct
directions by exact arithmetic plus Mobius injectivity. This is a partial
count, far below the **1073741825** required to exceed the production budget;
it is not a new unsafe-radius certificate.

For this selected quarter and the four private slots, the basis change
`g -> g+f` also gives a finite scalar chart. Its unique possible fourth-quarter
pole is `(eta+xi)/2`, whose mth power is checked not to be -i, and each private
second coordinate after the change is nonzero. Combined with the general
core-uniqueness argument, these selected slots describe actual finite MCA
witnesses implicitly; no billion-entry certificate array is emitted.

The decisive missing claim is that the directions from the other three
quarters are distinct from each other, from this quarter, and from the four
private directions, with at most one total collision loss. The compact formula
does not establish that claim. The apparent simple possibility that the deleted
map is a Mobius transform of an odd monomial is rejected exactly at n=16
(and also at n=64,256), by cross-ratio checks on all ordinary slots.

## Reproduction

Run

```sh
python3 scripts/probes/astra_mca_twogen_lift_eval.py
```

At n=16,64,256 the probe independently constructs H by dense Lagrange
interpolation, builds the displayed local polynomials, checks their agreement
cores and every old projective residual, differentiates the dense H/Q, performs
the two exact polynomial divisions, and compares every deleted residual slot
with the compact formula. All 336 old-node and 342 deleted-slot comparisons
pass, and the three complete finite counts remain 18,66,258. The production
cell performs only the explicitly stated constant-size arithmetic checks.

These are mathematical derivations and reproducible finite arithmetic, with
independent agent review. They are not Lean proofs of the full production
collision claim, and they make no prize-completion claim.
