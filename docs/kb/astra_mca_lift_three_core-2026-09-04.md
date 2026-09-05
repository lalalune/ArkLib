# Actual MCA witnesses from the middle-band triple, and the exact conversion ceiling

Date: 2026-09-04. Mathematical proofs and exact modular certificates; not new
Lean theorems. The evaluation domain remains the same smooth subgroup.

The middle-band triple can be converted into actual MCA-bad scalars, including
the no-joint-explanation clause. Reserving unused coordinates for three distinct
cancellation values gives **54 certified bad scalars at `n=64`**, **108 at
`n=128`**, and **222 at `n=256`**, all at rate `1/2` and agreement strictly
above `2n/3`. The same architecture has a matching upper bound on the scalars
it can certify from these three cores plus one extra coordinate. Those values
remain below `n-1`.

This is a quantitative comparison of actual MCA witnesses with the desired
strip budget. It is not a global upper bound on the MCA error of the constructed
pair: unrelated codewords or supports could supply additional bad scalars.

## 1. Construction and the exact event

The event tested is `mcaEventNat` from
[`MCAExactComputationKit.lean`](../../ArkLib/Data/CodingTheory/ProximityGap/MCAExactComputationKit.lean),
equivalent to the cardinality version of `mcaEvent` in
[`Errors.lean`](../../ArkLib/Data/CodingTheory/ProximityGap/Errors.lean).
A witness is a support `S` of the required size, a codeword matching
`u0+gamma*u1` on `S`, and the absence of a codeword pair matching both
received components on that **same** `S`.

Reuse the field-uniform cubic seed and power lift from
[the middle-band counterexample](astra_grand_smooth_middle_counterexample-2026-09-04.md).
Write the three degree-`3m` locators as `W_AB,W_AC,W_BC` and their minimal
cofactors as `r_AB,r_AC,r_BC`, each of degree at most `m`, with

```
W_AB*r_AB + W_AC*r_AC + W_BC*r_BC = 0.
```

Set

```
n=16m,  k=8m,  t=4m-2,  q=floor(2m/3)+2,
s0=floor(2n/3),  Ecard=3m+2-3q,       m>=4.
```

Choose a triple region `T` of size `t`, three disjoint pair regions of size
`3m` as before, and three private regions of size `q`. Each core, consisting
of `T`, its two pair regions, and its private region, has exactly `s0`
points. The unused set `E` has size `Ecard`, with `0<=Ecard<=m`.

Put

```
F_A=0,
F_B=V_T*W_AB*r_AB,
F_C=-V_T*W_AC*r_AC.
```

These polynomials have degree at most `t+4m=k-2`. Thus both `F_i` and
`X*F_i` belong to the degree-`<k` Reed--Solomon code. On the union of the
cores define

```
u0(x)=F_i(x),       u1(x)=x*F_i(x)       on core i.
```

The definitions agree on overlaps. Values on `E` will be chosen separately.

At any point `x` outside core `i`, suppose the residual pair

```
d0=u0(x)-F_i(x),       d1=u1(x)-x*F_i(x)
```

is nonzero and `d0+gamma*d1=0`. Then

```
S=core_i union {x},       h_gamma=(1+gamma*X)*F_i
```

is an MCA witness. Its agreement size is `s0+1>2n/3`, and `deg h_gamma<k`.
For the no-joint clause, any codeword pair agreeing on `S` must already
equal `(F_i,X*F_i)`, because it agrees with that pair on the `s0>=k`
distinct points of the core. The nonzero residual at `x` contradicts that
joint explanation. This uses ordinary polynomial uniqueness, not a
presumption that closeness alone implies MCA failure.

## 2. Counting covered coordinates and choosing holes

On covered coordinates outside `T`, choose a core `i` whose `F_i(x)` is
different from the received value. Since `u1=x*u0`, the cancellation scalar
is `gamma=-1/x`. These scalars are distinct across coordinates.

The probe verifies on the 16-point seed that the three normalized polynomial
values never all coincide at any domain point, in every field used below.
The root-of-unity lift then supplies exactly `n-t-Ecard` such covered
coordinates. This is an exact seed condition checked at the production field
as well; it is not inferred from small primes.

To reserve the holes, choose one of the seven exterior seed points at which
the three normalized values are distinct. Such a point exists in every field
containing the seed: each of the three nonzero linear cofactors can eliminate
at most one exterior point. Reserve `Ecard<=m` points in its full fibre, and
choose `T` and the private regions from the remaining exterior points. At a
hole the three local pairs `(F_i(x),x*F_i(x))` are distinct.

Choose the received pair `(a,b)` at each hole so that

```
gamma_i = (F_i(x)-a)/(b-x*F_i(x)),       i=A,B,C,
```

is defined, gives three distinct scalars, and avoids all previously chosen
scalars. This is possible over sufficiently large finite fields by avoiding
finitely many affine lines in the `(a,b)` plane:

- three lines exclude zero denominators;
- the line `b=x*a` excludes collisions between the three local scalars;
- for each previous scalar and each local pair, one line excludes equality
  with that scalar.

With at most `B` total scalars planned, fewer than `3B+4` lines suffice at
each stage. A field of size greater than `3B+4` cannot have its whole affine
plane covered by them. Every hole therefore contributes three new MCA-bad
scalars, with the same no-joint proof as above.

The resulting certified count is

```
B = (n-t-Ecard) + 3*Ecard
  = n-t+2*Ecard
  = 18m+6-6q.
```

For the fields in the probe, concrete hole values are found and every
resulting witness is verified. Where the generic sufficient field-size
inequality does not hold, those explicit choices still establish the
displayed finite example.

## 3. Why changing the local pair cannot improve this three-core conversion

The following bound concerns any received pair locally explained by
degree-`<k` codeword pairs on these **same three cores**, with its certified
bad scalars obtained by adding one coordinate to one core. It does not
cover arbitrary MCA supports.

First, the seed's linear-cofactor syzygy space has dimension exactly one.
The previous proof gives a nonzero syzygy `r` and excludes constant
syzygies. Thus `r` is primitive: a common nonconstant divisor of its
linear entries would yield a constant syzygy after division. If two
linear syzygies were independent, their cross product would have entries
of degree at most two and be parallel over `K(Y)` to the primitive cubic
vector `(p_AB,p_AC,p_BC)`. Since the cubics have gcd one, the proportionality
factor must be polynomial, which is impossible at those degrees unless
the cross product is zero. In that case primitivity of `r` makes the
second syzygy a polynomial multiple of `r`, and the linear degree cap
makes that multiple constant. This proves dimension one in every field
under consideration.

Any compatible local triple `(g_A,g_B,g_C)` of degree-`<8m` polynomials
has differences divisible by `V_T` and their corresponding region
locators. Its reduced syzygy cofactors have degree at most

```
(k-1)-t-3m = m+1.
```

Split these cofactors by exponent modulo `m`. Residues zero and one give
linear-cofactor relations between the base cubics; all other residues
give constant relations and vanish. By the one-dimensional seed result,
the only possibilities are the lifted minimal syzygy multiplied by
`L(X)=a+bX`. Consequently

```
g_i(X) = g_A(X) + L(X)*F_i(X),       i=A,B,C.
```

For a received pair with two such local triples, write the multipliers
as `L0,L1`. At a covered point owned by core `j`, the residual relative
to core `i` is

```
(L0(x),L1(x)) * (F_j(x)-F_i(x)).
```

Every nonzero residual there therefore has the same cancellation scalar,
independent of `i`, if such a scalar exists. A zero residual has a joint
explanation and supplies no bad witness. A covered coordinate contributes
at most one distinct scalar; a point of `T` contributes none; a hole
contributes at most three, one for each core. Hence the entire specified
conversion certifies at most

```
n-t+2*Ecard = B < n-1.
```

The explicit construction attains this bound in the tested cells and,
by the finite-line avoidance argument, at the production field below.
Thus replacing `(r,Xr)` by arbitrary compatible local pairs does not
improve the count in this architecture.

## 4. Admitting the next syzygy loses the one-extra-point agreement budget

There is no independent normalized syzygy before product degree `5m`:
the same residue argument below that degree gives only polynomial
multiples of the first seed syzygy. At degree `5m` an independent relation
does exist: on the seed, quadratic cofactors give nine unknowns and six
coefficient equations, hence kernel dimension at least three, whereas
multiples of the first linear syzygy account for only two dimensions.

Making that extra freedom fit in degree `<k` requires `t<=3m-1`.
But with the same three pair regions, the sum of all three core sizes is
at most

```
3t + 18m + (7m-t) = 25m+2t <= 31m-2.
```

Three cores of size at least `s0=floor(32m/3)` require total membership
`3s0>=32m-2`. The deficit is at least `m`. Thus no allocation of private
points can retain all three cores at the agreement needed for one extra
cancellation point. At least one core loses
`ceil((3s0-(31m-2))/3)` points. At production this is **22,369,622 points**.
Merely shrinking `T` is therefore not a viable next step for this conversion;
one needs new support geometry or a mechanism producing many additional
matches for a scalar.

## 5. Exact evidence and production comparison

Run:

```sh
python3 scripts/probes/astra_mca_lift_three_core.py
```

Each displayed witness is checked for polynomial degree, agreement on its
full support, and a dual parity certificate ruling out joint explanation.
For the latter, the probe takes `k` core points and the extra point and
forms the Vandermonde dual row
`lambda_j=1/product_(l!=j)(x_j-x_l)`. It directly verifies annihilation
of degrees `0,...,k-1`, then checks that at least one received component
has a nonzero parity sum while the `gamma`-combination has zero parity.
This separately validates the no-joint clause.

| field | `n` | event agreement | certified MCA bad scalars | same-core ceiling | `n-1` |
|---|---:|---:|---:|---:|---:|
| `F_193` | 64 | 43 | 54 | 54 | 63 |
| `F_257` | 128 | 86 | 108 | 108 | 127 |
| Proth field `111*2^128+1` | 64 | 43 | 54 | 54 | 63 |
| same Proth field | 128 | 86 | 108 | 108 | 127 |
| same Proth field | 256 | 171 | 222 | 222 | 255 |

All **546 nonjoint parity certificates** pass. The probe also checks the
normalized compatibility-matrix nullities at product degrees
`4m,4m+1,5m-1,5m`, which are respectively `1,2,m,m+2`.

At the repository's actual prime

```
P = 365375409332725729550921208179070755120141565953,
n = 2^30,   k = 2^29,
```

the prime and domain root are established in
[`_PrizeShapePrimeP30.lean`](../../ArkLib/Data/CodingTheory/ProximityGap/Frontier/_PrizeShapePrimeP30.lean)
by `prime_P` and `orderOf_g`. The probe checks the exact root and the
16-point seed, plus the counting and finite-line avoidance inequality;
it does not materialize the billion-point domain. The proof gives

```
agreement = 715827883,
B = 939524094 < 1073741823 = n-1.
```

The same-core ceiling is 134,217,729 below `n-1`. No global MCA upper bound
or improved grand-prize threshold is obtained.

For this particular P, the exact target numerator budget
`floor(P/2^128)` equals n, by `PrizeShapePrimeP30.P_div_two_pow_128`.
The `n-1` strip budget compared above is a stronger sufficient target;
the construction remains below the exact prize budget as well.

## Relation to existing constructions

The primitive-direction and isolated-coordinate method already appears in
`probe_rate_quarter_smooth_isolated_counterexample.py` and its production
certificate `probe_rate_quarter_prize_p1_isolated_counterexample.py`.
Those concern the different rate-quarter, constant-syzygy locator family.
The contribution here is its exact application to the new nonconstant
middle-band family, including the matching conversion ceiling supplied by
its one-dimensional seed syzygy space. No broad novelty claim is made.

[Gao, Yang, Xu, and Kan (2026)](https://arxiv.org/html/2607.10572v1) give
constructive list-to-MCA transfers, including a Reed--Solomon version that
may change one evaluation point. Preserving the Reed--Solomon family does
not by itself preserve a prescribed smooth domain. The construction here
keeps every evaluation point fixed and directly verifies the repository's
MCA event; the paper is relevant context rather than an assumed bridge.
