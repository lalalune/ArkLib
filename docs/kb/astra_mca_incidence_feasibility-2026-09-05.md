# Sharp common-domain incidence thresholds for six pencils

This is a counting result for the necessary absence-set conditions in the
[seven-type classification](astra_mca_six_pencil_types-2026-09-04.md). It does
not construct polynomial pairs, absence locators, square resultants, or MCA
events. The proof is elementary and accompanied by a deterministic arithmetic
checker; it is not Lean-formalized.

Let b be an integer with `b>2`, set `n=6b-2`, and let each of six absence sets
have size `2b`. A
coordinate's absent set is empty, a singleton, or a complete line flat of the
configured six-point incidence type. Every nonsingleton flat has weight at
most `b-2`, as required by saturation of at least five pencils.

## An exact counting identity

Write `e` for the empty-flat weight, `s` for the sum of singleton weights,
`T` for the sum of all triple-flat weights, and `Q` for the sum of all
four-point-flat weights. There are no larger flats in the seven remaining
types. Counting absence incidences minus twice the number of coordinates
gives exactly

```text
T + 2Q = 4 + s + 2e.
```

In particular a one-triple type must have triple weight at least four. This
is stronger than the lower bound one obtained from that triple's union alone.

The general Bonferroni bound is

```text
|union Di| >= sum |Di| - sum_{i<j}|Di intersect Dj|
           >= 12b - 15(b-2) = 30-3b.
```

Fitting into `6b-2` coordinates requires `9b>=32`, hence integer `b>=4`.
The construction below shows this common-domain incidence threshold is sharp.

## Two disjoint triples are feasible for every integer b at least four

Use long flats `123` and `456`, each of weight two. The other nonsingleton
flats are the nine cross pairs `ij`, with `i in {1,2,3}` and `j in {4,5,6}`.
Put

```text
m=2b-2,  q=floor(m/3),  r=m mod 3.
```

Assign the cross-pair weights by a cyclic three-by-three matrix having `r`
entries `q+1` and `3-r` entries `q` in every row and column. Each pencil has
absence size `2+m=2b`. The number of coordinates is

```text
2+2+3m = 6b-2.
```

All weights are positive, and the largest cross weight is `ceil(m/3)`.
For `b>=4`, `m<=3(b-2)`, so every nonsingleton weight is at most `b-2`.
There are no singleton or empty coordinates. Thus these are actual finite
set systems on a common domain: make one distinct coordinate for each unit
of flat weight and define `Di` by membership of its label in the flat.

At `b=4` all eleven flat weights are two, giving `n=22`. At `b=5` the cross
matrix has rows `(3,3,2)`, `(2,3,3)`, `(3,2,3)`, giving `n=28`. In particular
oddness of `b` does not strengthen the incidence threshold.

At production,

```text
b=178956971, n=1073741824,
each long-triple weight=2,
q=119304646, r=2,
six cross-pair weights=119304647,
three cross-pair weights=119304646.
```

## Exact least b for each classified incidence type

Here “feasible” refers only to the finite-set conditions above. The checker
supplies an explicit fixture at each listed minimum; this table does not
assert that every larger `b` is feasible for each type.

| Long flats | Least feasible b |
|---|---:|
| `123` | 6 |
| `123,145` | 5 |
| `123,456` | 4 |
| `123,145,246` | 5 |
| `123,145,246,356` | 5 |
| `1234` | 8 |
| `1234,156` | 8 |

For one triple the identity forces `4<=T<=b-2`, so `b>=6`. In fact this type
is feasible for every `b>=6`: set its triple weight to four, each of `45,46,56`
to two, and use a cyclic cross matrix with every row and column summing to
`2b-4`. Its maximum entry is `ceil((2b-4)/3)<=b-2`, and the total number of
coordinates is `4+3(2b-4)+6=6b-2`. No congruence restriction is needed.

For the other three intersecting-triple types, only `b=4` remains to exclude.
A point on two triples lies on exactly three nonsingleton flats: its two
triples and one ordinary pair. At `b=4` each has weight at most two. To reach
absence size eight that point needs singleton weight at least two. The types
with two, three, and four intersecting triples respectively have one, three,
and six such points. Therefore their respective lower bounds on total
singleton weight are `2,6,12`, whereas total triple weight is at most `4,6,8`.
Each contradicts `T=4+s+2e`.

For a four-point line of weight `t`, its four absence sets have union size
`8b-3t`. Thus `8b-3t<=6b-2`, or `t>=ceil((2b+2)/3)`. Together with `t<=b-2`
this gives `b>=8`, in both four-point-line types.

The small fixtures are given explicitly in the checker. For example the
four-point-line type at `b=8` has `w1234=6`, all eight cross weights to points
5 and 6 equal to four, and singleton weight two at each of points 1 through 4.
The four-point-line plus triple type has `w1234=6`, `w156=1`, all six cross
weights from points 2,3,4 to 5,6 equal to five, and singleton weight nine at
point 1. Both use exactly 46 coordinates and have all six absence sizes 16.

## The remaining algebraic conditions are substantial

For the two-disjoint-triple family, the
[private-locator identity](astra_mca_six_locator_consistency-2026-09-04.md)
would require three disjoint monic private locators of degree `2b-2` with a
constant linear relation whose coefficients are all nonzero. Their product
would divide `V`, with remaining factor of degree four. More precisely, for
the triple `123` the remaining coordinates are exactly the two long-flat
regions `123` and `456`, each of size two. The same degree-four remaining
factor serves the triple `456`. On the production root-of-unity domain this
means, after nonzero rescalings,

```text
A+B=C,    A*B*C*D = nonzero_constant*(X^n-1),
degree A=degree B=degree C=2b-2,
degree D=4.
```

These root identities do not follow from a valid incidence weighting.
The degree divisibility `4 | gcd(n,2b-2,4)` at production is a necessary
numerical condition for a common power lift of order four, not a proof of
such a lift. No multiplicative invariance of the actual root sets has been
established.

If the full six-pencil configuration were polynomially realized, the
[covering-degree lemma](astra_mca_six_locator_birationality-2026-09-04.md)
would give `nu | b` and `nu | 2`. Production `b` is odd, so the full
six-locator map would be birational. This rules out a common nontrivial cover
of that full map. It does not rule out a power factor for just one triple's
private-locator ratio after removing its common degree-two locator.

There is a stronger compatibility requirement on the two private ratios.
Write `U1,U2,U3` for the private locators of the first triple and `Z4,Z5,Z6`
for those of the second. Put `r=U1/U2` and `s=Z4/Z5`. Each private triple
spans a two-dimensional constant polynomial space, since it has a constant
relation and two disjoint nonempty root sets give independent polynomials.
Its full locators span `E1=T1*span(U1,U2)` or `E2=T2*span(Z4,Z5)`.
The full locator-span theorem says `dim(E1+E2)=3`, so their intersection has
dimension one. Choose nonzero `H` in that intersection and extend it to
bases `(H,J1)` of `E1` and `(H,J2)` of `E2`. Dividing all full locators by H
shows that the full locator map's function field is

```text
K(J1/H, J2/H) = K(r,s).
```

The equality follows because each `J1/H` and `J2/H` is an invertible
fractional-linear transform of its corresponding private ratio. Production
birationality therefore forces `K(r,s)=K(X)`. Consequently the two private
ratio maps cannot share any nontrivial rational right factor: if both lay
in `K(R(X))` for a rational map R of degree greater than one, that field
would be a proper subfield of `K(X)`, a contradiction. In particular both
private triples cannot have a common `X^2` or `X^4` power invariance. Either
private ratio individually may still factor in this way; only the shared
factor is excluded.

The [private cubic normal form](astra_mca_private_cubic_surface-2026-09-05.md)
uses this common one-dimensional span to write its generator as `D*R` and
derive a depressed cubic identity. It forces a substantial but nonempty
production degree range for R. A separate characteristic-zero elliptic
example shows why bounded-degree coefficients alone do not bound the
solution degree; the actual cyclotomic and saturation constraints remain
essential.

The elementary genus test also remains compatible. At production `b=2 mod3`,
the flat-point branch contribution for the birational map is at least

```text
2*binomial(2,2) + 3*binomial(q,2) + 6*binomial(q+1,2)
  = 2b^2-7b+8,   where q=(2b-4)/3.
```

The arithmetic genus of a degree-`2b` rational plane image allows
`2b^2-3b+1`, leaving positive slack `4b-7=715827877`.

Run `python3 scripts/probes/astra_mca_incidence_feasibility_check.py` to check
the seven minimal fixtures, both uniform-in-b construction formulas at
selected boundary and production values, and the production genus arithmetic.
It performs exact integer arithmetic with a constant number of flat records;
it does not enumerate the production domain or search for polynomial witnesses.
