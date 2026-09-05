# The remaining six-pencil incidence types

These are necessary constraints for an over-budget six-pencil example at the
predecessor agreement. They do not construct polynomial pencils, and do not
reduce the entire problem to the previously excluded quadrilateral pattern.
The arguments have an independent mathematical review; they are not Lean
proofs or a production census.

Use the hypotheses of the
[complete-line-flat note](astra_mca_six_pencil_flats-2026-09-04.md): six distinct
polynomial pairs, component degrees at most d, equal exact joint cores, full
cover, and a whole configuration not collinear over K(X). Normalize

```text
b=h+1>2, n=6b-2, d=3b-2,
each absence set Di has size2b, target agreement=4b.
```

All configured collinearities below are over K(X). A coordinate's absent set
is empty, a singleton, or a complete line flat. Let w_F be the number of
coordinates with absent set F. Then

```text
sum_F w_F=n,    sum_{F containing i} w_F=2b for every i.
```

For two different pencils, their common absence set consists exactly of the
nodes assigned to their complete line flat. Write its weight as t. Their
shared core has size `n-4b+t=2b-2+t`; a nonzero component difference of degree
at most d vanishes there, so `t<=b`.

## Saturation strengthens every pair bound to b-2

Each pencil supplies at most b candidate bad scalars, since all its 2b
nonzero residuals must supply at least two cancellations for agreement 4b.
To obtain at least `n+1=6b-1` distinct bad scalars, the sum of all per-pencil
deficits from b and all scalar-set overlaps is at most one. At least five of
the six pencils are therefore saturated: their outside coordinates split
into b pairs with distinct finite cancellation scalars.

Take any two distinct pairs Pi,Pj. Divide their component difference by its
polynomial gcd, writing

```text
Pi-Pj=H*v,     gcd(v0,v1)=1,
e=max(deg(v0),deg(v1)).
```

The primitive vector cannot vanish simultaneously at a field element, so H
vanishes at every shared-core node. Additivity of degrees gives `e<=b-t`.
On `Ui=Di\Dj`, of size `2b-t`, pair j owns the coordinate and pair i has a
nonzero residual of direction v(x).

If `t=b`, v is constant, and the b>2 points of Ui all have the same direction,
preventing saturation of i. If `t=b-1`, then e<=1. A constant v again fails.
A primitive nonconstant vector of linear polynomials gives an injective map
to the projective line. Thus the b+1 points of Ui have distinct directions,
and each needs a partner among only b-1 remaining outside points, also
impossible. A direction at infinity only makes finite saturation fail sooner.

Hence if either i or j is saturated, `|Di intersect Dj|<=b-2`. Every pair
contains a saturated pencil, because at most one pencil is unsaturated. Thus

```text
every absence flat with at least two points has weight at most b-2.
```

This excludes all proposed uniform patterns assigning weight b to their
nontrivial flats, including the K2,3 five-region pattern and the analogous
chorded-cycle pattern. It does not exclude nonuniform weights.

## Seven line-incidence types remain necessary possibilities

A long line means one containing at least three of the six configured pairs.
The table lists representatives up to relabeling. Unlisted pairs lie on
ordinary two-point flats. This classification concerns incidences only;
weights, exact polynomials, and saturated scalar directions are additional
requirements.

| Largest line | Long-line representatives | Description |
|---|---|---|
| 3 | 123 | One triple |
| 3 | 123,145 | Two intersecting triples |
| 3 | 123,456 | Two disjoint triples |
| 3 | 123,145,246 | Three lines forming a triangle |
| 3 | 123,145,246,356 | Complete quadrilateral |
| 4 | 1234 | One four-point line |
| 4 | 1234,156 | A four-point line and one triple |

For largest line three, each point is on at most two long lines: each such
line consumes two other points, and different lines through that point share
no others. Three long lines must meet pairwise at three distinct points to
fit into six points. Four long lines use all twelve available incidences,
forcing the complete quadrilateral. This proves the five largest-line-three
cases, along with the no-long-line case excluded below.

A four-point line leaves just two points outside it. Any other long line
must contain both outside points and exactly one point on the four-point
line, so there is at most one. A five-point line has only the sixth point
outside it. Six collinear points were already excluded by the full-cover
n-direction bound.

There must be at least one long line: if every absent set has size at most
two, total absence incidence is at most `2n=12b-4`, instead of the required
12b. A five-point line is also impossible. If its weight is t, the union of
its five absence sets has size `10b-4t`, since outside its common flat those
sets are disjoint. Fitting in n nodes requires `t>=b+1`, contradicting even
the weaker degree bound `t<=b`.

More generally a line of r configured points has absence-set union size
`2br-(r-1)t`. For a triple this implies `t>=1`. For a four-point line it
implies `t>=ceil((2b+2)/3)`; saturation also requires `t<=b-2`. Thus four-point
lines need b>=8, which the production parameters satisfy.

## A concrete one-triple incidence escape survives these tests

Let the only long line be 123. For `b>=8` and `b=2 mod3`, assign these weights:

```text
w_{123}=4,
w_{ij}=(2b-4)/3 for i in{1,2,3}, j in{4,5,6},
w_{45}=w_{46}=w_{56}=2,
all singleton and empty weights=0.
```

Each point has absence degree `4+3(2b-4)/3=2b`. The number of coordinates is
`4+9(2b-4)/3+3*2=6b-2`. Every nontrivial flat weight is at most b-2. All absent
sets are complete flats, so no noncollinear triple is simultaneously absent.

At production these exact numbers are

```text
b=178956971,    n=1073741824,
w_{123}=4,     each of nine cross-pair weights=119304646,
each of three remaining pair weights=2,
each pencil's total absence=357913942.
```

Thus the necessary incidence and primitive-degree tests do not force the
quadrilateral or exclude every six-pencil example. Realizing these prescribed
equalities by degree-less-than-k polynomial pairs still requires the actual
simultaneous interpolation kernel to have rational rank at least two. The
exact determinant/locator identities and almost-perfect residual pairings
must also hold. No field-valued realization, interpolation rank certificate,
or set of over-budget scalars is supplied here.
