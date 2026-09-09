# Restricted optimum across all four degree-seven sources

2026-09-08. Reviewed written reduction plus two independent exact
production-field censuses. This is not a Lean theorem or universal MCA safety.

## Statement

Work over the certified production prime and order-sixteen subgroup. Let
`n=2^30`, `s=n/16=67108864`, and choose arbitrary four pairwise distinct
polynomials `W_i` of degree at most seven. Set

```
p_i(X)=Q(X) W_i(X^s),   q_i(X)=X p_i(X),   deg Q <= s-2.
```

Within the mechanism that obtains bad directions from these four sources'
joint cores plus one outside point, no allocation with at least `n+1` distinct
supplied directions can have all four cores larger than `760567124`.
The existing order-sixteen construction attains this core bound. This extends
its fixed-seed optimum to arbitrary four degree-at-most-seven sources under
the stated carrier and common-factor degree bound.

It does **not** cover five sources, additional decoders agreeing at multiple
outside points, another carrier, arbitrary order-32 sources, or a larger
common-factor budget allowed by lowering the maximum source degree. It is not
universal MCA safety. `Q=0` supplies at most one direction per coordinate and
cannot give more than `n` directions.

### Local inequality and dangerous incidence profiles

Subtract `W_0` from every source to normalize `W_0=0`; this preserves equality
partitions and all degree bounds. Let `F` count quadruple fibers and `T` count
fibers with exactly a triple equality class. At a covered non-root point,
direction credit is one when a nonowner exists, and zero for a quadruple
class. An uncovered point supplies at most the number of distinct local
classes. At a common root the source vectors coincide. Matching that vector gives
four core credits and no direction; choosing a different received vector
gives at most one direction and no core credit. Both states satisfy the
same inequality below.

For a local partition put `beta=8+3*[triple]+4*[quadruple]`. Every covered or
uncovered state has `2*direction_credit+3*total_core_credit <= beta`.
A common-root state exceeds this by at most four. Therefore

```
2D + 3(C_0+C_1+C_2+C_3) <= (128+3T+4F)s + 4 deg Q.
```

If `3T+4F<=36`, `D>=16s+1` and `deg Q<=s-2` give

```
min_i C_i <= floor((136s-10)/12) = 760567124.
```

Let `h_0,...,h_3` count the four exact triple types, so `T=sum h_i`. Every pair
of sources has all `F` quadruple roots and the roots of two complementary
triple types. The nonzero degree-at-most-seven difference therefore gives
`F+h_i+h_j<=7` for every distinct `i,j`.

The only sorted profiles satisfying these inequalities and `3T+4F>36` are

```
F=0, h=(4,3,3,3);
F=1, h=(3,3,3,2);
F=1, h=(3,3,3,3).
```

This classification is checked by the separate exact `dual_check.py`; its
simple enumeration is over eight possible counts in each of five positions.

### Why one unequal-degree census covers every dangerous profile

Each listed profile contains disjoint required triple-root sets `A,B,C,D`
of sizes `(4,3,3,2)` with respective source triples `012,013,023,123`, after
permuting source labels. For `F=0`, choose four roots of the largest triple
type and two of the last triple type. For `F=1`, assign the quadruple root to
`A`, together with its three exact triple roots; it also satisfies the required
012 equality. Choose the other required roots from their disjoint exact
triple types. Quadruple equality is permitted as an extra coincidence.

Write `A,B,C` also for their monic root polynomials. Degree and root bounds
force, after normalizing `W_1` monic,

```
W_1=A B,   W_2=lambda A C,   W_3=B C L,
```

where `lambda != 0` and `deg L<=1`. At the two D nodes,
`lambda=B/C` must be equal and `L=A/C`. Thus each compatible arrangement has
exactly one normalized source tuple: `L` is its two-point interpolant.
This is exhaustive, including possible quadruple fibers and extra triples.

The primary checker exhausts the production field directly. Unordered B,C
pairs suffice: swap sources 1 and 2 and scale all sources by lambda inverse.
This exchanges B and C, replaces lambda by its inverse and L by L/lambda,
and only relabels equality classes, preserving the minimum-core bound.

The exact census has the following counts:

| Quantity | Count |
|---|---:|
| Unordered disjoint three-root B,C pairs | 80,080 |
| Two-node D ratio tests | 3,603,600 |
| Compatible B,C,D choices | 8,800 |
| Compatible four-root A assignments | 616,000 |
| Assignments with no quad and exactly twelve triples | 609,280 |
| Assignments with a quadruple fiber | 6,720 |
| Assignments with the thirteenth required triple | 0 |

The factorization reduces 252,252,000 raw support assignments to the displayed
ratio census. No small-field filtering or random selection was used. The
optimized run took about 2.7 seconds.

Pruning is algebraic: A cannot acquire another triple root because A would
then have five roots and B has three, forcing nonzero `W_1` to have eight
roots. B or C cannot acquire a fourth triple root for the same reason. The
only possible thirteenth exact triple is a third D point; it is checked via
the nonzero cubic `B-lambda C` and the interpolant L. A quadruple point must
be an A root at which L vanishes. These tests leave precisely the 6,720
quadruple cases.

### Exact exceptional bounds

The 6,720 quadruple cases have only two profiles of largest class size and
number of classes. Their rational upper bounds on a normalized common core
are `67/6` (1,152 cases) and `131/12` (5,568 cases), both strictly below
`34/3`. The weaker of these already implies
`min C_i <= floor(67s/6)=749382314 < 760567124`.

These are explicit rational inequalities, not inferred LP optima. For a
positive rational lambda, take each fiber weight
`beta_j=max(1+lambda*m_j,number_of_classes_j)` and root surcharge
`z=max(0,4*lambda-min beta_j)`. Each covered state satisfies
`direction+lambda*core_sum<=beta_j`, uncovered states do too, and each common
root adds at most z. Consequently
`min C_i/s <= (sum beta_j+z-16)/(4lambda)` after relaxing the root budget to
one and directions to sixteen. The receipts store the exact vectors, all
with `lambda=3`; `fractions.Fraction` checks every relevant local inequality.
The weight at a quadruple fiber is conservatively 13 rather than 12, so these
bounds are intentionally relaxed.

An independent implementation constructs every full partition at all sixteen
nodes for all 616,000 compatible assignments, without the primary pruning.
It reproduces every count and verifies 82 local states, including both
common-root states. Using the exact zero direction credit for a quadruple
fiber tightens the exceptional bounds to 133/12 and 65/6; this does not
change the attained main core cap.

## Reproduction

All checkers use Python's standard library. From the repository root:

```sh
python3 scripts/probes/astra_mca_order16_all_four_check.py --output /tmp/all-four.json
python3 scripts/probes/astra_mca_order16_all_four_dual_check.py /tmp/all-four.json
python3 scripts/probes/astra_mca_order16_all_four_independent_check.py
```

Retained [primary census](../../scripts/probes/receipts/astra_swarm_20260908/all_four.json),
[local dual check](../../scripts/probes/receipts/astra_swarm_20260908/all_four_dual.json),
and [independent full census](../../scripts/probes/receipts/astra_swarm_20260908/all_four_independent.json)
record the exact results. Source hashes are in the adjacent manifest.
The reduction from all arbitrary sources to this finite census is a reviewed
written argument, not a claim that the Python loop quantifies over all
production-field coefficients directly.
