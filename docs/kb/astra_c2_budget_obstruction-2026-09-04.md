# What the current C2 budgets can and cannot improve

This audit fixes the 68.04 candidate at error 80791, root caps
`T=6919, Y=136, R=30`, and the binding raw flag `(r,v,z)=(10,37,2317)`.
It uses the official companion at
[`032154395c51fd6f77715a7f42d9a987ab9fb48a`](https://github.com/proximity-prize/proximity-prize/commit/032154395c51fd6f77715a7f42d9a987ab9fb48a).
It finds a valid but negligible tightening and a kernel-checked obstruction
to obtaining a six-percent improvement from the scalar budgets alone.
It does not prove a new prize score or an obstruction to the actual geometry.

## A removable rounding

Write raw flags as `(z,v,r)`, let `w=131071`, and put

```
P = (z,v,r)
N = (z,v-1,r-2)
C = (2z,2v,2r-1)
E = (z,v,r+1).
```

The C2 branch has `r>=3, v>=2`, so its padding is inactive. Its rational
coordinate is `C+(w+1)N`. Its published moving cut is `C+(w+1)P`.

In `LocatorHybridTransportC2.exists_firstTail_moving_budgets`, the call to
`exists_moving_pole_budget_family` actually supplies

```
sum movingCost <= flagMixed flag E (C+w*P).
```

The last two lines weaken `w` to `w+1`. Keeping the returned inequality removes
that rounding. Thus the provider argument can use the smaller moving cut
`C+w*P`, with the same first-tail and rational contributions. The required
transport/provider signature changes have not been integrated or compiled
against the companion; the stronger inequality is the existing intermediate
`hm`, before its final monotonicity step. No new pole estimate is required.

At the binding flag the exact decomposition is:

| Quantity | Value |
|---|---:|
| First-tail/rational contribution | 178395282264909660 |
| Published moving budget | 801126293887 |
| Moving budget before rounding | 801120181870 |
| Published moving contribution, including `w+5` | 105008430097532412 |
| Published singleton cost | 283403712362442072 |
| Singleton cost after removing rounding | 283402911223701780 |
| Saving | 801138740292 |

The saving is **0.000282685%** of the singleton cost. It cannot close the
recorded gap of 17225531450318380.

## Why the scalar aggregation alone cannot save six percent

The last aggregation step retains three unit-cost bounds, the weighted
first-tail budget, and the moving sum. Consider one **abstract scalar atom**
of multiplicity one, with unit budgets

```
zCost   = 207880202
yzCost  = 11748245514
allCost = 57053808956.
```

These are exactly `flagMixed P firstTail unitFlag` in each coordinate.
Assign its moving budget the stronger unrounded value `801120181870`.
All four scalar bounds are equalities, as is the rational weighted budget.
The multiplicity-one branch charges `w+1`, giving

```
178395282264909660 + 131072*801120181870
  = 283399706742974300.
```

This exceeds 94% of the published singleton cost. The padded two-tail
alternative is larger, at `374823648281845290`. Keeping the same complement
and other terms leaves an excess of `17221525830850608` over the field.

The Lean theorem `scalar_caps_do_not_imply_six_percent` proves the negation
of the universal arithmetic implication from those four scalar caps to the
94% bound. It does **not** construct a polynomial, a component, or a local-DVR
certificate. In particular it does not rule out a new geometric relation
among these budgets. Such a relation, or a genuinely smaller geometric
budget, is necessary for this strategy to give a substantial improvement.

## Geometric checks and a small base-locus calculation

The moving projection has `J=Q+U*G/H`, where `Q` has quadratic support in
all coordinates and `U` has linear support in the Y/Z coordinates.
The exact pole target is

```
max(2*allPole, yzPole + pole(G/H)).
```

The local coefficient estimate contains both extreme weights. Dropping the
quadratic support or the linear multiplier is not justified by that estimate.
The products `H*Q` and `U*G` also genuinely reach the published fiber flag;
coordinatewise joining the flags of `H` and `G` omits these multipliers.

For a generic fiber parameter `t`, the eliminant equations are

```
H*(t-Q)-U*G = 0,
A = sum_j B_j * U^(k-j) * (t-Q)^j = 0.
```

Consequently `A` belongs to `(U,t-Q)^k`. The base locus `U=0,Q=t` is excluded
from the moving-fiber count. If this base locus were a full proper transverse
intersection on the surface, subtracting its expected multiplicity would
save `k*flagMixed(P,unitYZ,2*unitAll)` from the moving budget. At `k=w` the
resulting final saving would be only `81228280608288`, or **0.02866%** of the
singleton cost. This is a conditional calculation: properness, the number
of base points, boundary behavior, and the global subtraction theorem are
not established here. A larger correction must use more than this elementary
base locus.

## Reproduction and proof status

```sh
python3 scripts/probes/astra_c2_budget_obstruction.py
/tmp/arklib-lean-bootstrap/lean-4.30.0-rc2-darwin_aarch64/bin/lean \
  scripts/probes/astra_c2_budget_obstruction.lean
```

The Python probe passes. It independently checks mixed counts by polarizing
the cubic flag-polytope volume, and verifies the exact values above. The
core-only Lean file compiled successfully with exit 0 in 2.22 seconds.
Both `exact_values` and `scalar_caps_do_not_imply_six_percent` report **no
axioms** under `#print axioms`. The proof uses `decide`, not `native_decide`.
The finite arithmetic certificate is separate from the source-level
geometric tightening and its outstanding integration.

The [two-version CI run](https://github.com/lalalune/ArkLib/actions/runs/33935578742)
also passed at commit `40ea4a5ba28c2bd05a5cb164f97ab90c218b655d`, on research
Lean 4.30.0-rc2 and official-companion Lean 4.32.2. Both new reports were
axiom-free in both jobs; all fourteen auxiliary reports per job passed the
allowlist audit. This does not validate the unintegrated geometric change.
