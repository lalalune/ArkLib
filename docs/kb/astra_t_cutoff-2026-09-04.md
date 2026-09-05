# T-interpolant cutoffs and the residual ledger at 68.04

The best of four complete replays lowers the combined numerical allowance from
`292206259561713467` to **`292119564672092577`**, an improvement of
`86694889620890`. It still exceeds the field budget by **`17138836560697490`**
(about 6.23%). No new `ProtocolClaim`, leaderboard score, or prize solution is
proved.

This continues the [contact-strip](proximity-astra-contact-strip-2026-09-04.md)
and [factor-partition](proximity-astra-factor-partition-2026-09-04.md) experiments
at error cell 80791. The official companion source is pinned to
[`032154395c51fd6f77715a7f42d9a987ab9fb48a`](https://github.com/proximity-prize/proximity-prize/commit/032154395c51fd6f77715a7f42d9a987ab9fb48a).
Its promoted lower score is 68.03; this experiment targets the next error cell
needed for 68.04.

## A quotient cutoff need not equal two

Set `n=262144`, `w=131071`, and `a=181353`. For T-interpolation parameters
`(m,L,S)`, let `D=m*a` and

```text
N(L) = coefficientCount(D,w,L,S) - n*localRankBound(m,L,S).
Q(k) = coefficientCount(D,w,k,S).
```

These are signed integer nullity lower bounds in the probe. The source theorem
uses natural subtraction after the required positive dimension inequality.

Suppose a nonzero polynomial F divides every T-kernel interpolant and has total
degree at least `L-k`. The injective quotient family lies in the box
`globalCoefficientBox D w k S`. Consequently its dimension is at most `Q(k)`.
If `N(L)>Q(k)`, the dimension obstruction gives

```text
totalDegree(F) <= L-k-1.
```

This is the argument already used by `LocatorCaps.common_TCap_total_le`, with
`k=2`, in the pinned
[`PackedLocatorTail.lean`](https://github.com/proximity-prize/proximity-prize/blob/032154395c51fd6f77715a7f42d9a987ab9fb48a/ProximityPrize/SubmissionLower/PackedLocatorTail.lean).
`LocatorLowQuotient.quotient_box_of_full_divisor` and
`common_divisor_dimension_obstruction` accept the general quotient box. There
is no mathematical restriction to k=2 in those interfaces. Instantiating them
at the new parameters, including the revised selected degree bound, remains a
Lean proof obligation.

Two direct witnesses are:

| m | L | S | Y | k | N(L) | Q(k) | Selected total cap |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 194 | 6923 | 60 | 268 | 4 | 1240442015 | 1222211935 | 6918 |
| 197 | 6922 | 61 | 272 | 4 | 1422701290 | 1241254000 | 6917 |

Both improve the previous selected cap 6919. However, this cap is only one term
in the error accounting: the second choice raises the residual T-box degrees
and **worsens the combined allowance**.

## Exact bounded search and its scope

[`astra_t_cutoff.cpp`](../../scripts/probes/astra_t_cutoff.cpp) considers every
integer shape

```text
1 <= m <= 270,
0 <= S <= min(m,81),
m+S <= L <= 130000,
D=m*a,
D+S <= w*(Y+1), where Y=floor((D-1)/w).
```

These are a deliberately bounded T-box embedding class: the weighted, slope,
and total caps fit the corresponding C ambient box after retuning its weighted
parameter to `270*a`. Every candidate also satisfies `S<=m<p`, where
`p=2130706433`. This does not claim to cover all interpolation supports, larger
ambient constructions, modified rank bounds, or a fully assembled root proof.

There is no arbitrary cutoff bound on k in this search. Above
`max(m+S,Y+S+1)`, the nullity is affine:

```text
N(L)=lambda*L+beta.
```

The program checks all **1,145,265** smaller admissible L cases and finds
nonpositive nullity. It examines **18,900** shapes, of which **15,390** have
nonpositive affine slope and hence cannot yield a positive kernel in the
remaining range.

For a positive slope, the least L for a fixed k is

```text
L(k)=ceil((Q(k)+1-beta)/lambda).
```

The quotient count is a sum of nonnegative weighted ramps in k, so its first
differences are nondecreasing. Using integer k,

```text
L(k)-k-1 = ceil((Q(k)+1-beta-lambda*k)/lambda)-1.
```

Thus the least selected cap is attained where `Q(k+1)-Q(k)` first reaches
lambda. Beyond the full weighted support, Q is affine with slope strictly
greater than lambda, so later cutoffs cannot improve this minimum. The search
also preserves the earlier nondominated `(selected cap,L)` choices: a tie in
selected cap can prefer a smaller L because it reduces the residual charge.
After the crossing, both L and selected cap are nondecreasing, so no discarded
later cutoff improves either quantity.

There are **5,205** retained shape/cutoff rows. The least selected cap in this
class is **6917**, attained by the m197 witness above. That is a bounded
parameter-search result, not an impossibility theorem for a different proof.

[`astra_t_audit.py`](../../scripts/probes/astra_t_audit.py) independently checks
the returned witnesses with Python integer counts, checks failure at L one
smaller, and enumerates the quotient ramp-transition range for the best twenty
point-charge rows. No floating-point decisions or numerical logarithms are
used. The C++ program uses signed 128-bit integers.

## Actual full-envelope comparison

All four replays retain the original 49 helper sources, exact contact-strip
rule, A-source `(m,L,S,Y)=(99,217071,30,136)`, B-source `(111,17568,33,153)`,
and the full phase domain. No local atom-refinement rectangle truncates these
runs. Every replay maximizes at the same raw flag **`(r,v,z)=(10,37,2317)`**.

| T choice `(m,L,S,k)` | Selected cap | Full combined allowance | Change from old T |
|---|---:|---:|---:|
| (194,6922,60,2), old | 6919 | 292206259561713467 | 0 |
| (194,6923,60,4) | 6918 | 292206040206005516 | -219355707951 |
| (197,6922,61,4) | 6917 | 292222169121174681 | +15909559461214 |
| (166,7159,51,1) | 7157 | **292119564672092577** | **-86694889620890** |

The last choice has `D=30104598`, `Y=229`, nullity `228451639`, quotient
dimension `120156251`, and positive margin **108295388**. Increasing its
selected total cap while decreasing the residual slope and Y caps improves
the combined count. Its phase maximum is `292043231449062169`; fixed tails and
the scalar list count supply the remaining terms.

This last choice minimizes the charge at the **old critical flag** among the
5,205 retained rows. Only the four listed choices received full-envelope
replays. The following point certificate also bounds every tuning in the
specified T class; it does not establish globally optimal error accounting.
The audit requires the actual returned maximizer to equal the stated flag
before it uses that flag's ordinary singleton allowance.

## A bounded optimality certificate for T tuning

The single critical flag gives a lower bound on this **numerical allowance**
for every T choice in the search class:

1. Every eligible selected total cap is at least 6917, so the flag with total
   degree 2364 remains in the phase domain. The base factor knapsack includes
   its singleton contribution `ATOM=283403712362442072`.
2. The Python audit independently recomputes both full-channel and clipped
   source budgets at this flag for all 49 sources. Exactly six route it. Their
   least point charge is `286642894046259837`, strictly greater than ATOM.
   Prefix defects are nonnegative. Thus no source phase, including recursive
   closure, can reduce this point's allowance below ATOM.
3. For fixed `(m,S)`, the remaining point ledger is nondecreasing in both the
   selected cap and actual L. The initial complement has already saturated its
   Y and R caps, so it is affine in the selected cap with positive slope.
   The two fixed-chain numerators and fixed-tail numerator have nonnegative
   coefficients in that cap. In the residual regular count, the first two
   mixed terms increase with L, and the third is constant; its Z agreement cap
   is `max(2*w*17568+1,2*w*L+1)`, also nondecreasing. The other terms are fixed.
   Positive division and taking integer floors preserve these inequalities.
4. Consequently the exact `(selected cap,L)` Pareto pruning preserves the
   minimum of this point lower bound. The exhaustive search's least point
   bound is **292119564672092577**.
5. The full m166 replay attains exactly that bound, and its source-realization
   gates pass. It is therefore optimal **within this bounded T-interpolation
   class and this fixed 49-source numerical envelope**, among choices for
   which those source gates hold.

This argument avoids claiming 5,205 full-envelope replays. It also avoids an
adversarial existence claim: an ordinary-factor allowance need not be
saturated by any polynomial. Changing the source pool, the factor-counting
envelope, rank estimates, interpolation support, or other root parameters lies
outside this certificate. The certificate is an exact computational audit and
the mathematical monotonicity argument above, not a Lean theorem of bounded
optimality.

The selected cutoff and actual interpolant limit must remain distinct. The
shared evaluator now accepts an explicit `--quotient-cutoff K`, with default
2 for old commands, and checks `T.L=selected+K+1`. For the best replay, the
root and residual arguments are

```text
--root 7157 136 30 153 33 217071
--errors 80791 --padding 0
--joint 111 17568 229 51 7159
--quotient-cutoff 1
```

These follow `candidate-closure --clipped-band` and precede the unchanged 49
source triples. The audit supplies the triples and checks the evaluator's
`QUOTIENT` receipt. Every residual formula uses the explicit T.L. The CLI
consistency check is not a dimension or polynomial certificate.

## Divisor R and contact degrees

If the divisor has actual R degree r and actual YS degree y, its contact degree
is at least `w*y-r`. The quotient box can therefore be tightened to

```text
globalCoefficientBox (D-(w*y-r)) w k (S-r).
```

The contact lower bound uses the **actual R degree or an upper bound on it**;
an R-degree lower bound alone does not justify substituting r into `w*y-r`.
Positive R degree alone still gives the weaker valid contact bound `w-1`
and reduces the quotient slope cap by one.

At the obstructing flag `(r,y)=(10,47)`, this refinement does not improve the
best selected cap for m194 or m197: they remain 6918 and 6917. For larger
conditional flags `(30,136)` and `(33,153)`, it can improve m197's bound to
6915. These are conditional arithmetic tests, not uniform root bounds or new
phase certificates. The critical singleton has total degree 2364, far below
all these caps, and its ordinary allowance alone is `283403712362442072`, above
the field budget. The tested T refinements therefore leave the underlying
counting obstruction present.

## Reproduction and remaining proof obligations

```sh
python3 scripts/probes/astra_t_audit.py
python3 scripts/probes/astra_t_audit.py --check-search --check-phases
python3 scripts/probes/astra_t_audit.py --sanitize --phase-case least_old_point_charge
```

The optimized full replays pass with the same final maxima. The sanitized run
checks the search and best full replay with undefined-behavior detection.
Generated binaries and JSON receipts are temporary; no generated tables are
committed.

Independent review also reproduced all three dimension witnesses using the
official nested-sum definitions rather than the fast closed-form helpers.
The old and new default phase executables produced byte-identical baseline
output. Seven malformed, repeated, or inconsistent quotient-cutoff inputs
were rejected before replay. The saved full-replay receipts identify the
shared evaluator by SHA-256, which was checked against the committed source.

The separate
[`astra_companion_t_kernel_gates.lean`](../../scripts/probes/astra_companion_t_kernel_gates.lean)
kernel-checks the three literal coefficient/rank/quotient equalities and their
ambient/cutoff arithmetic using `Std` and `decide`. Its four theorem reports
have empty axiom lists in the local check. The formulas were independently
compared with the probes. This proves the displayed finite arithmetic; the
identification with the official companion coefficient APIs is still separate.

Remaining work includes identifying the arithmetic with the packed coefficient
definitions, instantiating the common-divisor dimension theorem, updating
selected-box and residual-polynomial consumers, retuning ordinary-factor
gates for the increased total cap, certifying the phase tables and their
polynomial integration, and deriving and independently verifying a final
`ProtocolClaim`. The current combined count fails before that final step.
