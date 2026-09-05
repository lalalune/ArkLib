# Lower-R interpolation repairs at the binding flag

Allowing a repair of R-degree at most nine strengthens the necessary condition
from [the R-free repair argument](astra_kernel_descent_2026-09-04.md): an
irreducible factor at the binding flag can be universal on a nonzero full
source kernel only if **at least 6009 nodes have contact order at least 34**.
The R-free repair required 453 such nodes. This still does not exclude the
general binding factor or establish an improved protocol score.

The source pin is
[`032154395c51fd6f77715a7f42d9a987ab9fb48a`](https://github.com/proximity-prize/proximity-prize/commit/032154395c51fd6f77715a7f42d9a987ab9fb48a).
This note treats one fixed repair box; it does not search source parameters or
modify the phase recurrence.

## The repair need only have smaller R degree

The earlier descent proof remains valid with `degree_R(P)<degree_R(F)` in place
of R-freeness. If F divides every element of the full source kernel, choose a
nonzero Q with minimum R degree and write Q=F Q'. If P repairs the lost contacts
and satisfies

```text
contactWeight(P) <= contactWeight(F),
residualTotal(P) <= residualTotal(F),
degree_R(P) < degree_R(F),
```

then P Q' has the required contacts, remains in the original flag box, and has
strictly smaller R degree than Q. This is a contradiction. No derivative or
characteristic hypothesis is needed for this interpolation version of repair.

For a factor of R-degree r, define the cap-s repair dimension, for `s<r`, by

```text
C_s(c,t) = coefficientCount(c+1,w,t,s).
```

Set `b_i=min(m,nu_i(F))`, where m is the full source contact order. The rank of
the node-i contact map on that repair box is at most
`R_s(b_i,t)=RCN119.localRankBound(b_i,t,s)`. Consequently

```text
C_s(c,t) > sum_i R_s(b_i,t)
```

produces a nonzero repair by rank-nullity, contradicting universal divisibility.
Every such factor therefore necessarily satisfies the reverse inequality.
This is an additional profile constraint; no claim is made that its normalized
inequality dominates the R-free inequality for every profile.

The rank bound is the existing `RCN100.localTarget_finrank_le` in
[`PackedLegacyCore1.lean`](https://github.com/proximity-prize/proximity-prize/blob/032154395c51fd6f77715a7f42d9a987ab9fb48a/ProximityPrize/SubmissionLower/PackedLegacyCore1.lean#L16701).
It has no hypothesis `s<=b_i`, which matters when some node orders are small.
For a nonuniform profile, take the product of these node-dependent targets and
sum their dimensions. Connecting that construction to the formal repair lemma
remains a Lean integration obligation.

## Exact cap-nine computation

Use the exact binding factor degrees `(total,YS,R)=(2364,47,10)` and
`w=131071`, `n=262144`. The previous note proves

```text
c(F) >= w*47-10 = 6160327,
nu_i(F) <= YS(F)+degree_R(F) = 57.
```

The second bound uses irreducibility and positive R degree to ensure that
`X-x_i` does not divide F. Assume the full source multiplicity is at least 57,
as it is for the sources under consideration. Thus b_i=nu_i. The fixed repair
box is

```text
(D,t,s)=(6160328,2364,9).
```

Its conservative contact cap is at most the actual c(F). Its residual total
does not exceed the exact t(F), and its R degree is strictly below ten. It
also has joint YR degree at most 46, since `D+9=w*47`.

| Quantity | Exact value |
|---|---:|
| Repair coefficient count C9 | 2856185117975 |
| Node rank bound R9(33,2364) | 10367785 |
| Node rank bound R9(57,2364) | 33389585 |
| C9 minus n times R9(33,2364) | 138332486935 |
| Maximum extra rank per node above order 33 | 23021800 |
| Necessary number of nodes with order at least 34 | 6009 |

Indeed, if h nodes have order at least 34, monotonicity of the local rank bound
and `nu_i<=57` give

```text
sum_i R9(nu_i,2364) <= n*R9(33,2364)+h*(R9(57,2364)-R9(33,2364)).
```

For h=6008 the right-hand side is strictly below C9, producing the forbidden
repair. For h=6009 this particular coarse estimate no longer contradicts
universality. This is the exact rounded consequence of the displayed bounds,
not a realizability assertion about a degree flag or order profile.

The all-node order-34 profile still passes the necessary inequality:

```text
C9 - n*R9(34,2364) = -43076403945.
```

That arithmetic profile is not a constructed polynomial, universal factor,
or far-word/large-family witness. Additional information about realizable
contact-order profiles remains necessary. A larger actual c(F) can strengthen
the repair bound further; this calculation uses only the conservative degree
information at the binding flag.

## Scope and reproduction

Run `python3 scripts/probes/astra_kernel_lowr_audit.py`. It independently
evaluates the coefficient and rank sums with literal positive parts, compares
them to the existing closed-form evaluators, and checks all node orders
0 through 57. The rectangular closed-form gate is `b+9<=2365`, which holds
throughout. The script also constructs 27 small contact matrices by direct
multinomial substitution over F2, F5, and F101 and verifies the rank upper
bound. These are transcription checks, not production finite-field evidence.

As with the original descent lemma, the full kernel must contain every
polynomial obeying its contact and flag-box constraints. An arbitrary
post-projection universal-factor domain need not be closed under `Q -> P Q/F`.
No such closure is assumed here, and no companion Lean proof or leaderboard
submission is generated by the probe.
