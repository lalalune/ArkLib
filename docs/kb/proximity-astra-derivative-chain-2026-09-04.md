# A shared derivative-chain budget for the companion candidate

Status: **new arithmetic theorems checked by the Lean kernel; mathematical
polynomial bridge described below; full companion proof not ported or built**.

The official companion source is pinned at
`b34c0131cfa36b51111521541d7d3e35c8791082`. This note concerns its error cell
`80781`, proposed score `6803`, and radius `10340095/33554432`. It does not
resolve either grand challenge or certify a leaderboard improvement.

## The factorization matters

In the pinned
[`LocatorResidual.gcd_residual_count_lt`](https://github.com/proximity-prize/proximity-prize/blob/b34c0131cfa36b51111521541d7d3e35c8791082/ProximityPrize/SubmissionLower/PackedLocatorTail2.lean),
the proof sets

```
H = gcd12 QA QB
Q = quotientB QA QB
T = quotientA QA QB
QB = H * Q
QA = H * T.
```

The fixed seeds are zeros of H; on the residual seeds, H is nonzero and both
Q and T vanish. The published final ledger applies a derivative-chain count
to H and then a separate derivative-chain count to Q. Both use the full B
slope allowance 33. This loses the relation

```
degree_R H + degree_R Q = degree_R QB <= 33.
```

H and Q need not be coprime. If the same irreducible factor occurs in both,
its degree is counted twice in the two lists and also in the product degree;
the argument still holds. No disjointness assumption is needed.

For each polynomial, the sum of R-degrees of its distinct positive-R factors
is at most its R-degree. Thus concatenating the two factor-degree lists gives
a list of nonnegative integers with sum at most 33. This permits **one** chain
budget for both stages. The regular-seed and R-free-tail terms are left at
their existing separate upper bounds.

## Derivative pairs have smaller degrees

Write `n=262144`, `w=131071`, `a=181363`, `g=a-w=50292`, and
`D_B=111*a=20131293`. In RCN174, membership in the B coefficient box means
every support monomial with exponents `(x,y,r,z)` satisfies

```
y+z <= L,  r <= 33,  x+w*y+(w-1)*r < D_B.
```

This is the **RCN174 box**. Its first bound omits R. The RCN100 flag box is
different and bounds `y+r+z`. Differentiating R does not decrease L in the
RCN174 argument used here.

Let F be an irreducible positive-R factor of H or Q, and put
`d=degree_R F`. For `1 <= j < chainLength F <= d <= 33`, iterating
`support_before_pderiv` shows that any support exponent of `dR j F` comes
from an exponent of F with j added to R. Therefore

```
dR j F belongs to box (D_B-j*(w-1), w, L, d-j)
degree_Y(dR j F) <= floor((D_B-j*(w-1)-1)/w) = 153-j.
```

The undifferentiated right factor has caps `(153,d,L)`. The existing
`dR_ne_zero` and `isRelPrime_dR` lemmas apply because `d < p=2130706433`.
Consequently the proof of `chainSeeds_card_le` can be sharpened by applying
`all_regularPairSeeds_bound` with left caps `(153-j,d-j,L)` and right caps
`(153,d,L)`. The seed-cover argument itself is unchanged.

The scripts check every resulting degree and mixed-characteristic gate for
all 528 pairs `1 <= j < d <= 33`, at both L6676 and L14914. The characteristic
checks are exact integer inequalities. The support-shift and quotient-floor
arithmetic also have ordinary Lean proofs. The iterated polynomial-support
lemma and its integration with the companion seed-count theorem remain to be
formalized against the companion's pinned Mathlib/ArkLib dependencies.

## Exact cost and the universal partition theorem

For one derivative step, set

```
yl=153-j, rl=d-j
Ay=1+2*w*153, Ar=w*(2*d-1), Az=2*w*L+1
My=rl*L+L*d
Mr=yl*L+L*153
Mz=yl*d+rl*153
C_L(d,j)=floor(((n-w)*(Ay*My+Ar*Mr+Az*Mz)+(80781+1)*g*Mz)/g)
F_L(d)=sum_{j=1}^{d-1} C_L(d,j).
```

This is `RCN260.UnequalParameters.regularCountCap` for the displayed caps;
the right agreement vector dominates the left one in every coordinate.
Empty chains have cost zero. Missing derivative stages can only reduce the
sum, since each cost is nonnegative.

The new file
[`astra_companion_chain_budget.lean`](../../scripts/probes/astra_companion_chain_budget.lean)
checks, for L6676 and L14914, all 595 inequalities

```
F_L(a)+F_L(b) <= F_L(a+b),   a+b <= 33.
```

It then proves by list induction, for **every** finite list `ds`,

```
sum(ds) <= 33  ==>  sum(map F_L ds) <= F_L(33).
```

The shared-stage theorem applies this result to the concatenation of the fixed
and residual lists, using the larger L14914 for both. Since H and Q both divide
QB, both fit the B box. This avoids any comparison of different box costs in
the shared theorem.

| Quantity | Exact value |
|---|---:|
| Old fixed chain: 32 identical charges at L6676 | 4354575827795872 |
| Old residual chain: 32 identical charges at L14914 | 9727970656963232 |
| Sharper fixed chain, if charged separately | 3504566234932802 |
| Sharper residual chain, if charged separately | 7829081955871376 |
| One shared chain for both stages | 7829081955871376 |
| Saving against the original two-chain ledger | 6253464528887728 |

The old candidate allocated `260136176662196960` to its fixed regular stage.
The shared-chain expression instead allocates **266389641191084688**, keeping
the other regular and tail charges unchanged. This is a conditional ledger
until the polynomial and cover bridges are formally integrated.

## Verification and limits

Run:

```sh
python3 scripts/probes/astra_companion_chain_budget.py
lean scripts/probes/astra_companion_chain_budget.lean
```

The Python audit cross-checks the costs against the existing general
`regular_count` transcription, checks all characteristic gates and
superadditivity inequalities, and independently solves the degree-partition
dynamic program. It agrees with the two closed chain values.

Lean 4.30.0-rc2 checked the final file successfully on 2026-09-04 in 16.62 seconds,
with maximum resident set size 1382907904 bytes. The printed axiom lists for
`shifted_support_y_cap`, `derivative_y_cap`, `selected_chain_budget`,
`residual_chain_budget`, and `shared_chain_budget` are exactly
`[propext, Quot.sound]`. There is no `native_decide`, custom axiom, or unfinished
proof in this certificate. The universal list theorem is a proof by induction;
ordinary kernel `decide` checks only the bounded numerical inequalities.

The checked file imports Std and is not an executable companion submission.
The companion pins a different Lean/dependency version. Its full closure and
`ProtocolClaim 6803 10340095 33554432` have not been built or accepted by the
independent verifier. The phase search and original candidate obligations are
tracked in the [companion audit](proximity-astra-companion-2026-09-04.md).
