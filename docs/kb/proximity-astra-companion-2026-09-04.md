# Companion challenge audit and a 68.03-bit arithmetic candidate

Status: **research candidate; full soundness unproved; Lean not run**.

This audit checked the live prize sites on 2026-09-04 and inspected the official
companion contract at commit
`b34c0131cfa36b51111521541d7d3e35c8791082`. The arithmetic probe in
[`scripts/probes/astra_companion_parameters.py`](../../scripts/probes/astra_companion_parameters.py)
is dependency-free and reproduces published integer receipts before testing new
parameters. It does not assert a new theorem, leaderboard score, or prize solution.

## What the official targets mean

The [grand challenge](https://proximityprize.org/) asks for the sharp radius at a
specified error target, such as `2^-128`, for smooth-domain Reed-Solomon codes at
rates `1/2, 1/4, 1/8, 1/16`. Its two targets concern mutual correlated agreement
and interleaved list size. The [companion challenge](https://better.codes/) was
showing a lower score of **68.02** and upper score of **116.13**, with **8.344%** of
its original displayed interval closed. These are distinct questions.

The [official README](https://github.com/proximity-prize/proximity-prize/blob/b34c0131cfa36b51111521541d7d3e35c8791082/README.md)
defines the companion score using `(1-delta)^128`. This is a spot-check score
induced by a certified reduction threshold. It is not the negative logarithm of
winning-set soundness and is not an end-to-end protocol security estimate.

- [Lower target](https://github.com/proximity-prize/proximity-prize/blob/b34c0131cfa36b51111521541d7d3e35c8791082/ProximityPrize/Benchmark/TargetLower.lean):
  certify admissibility, `certifiedGammaError(delta) <= 2^-128`, and
  `(1-delta)^128 <= 2^(-B/100)`.
- [Upper target](https://github.com/proximity-prize/proximity-prize/blob/b34c0131cfa36b51111521541d7d3e35c8791082/ProximityPrize/Benchmark/TargetUpper.lean):
  certify `winningSetDensity(delta) > 2^-128` over the entire admissible suffix
  from the submitted grid radius, and the corresponding reverse score bound.
  The target does not assume monotonicity or construct an attacking prover.

The [pinned profile](https://github.com/proximity-prize/proximity-prize/blob/b34c0131cfa36b51111521541d7d3e35c8791082/ProximityPrize/Benchmark/IRSProfile.lean)
has `n=262144`, base dimension `131072`, interleaving `8`, total dimension
`1048576`, and field size `q=p^6`, where `p=2130706433`. Its domain is the
size-`2^18` multiplicative NTT domain embedded in the sextic extension. Write
`w=131071` for maximum polynomial degree. The exact shared count budget is

```
floor(q / 2^128) = 274980728111395087.
```

The contract pins upstream ArkLib at
`e65197892890b8fd9b0dc05b8980273cf1d595cc`. The user's research fork is a different
checkout and is not automatically an admissible companion submission. The
companion source policy and verifier pin must be respected when porting proofs.

The linked [ABF26 paper landing page](https://eprint.iacr.org/2026/680) reports a
2026-07-06 revision. Its PDF download returned HTTP 403 during this audit;
statements about the exact executable challenge here rely on the inspected
pinned Lean interfaces, not a claimed complete reading of the PDF.

## Why changing the radius alone cannot improve the record

The current [lower solution](https://github.com/proximity-prize/proximity-prize/blob/b34c0131cfa36b51111521541d7d3e35c8791082/ProximityPrize/SubmissionLower/Solution.lean)
exports `ProtocolClaim 6802 10338815 33554432`. This radius is
`(80771 + 127/128)/262144`. Staying in error cell `80771` can approach only
`68.020195085...` spot-check bits. Reaching `68.03` requires tolerating error
cell **80781**, ten additional errors.

The baseline is substantive: a large locator/interpolation proof with generated
phase and factor-count certificates. In
[`PackedLocatorTail.lean`](https://github.com/proximity-prize/proximity-prize/blob/b34c0131cfa36b51111521541d7d3e35c8791082/ProximityPrize/SubmissionLower/PackedLocatorTail.lean),
`LocatorArithmetic` gives its locator parameters and ledger.
`LocatorFastKernelArithmetic` provides the arithmetic formulas used below.
The scalar closure and final protocol are in
[`PackedLocatorTail2.lean`](https://github.com/proximity-prize/proximity-prize/blob/b34c0131cfa36b51111521541d7d3e35c8791082/ProximityPrize/SubmissionLower/PackedLocatorTail2.lean).

## Exact parameter candidate

Set `e=80781`, agreement count `a=n-e=181363`, and gap `g=a-w=50292`.
The candidate radius and score are

```
delta = 10340095 / 33554432
B = 6803.
```

The script verifies both `floor(n*delta)=80781` and the exact integer inequality

```
(33554432 - 10340095)^12800 * 2^6803 <= 33554432^12800.
```

This proves the rational score conversion by ordinary positive real arithmetic.
It says nothing by itself about the reduction error.

For locator multiplicity `m`, total cap `L`, slope cap `s`, and weighted cutoff
`D=m*a`, the transcribed coefficient count is

```
C(D,L,s) = sum_{i>=0, 0<=j<=s} (L+1-i-j)_+ (D-w*i-(w-1)*j)_+.
```

The sum ends once `w*i >= D`. Here `x_+ = max(x,0)`. Define

```
R(ni,nj,o,L) = [ni*nj*(L+1-o)_+
               - nj*ni*(ni-1)/2 - ni*nj*(nj-1)/2]_+.
M_r = min(r,L), h_r = min(r+1,m-r).
K(m,L,s) = sum_{r=0}^{m-1}
  [R(M_r+1,s+1,0,L)
   - R((M_r+1-h_r)_+,(s+1-h_r)_+,h_r,L)]_+.
```

These are the published `fastCoefficientCount` and `fastLocalRankBound` under
their stated shape gate `m+s <= L+1`. The signed difference `C-n*K` is kept as an
integer in the probe, so a failed dimension inequality cannot be hidden by
natural subtraction.

| Kernel | m | L | s | D | Y degree cap | C - n K |
|---|---:|---:|---:|---:|---:|---:|
| A | 98 | 130000 | 29 | 17773574 | 135 | 36690258760 |
| B | 111 | 14914 | 33 | 20131293 | 153 | 21933893 |
| C | 270 | 130000 | 81 | 48968010 | 373 | 293702551079764 |
| T | 181 | 6679 | 56 | 32826703 | 250 | 367415844 |

All four dimension inequalities are strictly positive. Reusing the old kernel
parameters fails: at the new error count the old A, B, and T differences are
negative. Their retuning is necessary, not optional.

A separate scalar interpolant can use multiplicity `97`, total Y cap `134`, and
slope cap `29`. Transcribing `RCN279.coefficientCount` and its seedless rank gives

```
coefficient count = 28561925345
local rank bound  = 108950
C - n K           = 1336545 > 0.
```

The published list-count expression, with `Y=134` and `s=29`, is

```
cy = 1 + 2*w*Y
cr = w*(2*s-1)
Tlist = (n-w)*(cy*s + cr*Y) + (2*s-1)*Y*g
      = 264742172041443.
Llist = floor(Tlist/g) + 1 = 5264101091.
```

The exact characteristic check `cy*s+cr*Y=2019804139 < p` passes. This verifies a
specific numerical gate and the list-budget arithmetic; all other hypotheses of
the generic scalar theorem still require a proper Lean instantiation.

## What the rest of the ledger allows

The published baseline has `fixedRegularCap=254595720129422441` and total MCA
ledger `267904550184655204`. Reproducing this total is an assertion in the probe.
The remaining formulas come from `RCN260.UnequalParameters.regularCountCap` and
`RCN318.TightParameters.countCap` in
[`PackedLegacyCore1.lean`](https://github.com/proximity-prize/proximity-prize/blob/b34c0131cfa36b51111521541d7d3e35c8791082/ProximityPrize/SubmissionLower/PackedLegacyCore1.lean).

For the candidate, the script evaluates those expressions using `LB=14914`,
`LT=6679`, and selected total cap `LT-3=6676`. **This is a proposed parameter
relationship; the selected-box and quotient hypotheses have not been proved.**
The resulting arithmetic is

| Term | Candidate integer |
|---|---:|
| Fixed derivative chains and tails | 4425759424902110 |
| Residual regular stage | 531786073199204 |
| One B/B chain stage, used 32 times | 303999083030101 |
| One singular tail slot, used 34 times | 4677353824485 |
| Sum excluding the fixed regular stage | 14844546185097036 |
| MCA budget after the scalar list budget | 274980722847293996 |
| Available for the unproved fixed regular stage | 260136176662196960 |

Thus the candidate is not already ruled out by this ledger: the new fixed
regular cap could be up to `5540456532774519` above the old cap, roughly 2.18%.
But the old fixed cap is not a theorem for the new parameters, and substituting
it would be invalid. The exact remaining mathematical task is to obtain the
retuned phase-prefix, power-route, and factor-count certificates within the
allocation **260136176662196960** while discharging all changed gates.

The extension from Y cap 132 to 135 and selected total cap 6412 to 6676 affects
existing generated tables. Existing phase budgets include hardcoded contact
weights and gap constants. Those cannot be reused merely because the final
ledger has spare room.

## Attack direction checked

The current [OrbitPencil construction](https://github.com/proximity-prize/proximity-prize/blob/b34c0131cfa36b51111521541d7d3e35c8791082/ProximityPrize/SubmissionUpper/OrbitPencil.lean)
uses 512 fibres of size 512, 272 whole fibres, and a 511-point common core.
Prescribing 14 top coefficients and one product label yields a pigeonhole family
from

```
binom(511,272) / (p^14 * 512).
```

It creates more than the required `q*2^-128` winning scalars. The agreement count
is `139775`, so the unsafe grid index is `122369`; the score rounds up to 116.13.

The script searches the numerical feasibility inequality within the same
construction for fibre counts 64, 128, 256, 512, 1024, 2048, and 4096:

```
t = max(0, r - F/2 - 2)
binom(F-1,r) > floor(q/2^128) * p^t * F
agreement count = (r+1)*(n/F)-1.
```

Among these numerical cases, 512 retains the best unsafe index. This rules out a
simple improvement from those particular substitutions only; it is not an
optimality theorem for attacks. For example, the tempting 256-fibre case with
`r=136,t=6` is short by about 2 bits of guaranteed family size. A stronger bound
on a large fibre of the coefficient/product map would be a substantive new
combinatorial input, not an arithmetic correction.

## Remaining obligations and verification

Run from the research checkout:

```sh
python3 scripts/probes/astra_companion_parameters.py
```

The run on 2026-09-04 completed successfully, reproduced the pinned baseline
ranks, nullities, scalar receipt, and final ledger, and checked the candidate
integer inequalities. It uses Python integers, not floating point, for every
assertion and search decision.

To turn this candidate into an improvement:

1. Prove the retuned support, quotient, characteristic, and phase-source gates.
2. Construct and check new phase-prefix/factor-count certificates whose fixed
   regular charge fits the displayed allocation.
3. Instantiate the scalar and MCA lemmas at error cell 80781 and derive the
   squared-interleaved list bound used by `certifiedGammaError`.
4. Produce `ProtocolClaim 6803 10340095 33554432`, compile its full closure, and
   inspect the axiom census for the allowed standard axioms only.
5. Run the pinned independent verifier before claiming any ranked improvement.

No Lean build, official verification, publication, or submission was performed.
Neither grand challenge is resolved by this arithmetic candidate.
