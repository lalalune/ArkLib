# Companion audit and a numerically feasible 68.03-bit proof candidate

Status: **a six-source successor fits the arithmetic budget after a shared-chain
refinement; chain arithmetic kernel-checked; full companion proof unported;
no new verified score**.

This audit checked the live prize sites on 2026-09-04 and inspected the official
companion contract at commit
`b34c0131cfa36b51111521541d7d3e35c8791082`. The arithmetic probe in
[`scripts/probes/astra_companion_parameters.py`](../../scripts/probes/astra_companion_parameters.py)
is dependency-free and reproduces published integer receipts before testing new
parameters. The compact C++ phase evaluator also reproduces the published fixed
regular cap exactly. The first candidate failed the numerical phase allocation
by over 5%. The later six-source construction below fits a refined ledger, with
the full polynomial and phase proof still outstanding. The numerical scripts
do not certify a new theorem, leaderboard score, or prize solution.

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

The linked [ABF26 paper](https://eprint.iacr.org/2026/680) reports a 2026-07-06
revision. Its PDF initially returned HTTP 403, but a subsequent retrieval on
2026-09-04 succeeded. The relevant introduction, Definition 4.3, positive and
negative results in Section 4, and Appendix C were inspected. They confirm the
distinction between the broad sharp-threshold challenge and the executable
fixed-profile companion contract. Claims about the executable target below
use the pinned Lean interfaces.

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

This ledger initially allowed a new fixed regular cap up to `5540456532774519`
above the old cap, roughly 2.18%. That was a feasibility test, not evidence that
the fixed regular bound would fit. The phase regeneration below rejects this
first candidate. Substituting the old cap would be invalid: it is not a theorem
for the new parameters. An improvement needs a substantially sharper fixed
regular bound within **260136176662196960**, alongside all changed gates.

The extension from Y cap 132 to 135 and selected total cap 6412 to 6676 affects
existing generated tables. Existing phase budgets include hardcoded contact
weights and gap constants. Those cannot be reused merely because the final
ledger has spare room.

## Regenerated phase budget: exact baseline and failed candidate

The evaluator
[`astra_companion_phases.cpp`](../../scripts/probes/astra_companion_phases.cpp)
uses signed 128-bit integers, an exact zero-slice knapsack, upper envelopes of
integer affine functions, and componentwise prefix maxima. It has four modes:

| Mode | Fixed regular envelope | Excess over candidate allocation |
|---|---:|---:|
| Published baseline, original inputs | 254595720129422441 | not applicable |
| First candidate, retuned four sources | 274912523147183536 | 14776346484986576 |
| Candidate with full z-dependent prefixes | 274535875126515098 | 14399698464318138 |
| Candidate with all-sources recursive closure | 274535875126515098 | 14399698464318138 |

The baseline matches the published cap **exactly**, with maximizing raw flag
`(r,v,z)=(18,49,6259)`. The first candidate maximizes at `(19,50,6523)`;
its four successive phase costs are

```
367843844691741053
278307060379860955
276768223758847701
274095080993375018.
```

Adding the initial A-source complement yields the table's first-candidate cap.
The z-aware version maximizes at `(15,36,6523)`. Its improvement is too small to
close the deficit. This is an obstruction to these particular numerical
envelopes and parameter choices, **not a lower bound proving that every proof
of 68.03 must fail**.

The definitions are from the pinned
[`PackedLocatorTail.lean`](https://github.com/proximity-prize/proximity-prize/blob/b34c0131cfa36b51111521541d7d3e35c8791082/ProximityPrize/SubmissionLower/PackedLocatorTail.lean)
and the adjacent `PackedLocatorTail1.lean` and `PackedLocatorTail2.lean`:

1. A raw flag is `(z,v,r)`; its total, middle, and slope degrees are
   `t=z+v+r`, `y=v+r`, and `s=r`.
2. `ordinaryCostOf` uses the C2 hybrid envelope when `r>=3,v>=2`, otherwise
   the padded envelope. Its cost is affine in `z` for `z>=3`. The source's
   convex-carrier lemma moves all z degree to one factor for the **base**
   knapsack envelope. The probe does not assume phase-refined caps are convex.
3. For each source, `Routeable` tests whether either the full quotient-channel
   sum or its contact-thinned version is strictly below source nullity.
   A routeable parent has a linear potential charge plus a prefix defect for
   child flags of strictly smaller slope.
4. The published coarse construction maximizes defects over z. The alternative
   retains z in the componentwise prefix maximum. Strict slope decrease makes
   this recurrence well founded; a new prefix-soundness proof/certificate still
   needs to be instantiated in Lean.

The retuned source interpolation data are:

| m | L | S | Y | Signed nullity |
|---:|---:|---:|---:|---:|
| 4800 | 328400 | 1480 | 6641 | 5090867013182078230 |
| 1200 | 82100 | 370 | 1660 | 18278038734560710 |
| 1000 | 42000 | 310 | 1383 | 4003459072456058 |
| 390 | 19500 | 120 | 539 | 91073661700890 |

Here `D=m*a`, `Y=floor((D-1)/w)`, `a=n-e`, and `g=a-w`. For the phase sources,
write `Ay=1+2*w*Y`, `Ar=w*(2*S-1)`, and `Az=2*w*L+1`. The retuned linear
potential coefficients (total, middle, slope) are

```
ceil((n-w)*(Ay*S+Ar*Y)/g)
ceil((n-w)*(Ar*L+Az*S)/g)+(e+1)*S
ceil((n-w)*(Ay*L+Az*Y)/g)+(e+1)*Y.
```

The published baseline potentials add 10000 to each corresponding ceiling.
The evaluator uses those published coefficients, and the published initial
A-source vector `(5961153504,5974067721865,22929595672934)`, for its baseline
assertion. The candidate uses the ceiling coefficients; its initial A source
uses `max(Y,153)` and `max(S,33)` in the agreement coefficients to dominate the
wider selected box. Proving this domination at the new parameters is a Lean
obligation, not something established by matching the baseline.

The evaluator checks positive source nullity and the following necessary gates:
`L>=m+S`, `S<=m<p`, `D+S<=w*(Y+1)`, source caps dominating the selected box,
and the three helper mixed products below `p`. The shape condition with **D+S**
matters: the definition of Y alone only guarantees a condition on D. Binary
search for routing uses the source theorem's monotonicity, with selected total
cap at most source L. Remaining ordinary-factor characteristic and quotient
gates, generic theorem instantiation, and Lean compilation remain unproved.

Additional bounded experiments did not close the gap:

- The candidate T nullity exceeds the total-degree-two quotient coefficient
  count `326956325` by `40459519`. This necessary quotient dimension test passes.
- Searching T multiplicities 80 through 420 and slopes from 27% through 35%
  found a smallest L of 6657 at `(m,S,Y)=(194,60,268)`, with quotient margin
  `80130328`. This is only 22 below the proposed L6679. It is a bounded search,
  and substituting that source would change other ledger terms and gates.
- A source with `(m,S,Y)=(97,29,134)` becomes feasible at `L=223128`. Using it
  instead of A98 lowers the Y cap by one but raises the potential complement;
  the z-aware envelope increases to `275262086275345898`.
- Replacing all four defects by recursively closed final-child defects gave the
  same z-aware maximum. The initial source-shape sweeps failed to produce a viable
  bound; those searches are exploratory and do not establish optimality.

## Numerically feasible successor using a shared chain budget

The [derivative-chain note](proximity-astra-derivative-chain-2026-09-04.md)
identifies two refinements. First, the j-th derivative has smaller weighted and
slope degrees. Second, the fixed gcd H and residual Q satisfy `QB=H*Q`, so their
two factor-degree lists share a total R-degree budget of 33. Charging each stage
the full budget separately is unnecessary.

The new Std-only Lean file proves the corresponding arithmetic for every
finite degree partition. Applying it to the actual polynomial factors and seed
cover remains a formalization obligation. With the larger B box used for both
chains, the new combined chain charge is `7829081955871376`. It saves
`6253464528887728` against the original two-chain expression.

The root A/B/C/T and scalar interpolants are unchanged from the candidate table
above. A bounded search found the following compact phase-source set:

| m | L | S | Y | Signed nullity |
|---:|---:|---:|---:|---:|
| 8000 | 560000 | 2464 | 11069 | 40890965512431461440 |
| 4000 | 280000 | 1232 | 5534 | 2515200173660695446 |
| 1600 | 112000 | 492 | 2213 | 61152530622794379 |
| 1200 | 84000 | 369 | 1660 | 18802099200935610 |
| 650 | 52000 | 200 | 899 | 1754780192812150 |
| 250 | 20000 | 77 | 345 | 24306064036059 |

The exact recurrence retains z in the prefix and uses final child caps from
strictly smaller R-degree. Its fixed regular envelope is
`266199718851190708`, attained at `(r,v,z)=(14,35,6523)`. The initial A-helper
complement is included, as is the empty universal-child case. All six source
kernels have positive nullity and pass the necessary shape, domination, and
mixed-characteristic inequalities checked by the evaluator.

| Ledger quantity | Exact integer |
|---|---:|
| Fixed regular envelope | 266199718851190708 |
| Other terms after the shared-chain refinement | 8591081656209308 |
| Scalar list budget | 5264101091 |
| Combined proposed count | 274790805771501107 |
| Field count capacity | 274980728111395087 |
| Positive margin | 189922339893980 |

Thus the proposed integer count passes
`combined_count * 2^128 <= p^6`. The radius-to-score inequality for 6803 also
passes. **A numerical count expression fitting the budget is not a proof that
the true winning-set count is bounded by that expression.** The polynomial
bridges, phase soundness, and the rest of the retuned theorem gates must still
be proved and compiled.

Run the complete arithmetic receipt with:

```sh
python3 scripts/probes/astra_companion_shared_candidate.py
python3 scripts/probes/astra_companion_shared_candidate.py --check-phases
python3 scripts/probes/astra_companion_shared_candidate.py --sanitize
lean scripts/probes/astra_companion_chain_budget.lean
```

The phase replay compiles the C++ evaluator and asserts the same maximum in
forward, reverse, and rotated source orders. The sanitizer mode also checks for
undefined integer behavior. The independent Python transcription checks source
nullities, root kernels, quotient dimension, scalar conditions, and both exact
integer capacity and score inequalities. Its inner coefficient sums are
evaluated using exact sums of 1, i, and i-squared, and cross-checked against the
original double sum on the four root kernels.

The 2026-09-04 runs passed in all three source orders, both optimized and under
undefined-behavior instrumentation. Nine malformed/out-of-range input cases
were rejected. An additional multiplicity-96000 source exercised the widened
integer paths; its nullity matched the independent Python calculation and the
six-source maximum stayed unchanged. The four original baseline/candidate
replays also retained their exact recorded values. Tracked documentation links
and the forbidden-token precheck passed. Full `scripts/validate.sh` stopped at
exit 127 because `lake` is unavailable; it did not complete a repository build.

The search is not an optimality certificate. A 15-source set reaches
`265783441651992192`; a 52-source set reaches `265483881194044562`, and a
194-source set reaches `265309898373802401`. Greedy pruning produced the six
sources above. Removing one further source from that particular six-source set
gave a best tested five-source cap `266498137406098741`, just outside the
refined allocation. Other five-source choices are not ruled out.

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
python3 scripts/probes/astra_companion_parameters.py --check-phases
```

The run on 2026-09-04 completed successfully, reproduced the pinned baseline
ranks, nullities, scalar receipt, and final ledger, and checked the candidate
integer inequalities. The optional second command compiles the compact C++17
evaluator in a temporary directory, runs all four modes, and asserts the exact
baseline and rejected-candidate receipts. It needs `clang++` or `g++` with
128-bit integer support. No generated table or binary is committed. Python
integers or signed 128-bit integers, never floating point, determine these
assertions and phase maxima.

To turn this candidate into an improvement:

1. Prove the retuned support, quotient, characteristic, and phase-source gates.
2. Construct and check new phase-prefix/factor-count certificates whose fixed
   regular charge fits the displayed allocation.
3. Instantiate the scalar and MCA lemmas at error cell 80781 and derive the
   squared-interleaved list bound used by `certifiedGammaError`.
4. Produce `ProtocolClaim 6803 10340095 33554432`, compile its full closure, and
   inspect the axiom census for the allowed standard axioms only.
5. Run the pinned independent verifier before claiming any ranked improvement.

No full companion Lean build, official verification, or prize submission was
performed. The finite monomial certificate and new derivative-chain arithmetic
theorems are separately kernel-checked. Neither grand challenge is resolved.
The first 68.03 candidate fails its phase allocation; the six-source successor
fits its refined numerical ledger but still needs the full formal proof.
