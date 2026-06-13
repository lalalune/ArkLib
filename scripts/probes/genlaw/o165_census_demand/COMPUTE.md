# COMPUTE.md — EXACT deep-band #bad-scalar / #alignable-a-set computation vs K(16)
# (CensusDomination demand side, #389 delta* prize, complement of O164 fiber side)

Worktree: /home/nubs/Git/ArkLib-232 (origin/main, synced 2026-06-13).
Deliverables rescued here (/tmp is tmpfs): cd_demand.c (C residual-det kernel),
crosscheck_r7.py (triple-method check), plus the prior O165 python (pin_n16.py,
worstcase_badscalar.py, verify_ceiling.py, verify_residual_def.py, badscalar_demand.py,
adversary_deep.py). PIN.md holds the object/budget/prime pins.

## 0. WHAT WAS COMPUTED (this pass)

A NEW INDEPENDENT C KERNEL (cd_demand.c) recomputing the demand side from the GROUND-TRUTH
bordered-Vandermonde residual determinant (the literal Lean `Aligned` def, UniversalAlignmentLaw
L178 / OwnershipBound L48), distinct from the O165 python which used interpolation-coefficient
Gaussian elimination. The C kernel reproduces every prior O165 number EXACTLY, and the tightest
band was triple-checked by two further independent python methods. Then n=32 feasibility was
re-measured (not assumed) and the honest frontier pinned.

Pin (CensusDominationWeld L84, m=1, n=2^mu): k_c=(r-2)m+1=r-1, a0=rm+1=r+1, deep band r~n/2.
Faithful prime BabyBear p=2013265921, p^2=4.05e18 >> C(16,8)=12870 (faithful by 14 orders; no
saturation, dodges the O164 pigeonhole trap).

## 1. KKH26 CANONICAL STACK at the DEEP band a0=rm+1, n=16  [COMPUTED]

cd_demand.c `kkh 16` (residual-det kernel) == pin_n16.py (interp kernel), identical:

  r  kc  a0  C(16,a0)  #alignable  #badscal     K    pack   ok
  2   1   3       560          0         0     112    140   OK
  3   2   4      1820          0         0     448    364   OK
  4   3   5      4368          0         0    1120    728   OK
  5   4   6      8008          0         0    1792   1144   OK
  6   5   7     11440          0         0    1792   1430   OK
  7   6   8     12870          0         0    1024   1430   OK
  8   7   9     11440          0         0     256   1144   OK

The canonical KKH26 monomial stack (u0=x^{rm}, u1=x^{(r-1)m}) gives #alignable=0, #bad=0 at the
DEEP band for ALL r. Mechanism: its agreement is exactly rm (the fiber size), one short of the
deep band a0=rm+1. The KKH26 supply 2^r*C(n/2,r) lives at the CEILING band a=rm, NOT the deep band.

Kernel validation against the known regime (cd_demand.c `ceil 16` == verify_ceiling.py, EXACT):
  r=2..8 ceiling a=rm: #alignable = 120,560,1820,4368,8008,11440,12870 (= C(16,rm), the lossy
  full count), #badscal = 113,464,1233,2256,3025,3280,3281. Reproduces the q-dependent KKH26
  supply -> kernel is correct.

## 2. WORST-CASE-OVER-STACKS at the DEEP band a0=rm+1, n=16  [MEASURED-FAITHFUL]

The canonical KKH26 is 0 at the deep band, so the worst-case demand is over a stack SEARCH.
EXACT exhaustive over all 240 monomial pairs (e!=f), plus 200 random + structured P(x^d) trials
(cd_demand.c `wide`), faithful BabyBear. Headline #bad counts are EXACT (monomial maximizers
found by exhaustive enumeration; random/structured only confirm monomials win, never beat them):

  r  a0  worst #bad-scalar   maximizer       K     K/bad   pack   bad<=K?  bad<=pack?
  3   4        97            x^8,x^7        448    4.6x    364    YES      YES
  4   5       145            x^8,x^5       1120    7.7x    728    YES      YES
  5   6        89            x^9,x^15      1792   20.1x   1144    YES      YES
  6   7       113            x^8,x^10      1792   15.9x   1430    YES      YES
  7   8       225            x^10,x^15     1024    4.6x    1430    YES      YES   <- TIGHTEST
  8   9       104            x^9,x^11       256    2.5x    1144    YES      YES

Prize window for n=16: r in (sqrt(16 ln16)=6.66, 8] = {7,8}. The deepest bands r=7,8 hold:
r=7 #bad=225<=K=1024 (margin 4.6x), r=8 #bad=104<=K=256 (margin 2.5x). The worst-case maximizer
is a HIGH-FREQUENCY monomial pair (x^8 = the order-2 element -1), NOT the canonical KKH26 stack.
Bad count is O(n) (linear), matching probe_deltastar_badscalar_transversal.py.

CALIBRATION (sanity gate, every row): exact #bad <= packing upper bound C(n,a0)/(a0+1). PASSES
everywhere (e.g. r=7: 225 <= 1430). The exact count sits FAR below both the packing bound and K.

## 3. THE LITERAL CensusDomination (alignable-SETS form) IS FALSE at the deep band  [COMPUTED]

cd_demand.c `one 16 r 0 (r-1) a0` (codeword stack u0=x^0 const, u1=x^{r-1}):
  r=3 a0=4: #align=1820 (=C(16,4)) #bad=1   K=448
  r=5 a0=6: #align=8008 (=C(16,6)) #bad=1   K=1792
  r=7 a0=8: #align=12870(=C(16,8)) #bad=1   K=1024
A degenerate codeword stack makes EVERY a0-set alignable (#align = C(n,a0) >> K, up to 12.6x at
r=7) but pins only ONE bad scalar. This FALSIFIES CensusDomination AS LITERALLY STATED (the
alignable-SETS cap, CensusDominationWeld L69-74) -- but ONLY via the lossy overcount that
SinglePencilQIndependence.lean L19-23 was explicitly built to bypass. It is NOT a refutation of
the delta* Prop: the quantity that controls delta* is the #bad-SCALAR count, which holds (Sec 2).

## 4. n=32 FEASIBILITY  [INFEASIBLE for worst-case; MEASURED extrapolation]

MEASURED throughput (cd_demand.c, taskset -c5): n=32 r=6 a0=7 single stack = 3,365,856 sets in
16.4s = 205,235 sets/s (6x6 dets, 7 subtuples/set). Extrapolating with cost ~ C(a0,kc+1)*(kc+1)^3:

  r=10 a0=11: C(32,11)=129,024,480 -> est 76 min / SINGLE stack
  r=11 a0=12: C(32,12)=225,792,840 -> est 194 min (3.2 h) / single stack
  r=13 a0=14: C(32,14)=471,435,600 -> est 13.0 h / single stack
  r=15 a0=16: C(32,16)=601,080,390 -> est 29.0 h / single stack
  r=16 a0=17: C(32,17)=565,722,720 -> est 35.3 h / single stack

The SHALLOWEST n=32 deep band (r=10) already needs 76 min for ONE stack -> EXCEEDS the 15-min cap.
(Corrects the PIN.md "~9 min/stack" estimate, which was optimistic; the measured C cost is higher.)
A worst-case SEARCH (240 monomial pairs) at r=11 = 240 x 3.2h ~= 770 h ~= 32 days: INFEASIBLE.
Syndrome reduction (census over affine lines in F_q^{n-k}) is q^{2(n-k)} at faithful q~2e9:
astronomically infeasible without the (open) rotation-quotient + coset-direction restriction.

n=32 SPOT-CHECKS (cheap bands only, cd_demand.c `one`), confirm scale-invariant mechanism:
  KKH26 deep band a0=rm+1, r=3,4,5: #align=0, #bad=0 (same "one short of rm+1" mechanism as n=16).
  KKH26 ceiling band a=rm, r=3,4: #align=4960,35960 #bad=4512,29601 (nonzero supply, kernel valid).

CONCLUSION: n=16 is the HONEST EXACT WORST-CASE FRONTIER. n=32 admits only single-stack
spot-checks (and only on bands shallower than the deep band within the 15-min cap), NOT a
worst-case verdict.

## 5. INTERNAL CROSS-CHECKS (every headline triangulated)

(i)   C residual-det kernel (cd_demand.c) == python interp-coeff kernel (pin_n16.py): KKH26
      deep band all-zero, identical across r=2..8.
(ii)  C ceiling-band (cd_demand.c `ceil`) == verify_ceiling.py: 120/560/1820/4368... identical.
(iii) C worst-case mono search (`mono`/`wide`) == worstcase_badscalar.py: 97/145/89 for r=3,4,5
      identical; deep band extended here to r=6,7,8 (113/225/104).
(iv)  TIGHTEST band r=7 TRIPLE-checked (crosscheck_r7.py): interp-coeff #bad=225, residual-det
      #bad=225, C kernel #bad=225 -- all three agree; #align=266 (interp) == 266 (residual-det).
(v)   GROUND-TRUTH check (verify_residual_def.py): residual-det == interp-coeff on KKH26(=0) and
      codeword stack(=1820), the two Lean definitions coincide.

## 6. VERDICT

CENSUSDOMINATION-HOLDS-WITH-MARGIN (bad-scalar form) at n=16, the feasible exact frontier.

- The delta*-controlling quantity (#BAD-SCALARS) holds vs the KKH26 budget K with margin
  2.5x-20x across the WHOLE deep band; tightest at r=7 (225 vs 1024, 4.6x) and r=8 (104 vs 256,
  2.5x). First direct faithful positive evidence the prize Prop is true at the demand level.
  Calibrated: exact <= packing C(n,a0)/(a0+1) everywhere.
- The literal alignable-SETS form of CensusDomination is FALSE at the deep band (codeword stacks
  -> C(n,a0) >> K, #bad=1) -- a narrow, KNOWN lossy-overcount negative: the correct in-tree
  obligation is the #bad-SCALAR form (SinglePencilQIndependence route), not the alignableSets cap.
- foundCounterexample = TRUE *for the literal alignable-SETS object*; FALSE for the bad-scalar
  object that actually gates delta*. Headline: NO counterexample to the delta* Prop; YES the
  literal CD normal-form is too weak as written.
- n=32: INFEASIBLE for a worst-case verdict (measured 76 min - 35 h per single stack at the deep
  band, >15-min cap; a search is ~weeks). n=16 is the honest exact frontier.
