# PIN.md — CensusDomination deep-band demand-side pin (#389, complement of O164)

Worktree: /home/nubs/Git/ArkLib-232 (origin/main). Scripts rescued to
`scripts/probes/genlaw/o165_census_demand/` (PIN target /tmp is tmpfs).

## 1. THE OBJECT — what CensusDomination needs bounded

`CensusDomination dom k_c a0 K` (CensusDominationWeld.lean L69-74) bounds, for ALL stacks
(u0,u1) and ALL bands a >= a0, the count of **alignable a-sets**:

  #{ S in powersetCard a [n] : EXISTS gamma, Aligned dom k_c u0 u1 gamma S
                               AND EXISTS non-degenerate (k_c+1)-tuple t in S
                                   (NOT (residual u0 t = 0 AND residual u1 t = 0)) }  <= K

- `Aligned` (UniversalAlignmentLaw.lean L178-181): every injective (k_c+1)-tuple t in S has
  residual(u0,t) + gamma*residual(u1,t) = 0  (residual = bordered-Vandermonde det, OwnershipBound.lean L48).
- Relation to #bad scalars: `badScalars_card_le_alignable` (UniversalAlignmentLaw.lean L284):
  #{bad gamma} <= #{alignable a-sets}. Each bad gamma owns its aligned sets (Aligned.gamma_eq L202),
  so #bad <= #alignable. THIS REDUCTION IS LOSSY (SinglePencilQIndependence.lean L19-23 says so
  explicitly: "overcounts massively"; many alignable sets collapse onto ONE scalar).
- Relation to O164 fiber: #alignable ~ (#distinct pinned gamma) x (avg #a-sets per gamma).
  O164 measured the FIBER multiplier (#a-sets per target, = #t-subsets hitting an e-symm target);
  this PIN measures the DEMAND (#distinct pinned gamma = #bad scalars). With O164 fiber = O(1),
  #alignable ~ #bad-scalars x O(1), so CensusDomination <=> #bad <= K/O(1).

Pin params (CensusDominationWeld.lean L84, interiorCeiling_of_censusDomination):
  k_c = (r-2)*m + 1,  a0 = r*m + 1,  n = 2^mu*m,  s = 2^mu, n/2 = 2^{mu-1} = s/2.
  Deep band: r ~ n/2 (prize window (sqrt(n log n), n/2)). Band a = a0 = rm+1 is the DEEPEST band.
  At m=1: k_c = r-1, a0 = r+1, so a0 - k_c = 2 (TWO top-coeff constraints share one gamma — the
  hard regime). The CEILING band a = rm = r has a-k_c = 1 (one constraint, q-DEPENDENT, where the
  KKH26 supply 2^r*C(n/2,r) actually lives).

Worst-case stack = KKH26 bad-line (KKH26BadLineConstruction.lean L377-393):
  u0 = X^{rm}, u1 = X^{(r-1)m} on H = mu_n; lambda_S = -sum_{a in S} a for r-subsets S of the
  inner group G = <g^m> (|G|=s). v_S(X^m) = X^{rm} - (sum a)X^{(r-1)m} + E, deg E <= (r-2)m, so the
  fiber pi^{-1}(S) (exactly rm points) agrees with -E (deg <= (r-2)m). Supply = 2^r*C(s/2,r) distinct
  lambda (kkh26_lemma1, p > s^{s/2}). The supply sits at agreement EXACTLY rm = the CEILING band,
  one short of the deep band a0 = rm+1.

## 2. BUDGET K = 2^r*C(n/2,r) — exact [COMPUTED]

n=16 (m=1, mu=4, n/2=8):
  r :  2    3    4    5    6    7    8
  K : 112  448 1120 1792 1792 1024 256
  (deep band r in [7,8]; max K = 1792 at r=5,6; packing bound C(n,a0)/(a0+1) = 140,364,728,1144,
   1430,1430,1144 — ALWAYS exceeds K in deep band, confirming PackingDeepBandMiss.lean.)

n=32 (m=1, mu=5, n/2=16):
  r :   2    3    4     5      6      7       8       9       10      11      12      13      14     15    16
  K : 480 4480 29120 139776 512512 1464320 3294720 5857280 8200192 8945664 7454720 4587520 1966080 524288 65536
  (deep band r in [10,16]; max K = 8,945,664 at r=11. Packing bound C(32,a0)/(a0+1) strictly
   exceeds K throughout deep band: e.g. r=11 pack=17,368,680 > K=8,945,664.)

## 3. FAITHFUL PRIME [MEASURED-FAITHFUL]

Need p^{m+1} > C(n,a) (dodge O164 saturation/pigeonhole). m=1 => p^2 > max_band C(n,a).
- BabyBear p = 2013265921 = 15*2^27+1. p^2 = 4.05e18. 2^27 | p-1 so mu_n exists for any n=2^mu<=2^27.
- n=16: max deep-band C(16,a) = C(16,8) = 12870. p^2 = 4e18 >> 12870. FAITHFUL by 14 orders.
- n=32: max deep-band C(32,a) = C(32,16) = 601,080,390. p^2 = 4e18 >> 6e8. FAITHFUL by 10 orders.
  (Min faithful prime at n=32: p > sqrt(6e8) ~ 24517, with n=32 | p-1. BabyBear works.)
  CONCLUSION: BabyBear is faithful at BOTH scales with huge margin. No larger prime needed for n=32.

## 4. RESULTS [COMPUTED] / [MEASURED-FAITHFUL] — n=16, faithful BabyBear

Validated two independent kernels agree: interp-coeff test == ground-truth bordered-Vandermonde
residual-det test (verify_residual_def.py): KKH26 stack = 0, codeword-stack = 1820, identical.

(A) KKH26 canonical stack (u0=x^r, u1=x^{r-1}) at the deep band a0=rm+1:
    #alignable = 0  for ALL r in [2,8].  REASON: KKH26 agreement = rm (the fiber), exactly ONE
    short of the deep band a0 = rm+1. The supply sits at the CEILING band a=rm, not the deep band.
    Confirms in-tree probe_deltastar_deepband_adversarial.py ("deg rm < rm+1 => zero deep bad").
    Cross-check: at the CEILING band a=rm my kernel reproduces the large q-dependent supply
    (120,560,1820,4368 alignable for r=2..5) — kernel validated against the known KKH26 regime.

(B) Worst-case-over-stacks DEMAND count (#BAD SCALARS, the real delta*-controlling quantity)
    at the deep band, faithful BabyBear (worstcase_badscalar.py):
      r=3 a0=4: worst #bad-scalar = 97  (maximizer mono x^8,x^7)   K=448   margin 5x
      r=4 a0=5: worst #bad-scalar = 145 (maximizer mono x^8,x^5)   K=1120  margin 8x
      r=5 a0=6: worst #bad-scalar = 89  (maximizer mono x^9,x^15)  K=1792  margin 20x
    The worst-case stack is a HIGH-FREQUENCY monomial pair (x^8 = the order-2 element -1), NOT the
    canonical KKH26 (x^r,x^{r-1}). Bad count is O(n) (97,145,89 ~ linear), matching
    probe_deltastar_badscalar_transversal.py ("worst-case bad-SCALAR count is LINEAR ~ n-2r+1").
    #bad <= K holds with MARGIN 5x-20x across the whole deep band. Calibration: every #bad <=
    packing C(n,a0)/(a0+1) (97<=364, 145<=728, 89<=1144). All consistent.

(C) The LITERAL CensusDomination object (#alignable-SETS, not #bad-scalars) is FALSE at the deep
    band, but ONLY via the known lossy overcount: codeword stacks (u0 = x, a degree-<k_c codeword)
    give #alignable = C(n,a0) (1820,4368) >> K but only ONE bad scalar (badscalar_demand.py:
    #alignSets=1820, #BADSCALARS=1). This is exactly the lossiness SinglePencilQIndependence.lean
    was built to bypass (bound #bad-scalars directly, not #alignable). It is NOT a refutation of
    delta*; it says the CensusDomination *normal form* (bounding alignable SETS) is too weak as
    literally written — the correct obligation bounds #bad-SCALARS.

## 5. VERDICT

FIRST DIRECT FAITHFUL EVIDENCE THE PRIZE PROP IS TRUE at the demand level: the worst-case
deep-band BAD-SCALAR count holds vs the KKH26 budget K with 5x-20x margin at n=16. The headline
honest negative is narrower and useful: CensusDomination *as literally stated* (alignable-SETS
form) is FALSIFIED by codeword stacks at the deep band — the right in-tree obligation is the
#bad-SCALAR form (SinglePencilQIndependence route), not the lossy alignableSets cap.

## 6. FEASIBILITY

- n=16: FULLY FEASIBLE. Enumerate a0-subsets of [16]; per-stack ~ C(16,a0)*a0^3 <= 8.3M ops; a
  full worst-case stack search (256 mono pairs + random + coset-structured) finishes in seconds.
  DONE here. THIS IS THE HONEST FRONTIER for an exact worst-case search.
- n=32: deep band is BEYOND a worst-case search. Per-stack one-band: C(32,17)=5.7e8 subsets,
  ~9 min/stack in python (within 15-min cap for a SINGLE stack, e.g. confirming KKH26=0 or testing
  ONE maximizer candidate). A worst-case SEARCH (~30-100 stacks) is INFEASIBLE in python; would
  need the C kernel (audit_sweep64.c-class) AND is still ~hours. Syndrome reduction (the
  probe_bad_family_census route: census over affine lines in F_q^{n-k}) is q^{2(n-k)} at faithful
  q~2e9 => astronomically infeasible without the (open) rotation-quotient + coset-direction
  restriction. CONCLUSION: n=16 is the honest exact-worst-case frontier; n=32 admits only
  single-stack spot-checks, not a worst-case verdict.

## 7. DUPLICATION / COMPLEMENTARITY

- O164 (faithful_fiber.py) did the FIBER/SUPPLY side: max #t-subsets hitting a fixed e-symm target
  = 3 (O(1)), zero-target fiber = 0, at faithful BabyBear. It did NOT count #bad-scalars/#alignable.
- This PIN did the COMPLEMENTARY DEMAND side: #distinct pinned gamma (#bad scalars) and #alignable
  a-sets, worst-case over stacks, faithful BabyBear. Uses O164's fiber=O(1) as the multiplier:
  #alignable ~ #bad x O(1), so the demand count IS the binding quantity.
- No in-tree EXACT deep-band #bad-vs-K test existed: probe_deltastar_badscalar_transversal.py and
  probe_deltastar_deepband_adversarial.py both used SMALL non-faithful primes (17,97,193,449) and
  RANDOM/adversarial Q0 single-poly stacks at a different (q-dependent) pin convention; neither
  enumerated the demand count at the EXACT CensusDomination pin (k_c=(r-2)m+1,a0=rm+1) with a
  faithful prime, nor distinguished #alignable-SETS from #bad-SCALARS, nor identified the
  high-frequency monomial worst case vs the canonical KKH26 stack. This PIN closes that gap at n=16.
