# CONJ.md — ConjectureBound: general-r deep-band #bad-scalar form/bound (#389)

Worktree: /home/nubs/Git/ArkLib-232 (origin/main, synced 2026-06-13). Opus 4.8.
Pin: DEEP band, deficit a0-k_c=2, m=1 rate family, k_c=r-1, a0=r+1, n=2^mu (m=1).
All counts exact-integer via residual-determinant ground-truth kernel cd_demand.c over faithful
BabyBear p=2013265921 (p^2 >> C(n,a0)). taskset -c5 nice -19 ionice -c3, one heavy at a time, <15min.
Kernel REUSED: /tmp/genr/cd_demand <- scripts/probes/genlaw/o165_census_demand/cd_demand.c. NO git/lake.

================================================================================
## 0. CALIBRATION ANCHOR (reproduced digit-for-digit this pass — anti-fabrication check)

  n=16 worst-over-monomial #bad r=3..8 = 97,145,89,113,225,104   [MATCHES O171/O172 EXACTLY]
  maximizers (e,f) = (8,7),(8,5),(9,15),(8,10),(10,15),(9,11)    [MATCH]
  n=32 r=3 = 897 (full 992-mono sweep, =n*C(n/4,2)+1)            [MATCHES O172]
  n=32 r=5 = 1441 at (x^17,x^31)=(x^{n/2+1},x^{n-1})             [MATCHES prior sweep]
  n=32 r=4 = 3105 at (x^16,x^9)/(x^16,x^25) [e=n/2 row]  -- NEW THIS PASS (full e=n/2 row + corner
            sweep; supersedes CF.md's (x^8,x^5)=865 single-stack, which was NOT the maximizer).

  EXACT (n,r): #bad / K=2^r*C(n/2,r) / margin / ratio #bad/K / maximizer:
    16 3   97    448   4.62x  0.2165  (x^8,x^7)
    16 4  145   1120   7.72x  0.1295  (x^8,x^5)
    16 5   89   1792  20.13x  0.0497  (x^9,x^15)
    16 6  113   1792  15.86x  0.0631  (x^8,x^10)
    16 7  225   1024   4.55x  0.2197  (x^10,x^15)
    16 8  104    256   2.46x  0.4062  (x^9,x^11)   <-- BINDING (smallest K, largest ratio)
    32 3  897   4480   4.99x  0.2002  (x^16,x^15)
    32 4 3105  29120   9.38x  0.1066  (x^16,x^9)
    32 5 1441 139776  97.00x  0.0103  (x^17,x^31)

================================================================================
## 1. THE CONJECTURE / BOUND (stated exactly, CLOSED — no residual)

Two-part deliverable. Part A is PROVEN (r=3). Part B is the honest general-r statement.

### PART A  [PROVEN, all n, r=3]  — the only band with a clean exact form
> #bad(n, r=3) = n*C(n/4, 2) + 1 = n^2(n-4)/32 + 1,  and  #bad(n,3) <= K = 8*C(n/2,3) for ALL n,
> via the exact polynomial identity  K - #bad = (h-2)*h*(13h-16)/12 - 1 > 0  (h=n/2, n>=8).
Reproduces 97 (n16), 897 (n32), 7681 (n64); identity verified n=16..128. Asymptotic margin -> 16/3.
[Derivation: order-2 parity split -> 2 quadratics -> antipodal pair-product x_a x_b + x_c x_d = 0 ->
 gamma=-e1(S); injectivity = A4 PairSumRigidityModP (PROVEN, threshold 2^n). O172.]

### PART B  [CONJECTURE-CALIBRATED, general r>=4]  — the demand bound, as a CLEAN <=K bound
> CONJECTURE (DeepBandHalfBudget):  for the deep band (deficit 2, m=1) at every n and 2<=r<=n/2,
>     #bad-scalar(n,r)  <=  K/2  =  2^{r-1} * C(n/2, r).
Equivalently #bad <= K with a guaranteed factor-2 slack. HOLDS at ALL 9 kernel-verified points
(worst ratio 0.4062 at the binding band n=16 r=8); K/4 and K/3 both FAIL there (104 > 256/4=64).
This is the cleanest provable-target bound consistent with the exact data; it implies the prize
obligation #bad <= K with room to spare.

### WHY NOT A CLEANER EXACT FORM (the honest negative — REFUTED candidates)
There is NO clean general-r EXACT closed form for the worst-over-line #bad. CALIBRATED REFUTATIONS:
 - naive r3-generalization n*C(n/4,r-1)+1: 65,17,1,1 vs actual 145,89,113,225. FAILS.
 - 2^{r-1}*C(n/2,r-1): 112,448,... vs 97,145. FAILS (it is K/2 of the band below; an over-count).
 - any single per-divisor line form: REFUTED (Sec 2).
 - n-scaling has no clean exponent: r=3 16->32 ratio 9.25; r=4 ratio 21.41; r=5 ratio 16.19.
   (n^2 would be 4.0.) Non-monotone in r AND non-power-law in n => no monomial closed form exists.

================================================================================
## 2. WHY NO EXACT FORM — the structural obstruction (CONFIRMED + sharpened)

The worst line is r-dependent with NO clean divisor selector. Two distinct regimes:

  ORDER-2 LINE (e=n/2, g^{n/2}=-1) wins at r=3,4,6 (the "even-resonant" r):
    n=16 e=n/2 row-max per r = 97,145,25,113,144,48  (r=3..8).  Global = 97,145,89,113,225,104.
    => order-2 line IS the global max at r=3,4,6 only; DEGENERATES (25,144,48 < global) at r=5,7,8.
  FULL-ORDER / mixed lines win at r=5,7,8:
    r=5 max (9,15): ord(g^e)=16=n, ord(g^{e-f})=8;  r=7 (10,15): ord 8, ord(g^{e-f})=16;
    r=8 (9,11): ord 16, ord(g^{e-f})=8.  Leading-char orders across r=3..8 = {2,2,16,2,8,16} —
    NOT monotone, NOT 2^{-floor(log2 r)}; the "x^{n/4} at r=4" hypothesis is FALSE (r=4 leading
    term is x^{n/2}=order-2). [Confirms StructureGate; divisorFamily REFUTED.]

  GAMMA-MULTIPLICITY changes shape per r (structure_probe, exact):
    r=3 (8,7): {1:96, gamma=0 owns 140}      -- near-injective + big gamma=0 sink
    r=4 (8,5): {1:128, 2:16, gamma=0:112}
    r=5 (9,15):{1:16, 2:64, 32:8, gamma=0:56}
    r=7 (10,15):{1:192, 2:32, gamma=0:10}
    r=8 (9,11):{2:96, 10:8, NO gamma=0}      -- qualitatively different (every gamma doubled)
  #contrib_sets is stable (~236-456 @ n=16) but its partition into distinct gamma is r-specific.
  Since gamma = -e1(S) (witness_pin_eq_neg_sum, all r), #bad = #{distinct e1 over alignable a0-sets}.
  The cardinality of this e1-level-set, OFF the a=4 slice (where it = (2^{m-1}-1)^2, A4CensusValue),
  is the OPEN analytic core — exactly the object ExcessCensusLaw / GeneralGapCensusLaw name as the
  "slice-census cardinality theory". No clean form exists there; this is the obstruction.

  ALIGNABLE-SETS is NOT bounded by K: wide search n=16 r=7,r=8 gives #align up to 11440-12870 >> K.
  Only the #bad-SCALAR collapse (gamma=-e1, many sets -> one scalar) brings the count under K. This
  is WHY the obligation is the #bad-scalar form, not the alignable-set form (literal CensusDomination
  is FALSE — established; reconfirmed by wide search this pass).

================================================================================
## 3. PROOF STATUS (tagged honestly)

[PROVEN, all n]  Part A: r=3 exact form + #bad<=K (polynomial identity). Rests on landed
  PairSumRigidityModP. The remaining step to a formal Lean theorem is wiring the r=3 collinearity
  reduction to that lemma (tractable, same shape as A4CensusValue) — NOT yet a landed .lean theorem.
[PROVEN, all n] a=4 slice deep value (2^{m-1}-1)^2 (A4CensusValue, in-tree).
[COMPUTED, exact] all 9 worst-case data points (kernel, faithful BabyBear); wide search (mono+random
  +structured) confirms the monomial line dominates for #bad at the binding bands (n=16 r=7,8).
[CONJECTURE-CALIBRATED, UNPROVEN] Part B: #bad <= K/2 for all (n,r). Calibrated against all 9 points
  (margin >= 2.46x; binding n=16 r=8 at 0.406*K). NOT proven for general r.
[REFUTED] clean exact general-r closed form (all candidates fail calibration; no power-law n-scaling).
[REFUTED] clean per-divisor maximizer-line rule (orders {2,2,16,2,8,16}, resonance not divisor law).

### EXACT PROOF OBLIGATION for Part B (#bad <= K/2)
Two routes, both reduce to the same e1-level-set core but with a factor-2 slack that may be reachable:
 (R1) Per-line bound: for EACH monomial line (x^e,x^f), #{distinct e1(S) : S alignable a0-set} <= K/2,
      then max over lines. Proven only at the order-2/r=3 resonance (Part A). Open for full-order lines.
 (R2) Global counting bound: #bad <= #contrib_sets - (gamma=0 absorption) and #contrib_sets <= ???.
      Measured #contrib_sets ~ 236-456 @ n=16 (all << K), but no proven upper bound on #contrib_sets
      that beats the packing bound (which itself can exceed K, Sec 2). This route is NOT closed.
 The honest obligation: bound the joint (e1,e2) two-symmetric level-set cardinality for a general-r
 alignable family by 2^{r-1}*C(n/2,r-1) -- the SAME analytic core ExcessCensusLaw names, now with an
 explicit factor-2 target and the binding instance pinned (n=16 r=8). r=3 and the a=4 slice are the
 only sub-cases closed.

================================================================================
## 4. RANK (honest /10)

novelty 6: the K/2-budget framing + the binding-band identification (r=n/2, smallest K) + the
  new n=32 r=4=3105 maximizer (corrects CF.md) are new; but the core object and the NO-clean-form
  verdict were already reached by StructureGate. Not a new mechanism.
insight 7: sharpens WHY no form (order-2 resonance at r=3,4,6 vs full-order at r=5,7,8; the e1-level-
  set = ExcessCensusLaw's named core; gamma-multiplicity fingerprints) and isolates the exact factor-2
  proof obligation with the binding instance. Genuine structural map, not just data.
prize-proximity 7: directly the prize's CensusDomination demand obligation, deep band, faithful q,
  production-relevant (CF.md q-threshold: production q realizes the char-0 worst case for n<=256/512).
  #bad<=K (the prize bound) HOLDS at every computed point with >=2.46x margin. But UNPROVEN for r>=4.
feasibility 4: an exact general-r form is infeasible (refuted — no clean form exists). The K/2 BOUND
  is the feasible target but its proof is the SAME open analytic core (e1-level-set cardinality);
  only r=3 + a=4 slice are closed. Below the 9/10 bar.

NOT 9+/10 on novelty/feasibility => NOT shipped as a positive exact-form conjecture. The deliverable
is: (i) Part A r=3 PROVEN (carried), (ii) Part B #bad<=K/2 as a CONJECTURE-CALIBRATED-UNPROVEN bound
with the exact obligation + binding instance, (iii) a calibrated REFUTATION of every clean exact form
and the per-divisor rule. This is a valid negative+partial deliverable per the anti-fabrication
contract: no fabricated form; the bound is the honest cleanest statement the data supports.

================================================================================
## 5. ARTIFACTS (rescued to scripts/probes/genlaw/o165_census_demand/ in report)
- CONJ.md (this file)
- calibrate.py (the calibration harness: reproduces all 9 points, tests forms+bounds)
- n=32 r=4 e=n/2 full row + corner sweep -> maximizer (x^16,x^9)=3105 [NEW; raw in report Sec 0]
- reused kernel: scripts/probes/genlaw/o165_census_demand/cd_demand.c (built /tmp/genr/cd_demand)
- reused probe: scripts/probes/genlaw/o165_census_demand/qthreshold/structure_probe.py (gamma-mult)
- prior: STRUCT-genr-divisor.md (divisor REFUTED), CF.md (r=3 form, q-threshold), r5_n32_sweep.txt
