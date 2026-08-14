# STRUCT.md — StructureGate: divisor-dependent worst-case family + per-line deep-band #bad structure (#389)

Worktree: /home/nubs/Git/ArkLib-232 (origin/main, synced 2026-06-13). Opus 4.8.
Pin: deep band, deficit a0-k_c=2, m=1 rate family, k_c=(r-2)+1=r-1, a0=r+1.
All counts exact-integer (residual-det kernel cd_demand.c over faithful BabyBear p=2013265921, p^2>>C(n,a0)).
taskset -c5 nice -19 ionice -c3, one heavy at a time, <15min cap. NO git/lake.
Kernel reused+built: /tmp/genr/cd_demand  <-  scripts/probes/genlaw/o165_census_demand/cd_demand.c.

CALIBRATION ANCHOR (reproduced digit-for-digit this pass, the anti-fabrication check):
  n=16 deep-band worst-monomial #bad r=3..8 = 97,145,89,113,225,104   [MATCHES O171/O172 exactly]
  maximizer monomials = (x^8,x^7),(x^8,x^5),(x^9,x^15),(x^8,x^10),(x^10,x^15),(x^9,x^11) [MATCH CF.md]
  r=3 closed form n*C(n/4,2)+1: n=16->97, n=32->897 (order-2 adj line x^16,x^15 confirmed). MATCH.

================================================================================
## 1. GATE — alreadyDone = FALSE (confirmed; no general-r deep-band deficit-2 closed form / <=K bound)

Read in full: ExcessCensusLaw.lean, GeneralGapCensusLaw.lean, the e249b9cf3 monomial-extremality
theorem markdown, GATE-qthreshold.md, CF.md, DISPROOF_LOG scan, and the latest #389 commits
(c7774f7ca K1 counting core, 6c0b630a4 Fisher bound, 9334408a3 symmetric-function reduction,
A4CensusValue, DeepBandSpectrumUpper).

WHAT EXISTS (do NOT re-derive):
- ExcessCensusLaw / GeneralGapCensusLaw: the EXACT iff-CHARACTERIZATION of a bad scalar as a
  punctured-band witness (a-subset T whose V_T * monic-cofactor has zero coeffs across the band and
  lambda at the punctured slot). These are LAWS (membership iffs), NOT counts. They reduce #bad to a
  cardinality of an explicit polynomial family; the docstring itself names the "slice-census
  cardinality theory (the analytic core)" as the OPEN follow-up. No count, no closed form, no <=K.
- e249b9cf3 monomial extremality THEOREM: bad scalars of the MONOMIAL LINE X^{rm}+gamma*X^{(r-1)m}
  = EXACTLY C(s,r), PROVEN (Lam-Leung 2-power induction). This is the CEILING band (agreement a=rm,
  deficit a-k_c=1), NOT the deep band. Confirmed by GATE calibration: ceiling closed form gives
  1233,2256,3025,... vs deep worst 97,145,89,... (~30x off). Different object.
- A4CensusValue: |a4Census|=(2^{m-1}-1)^2 -- the ONLY landed DEEP-band (deficit-2) exact value, but
  only the a=4 (i.e. fixed two-symmetric e1 AND e2) slice, q-threshold 2^n. Not general r.
- r=3 deep-band closed form #bad=n*C(n/4,2)+1<=K all n (O172): COMPUTED-FIT 3pts + combinatorial
  derivation; NOT yet a landed .lean theorem; only r=3.
- Latest #389 (K1 walk bound, Fisher bound, symmetric-function reduction) target the NON-correlated
  incidence / energy E_r(mu_n) / Johnson-bypass -- a DIFFERENT face (the supply/B(mu_n) analytic
  core), not the per-divisor deep-band deficit-2 #bad count.

EXACT REMAINING GAP: a general-r (r>=4) closed form OR <=K bound for the deep-band (deficit-2,
a0=rm+1) worst-case #bad-SCALAR count. Only r=3 (all n) and a=4-slice are landed. OPEN.

================================================================================
## 2. DIVISOR-DEPENDENT WORST-CASE FAMILY -- REFUTED as a clean rule [COMPUTED, exact]

The task's working hypothesis (r=3 -> x^{n/2}, r=4 -> x^{n/4}, pattern d=n/2^floor(log2 r))
is REFUTED by exact recomputation of the maximizers and their character structure.

n=16 maximizer monomials (e,f) and the multiplicative orders of g^e, g^f, g^{e-f}, g^{e+f}:

  r  k_c a0  (e,f)    #bad | ord(g^e) ord(g^f) ord(g^{e-f}) ord(g^{e+f})
  3   2  4   (8,7)     97  |    2       16       16          16
  4   3  5   (8,5)    145  |    2       16       16          16
  5   4  6   (9,15)    89  |   16       16        8           2
  6   5  7   (8,10)   113  |    2        8        8           8
  7   6  8   (10,15)  225  |    8       16       16          16
  8   7  9   (9,11)   104  |   16       16        8           4

KEY CORRECTION to CF.md: the r=4 maximizer (x^8,x^5) has LEADING term x^8 = x^{n/2} = the ORDER-2
element (g^8 has order 2 at n=16), NOT x^{n/4}=order-4. The pure order-4 line (x^4,x^3) gives #bad=0;
(x^8,x^11)=1. So "x^{n/4} wins at r=4" is INACCURATE -- the leading character is still order-2 at r=4;
what changes is the SECOND exponent / GAP (r=3 uses gap t=n/2-1=7 [adjacent]; r=4 uses t=5=n/2-3
[non-adjacent], = (x^8,x^13) by symmetry, also 145).

The leading-exponent character order across the maximizers is {2,2,16,2,8,16} -- NOT monotone, NOT
2^{-floor(log2 r)}, no clean divisor law. There is NO single order-d character line that is the
maximizer for all r. The maximizer family is GENUINELY r-dependent with no clean closed divisor rule
(consistent with CF.md's "non-monotone 97,145,89,113,225,104" but sharper: the divisor labeling
itself is not clean).

THE RESONANCE PHENOMENON (the real structure): each character line is the maximizer only at ONE
"resonant" r, and DEGENERATES (#bad collapses to 1) elsewhere. Direct measurement of the order-2
ADJACENT line (x^{n/2}, x^{n/2-1}) across r:
  n=16 (x^8,x^7):  r=3 -> 97, r=4 -> 1, r=5 -> 1, r=6 -> 1, r=7 -> 49
  n=32 (x^16,x^15): r=3 -> 897 (=n*C(n/4,2)+1), r=4 -> 1
The order-2 line resonates at r=3 (k_c=2), gives the proven n*C(n/4,2)+1, then degenerates. r=3's
clean closed form exists precisely BECAUSE k_c=r-1=2 matches the order-2 (2-fold parity) split into
exactly 2 quadratics with the 2+2 antipodal structure. The maximizer at general r is a DIFFERENT
character line resonant at that r, with NO uniform divisor selector.

================================================================================
## 3. PER-LINE STRUCTURE -- the r=3 derivation does NOT cleanly generalize [derivation + COMPUTED]

The r=3 order-2 mechanism (r3_derivation.py / r3_combinatorial.py, reproduced):
  k_c=2 affine fit  ->  W_i=(-1)^i(1+gamma/x_i) collinear  ->  multiply by x_i, split by PARITY
  (the order-2 character index mod 2) into 2 quadratics  ->  Vieta forces the antipodal pair-product
  x_a x_b + x_c x_d = 0  <=>  (a+b)-(c+d) = n/2 (mod n)  ->  bad gamma = -e1(S), count n*C(n/4,2),
  +1 for the degenerate gamma=0. Injectivity = A4's pair_sum_rigidity (PROVEN, threshold 2^n).

WHY IT DOES NOT GENERALIZE CLEANLY:
 (a) The order-2 split works only because the parity (mod-2) character makes each of the 2 quadratics
     degree EXACTLY 2 = a0/2 (2 even + 2 odd nodes at a0=4). For an order-d line at deficit-2, the
     d-ary split (index mod d) gives d polynomials whose degrees must sum to a0 and individually
     bound the per-residue node count; the joint Vieta condition is no longer a single clean
     pair-product but a system of d coupled symmetric-function constraints (the joint e1,e2 level set).
 (b) The bad gamma = -e1(S) Vieta pin (witness_pin_eq_neg_sum) HOLDS at every r (in-tree), so #bad =
     #{distinct -e1 over alignable a0-sets} ALWAYS. But the alignable-set condition for the worst
     line at general r is the JOINT (e1,e2) two-symmetric level set (GATE Sec 3), whose cardinality is
     the open analytic core (the SAME object ExcessCensusLaw flags). Only the a=4 slice
     (2^{m-1}-1)^2 has a closed level-set count; general a does not.
 (c) Empirically the naive generalization n*C(n/4,r-1)+1 FAILS (gives 65,17,1,... << 145,89,113;
     CF.md). Each resonant line's count is a DIFFERENT character/Gauss-sum sum-class with no shared
     closed form. The per-line counts are NOT a single closed-form family.

HONEST PER-LINE VERDICT: each character line HAS a deep-band count that is a fixed char-0 algebraic
integer (q-independent above threshold, GATE Sec 4) and IS character/Gauss-sum structured (the a=4
slice and r=3 prove it). But (i) which line is the maximizer has no clean divisor rule, and (ii) the
per-line count is closed-form ONLY at the resonant r where k_c matches the character order (r=3
order-2 -> n*C(n/4,2)+1; a=4 -> (2^{m-1}-1)^2). For a general (line, r) pair the count is the joint
(e1,e2) level-set cardinality = the open analytic core. NO clean unified closed form exists.

================================================================================
## 4. n=32 r=5 SPOT-CHECK [COMPUTED, exact] -- maximizer divisor

Bounded sweep (odd e in 1..31 x f in {31,29,27,25,23,17,15}, ~110 stacks, exact residual-det,
under cap) plus targeted high-freq probes. MAXIMIZER:

  n=32 r=5 deep band a0=6, k_c=4:  WORST #bad = 1441  at (x^17, x^31)  [<=K=139776, margin 97x]
    (near-symmetric twin (x^31,x^17) = 1440; next tier (x^15,x^17)=736, (x^17,x^15)=737)

STRUCTURE OF THE r=5 MAXIMIZER (x^17, x^31):
  e=17 = n/2+1,  f=31 = n-1.  ord(g^e)=32 (=n, full order), ord(g^f)=32, ord(g^{e-f})=16=n/2,
  ord(g^{e+f})=2.  This is the (x^{n/2+1}, x^{n-1}) family -- EXACTLY the n=16 r=5 maximizer
  (x^9,x^15)=(x^{n/2+1}, x^{n-1}), #bad=89, RESCALED. Scaling 89 -> 1441 = x16.19 (~ n^2, like r=3,
  but constant differs and 16.19 != 16 exactly -> NOT pure n^2, no clean closed form for this family).

VERDICT ON THE DIVISOR HYPOTHESIS for r=5: the predicted d=n/2^floor(log2 5)=n/4 (order-4 line) is
REFUTED -- the order-4 line (x^8,x^7) gives only 112-align/#bad small; the order-2 line (x^16,x^15)
degenerates to #bad=1 at r=5. The TRUE r=5 maximizer (x^{n/2+1}, x^{n-1}) has FULL-ORDER (n) leading
character, with the relevant "resonant" character living in the gap g^{e-f} of order n/2. So the
maximizer's governing divisor is NOT a small d|n and does NOT follow 2^{-floor(log2 r)}; it is the
near-(-1,-1) high-frequency corner of the (e,f) grid, r-specifically resonant.

================================================================================
## 5. SUMMARY VERDICT (the StructureGate deliverable)

1. GATE: alreadyDone = FALSE. No general-r deep-band deficit-2 #bad-scalar closed form / <=K exists.
   In-tree: the iff-LAWS (Excess/GeneralGap, no counts), the CEILING C(s,r) theorem (e249b9cf3,
   wrong band), the a=4 deep slice (2^{m-1}-1)^2, the r=3 deep form n*C(n/4,2)+1 (only r=3, not
   landed in Lean). The deep deficit-2 general-r count is the OPEN analytic core (same one
   ExcessCensusLaw names).

2. DIVISOR FAMILY: NO clean divisor rule. Maximizer leading-character orders across r=3..8 at n=16
   = {2,2,16,2,8,16} -- not 2^{-floor(log2 r)}, not monotone. The r=4 "x^{n/4}" claim is WRONG (its
   leading term is x^{n/2}=order-2). Each character line RESONATES at one r and degenerates (#bad->1)
   elsewhere. r=5 spot-check at n=32: maximizer (x^{n/2+1}, x^{n-1})=1441, full-order leading char,
   refuting the order-4 prediction.

3. PER-LINE COUNT: closed-form ONLY at the resonant (line, r): order-2 @ r=3 -> n*C(n/4,2)+1;
   a=4 -> (2^{m-1}-1)^2. The r=3 parity-split -> antipodal pair-product -> gamma=-e1 derivation does
   NOT generalize: the d-ary split gives d coupled symmetric constraints (joint e1,e2 level set),
   whose cardinality is the open core. naive n*C(n/4,r-1)+1 FAILS. No unified per-line closed form.

HONEST DELIVERABLE: a REFUTATION of the clean-divisor-family conjecture + the per-resonance
structural map. This is a valid negative result per the anti-fabrication contract: there is NO
clean general-r deep-band closed form; the obstruction is (a) no divisor selector for the maximizer
and (b) the joint (e1,e2) level-set count off the two landed slices. Conjecture rank: novelty 6,
insight 7, prize-proximity 6, feasibility (of a clean form) 3 -- BELOW the 9/10 ship bar, correctly
NOT shipped as a positive conjecture. The bound #bad <= K HOLDS at every computed point with margin
>=2.46x (n=16 all r) / 5x (n=32 r=3) / 97x (n=32 r=5), but remains MEASURED, not proven, for r>=4.

================================================================================
## 6. ARTIFACTS (rescue to scripts/probes/genlaw/o165_census_demand/ in report)
- /tmp/genr/STRUCT.md (this file)
- /tmp/genr/cd_demand  (built from scripts/probes/genlaw/o165_census_demand/cd_demand.c, REUSED kernel)
- raw r=5 n=32 sweep #bad>=400: in this file Sec 4; maximizer (x^17,x^31)=1441.
- calibration reproduced: n=16 worst 97,145,89,113,225,104 (anti-fabrication anchor).
- character-order table (Sec 2) reproducible via the inline python in the pass log.
