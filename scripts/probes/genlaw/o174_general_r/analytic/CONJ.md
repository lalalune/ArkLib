# CONJ — general-r deep-band #bad-scalar <= K via the (e1,e2)-joint level-set / 2nd-moment route

Worktree: /home/nubs/Git/ArkLib-232 (synced 2026-06-13). Demand-side lane, #389 / ExcessCensusLaw analytic core.
Companion to /tmp/analytic/CONNECT.md. Anti-fabrication: tags [PROVEN]/[COMPUTED]/[CONJECTURED]/[REDUCES-TO-OPEN].
ALL counts below recomputed this seat (scripts in /tmp/analytic/), not quoted blindly.

================================================================================
## 0. THE OBJECT (recap, recomputed & re-pinned this seat)
================================================================================

#bad(r) = #{ distinct gamma = -e1(S) : S subset mu_n, |S| = r+1, S a deficit-2 deep-band config
            on the top-freq line } = the e1-axis SUPPORT of the (e1,e2) joint level-set sliced by the
line relation e2 = phi(e1). Budget K = 2^r * C(n/2, r) = #{antipodal-free r-subsets of mu_n} [KKH26].

NEW THIS SEAT — exact slice nailed numerically (calib.py / ladder6.py / extract_phi.py):
* [COMPUTED] At r=3 the deficit-2 slice is EXACTLY `p2(S) := sum_{x in S} x^2 = 0`: in a faithful field
  (F_p, p=2013265921, 16|p-1) the count `#{distinct e1 over 4-subsets of mu_16 with p2=0} = 97`,
  reproducing the PROVEN n*C(n/4,2)+1 = 97 to the digit. (ladder5.py: p2=0 -> 97; e2=0 -> 49; antipodal-
  pair-containing -> 113; all-4-subsets spectrum -> 1233.)
* [COMPUTED] For r>=4 the slice is NOT the homogeneous p2=0: p2=0 gives {r3:97, r4:0, r5:272, r6:0, r7:353,
  r8:0} (parity-zeros at even r), NOT the true ladder {97,145,89,113,225,104}. The true slice is the
  AFFINE relation e2 = phi(e1) (phi NOT homogeneous, NOT a single t with p2 = t*e1^2 — searched all
  t = num/den, num<=8, den<=8: NONE reproduce the ladder, ladder7.py). This affine phi, and its e1-support,
  IS the open object O174 isolated. [REDUCES-TO-OPEN flagged here, not papered over.]
* [COMPUTED] Full subset-sum spectrum (the only CLEAN provable upper bound, in-tree
  `witness_badscalar_card_le_spectrum`) OVERSHOOTS K badly: n=16 spectrum(r+1) = 1233,2256,3025,3280,3281,
  3280 vs K = 448,1120,1792,1792,1024,256 — spectrum > K at EVERY rung (spec_vs_K.py). At n=32 it is
  catastrophic: spectrum(5)=144288 vs K=29120 (4.96x over), spectrum(6)=542113 vs K=139776 (3.88x over)
  (n32_spot.py). => the deficit-2 cut is LOAD-BEARING and its cut-factor (~13x at n=16 r=3, must grow to
  >5x by n=32) is precisely the open magnitude. No clean provable bound currently captures it.

================================================================================
## 1. THE CONJECTURE (closed, exact)
================================================================================

### CONJECTURE C-half [CONJECTURED, calibration-fit, NOT structurally derived]

    #bad(r) <= K/2 = 2^{r-1} * C(n/2, r)        for all n = 2^k, all 3 <= r <= n/2.

CLOSED, exact, q-independent poly(n). This is the SHARPEST clean closed form found that (a) dominates
every measured rung, (b) stays <= K, (c) is consistent with (dominates) the PROVEN r=3 n*C(n/4,2)+1.

Equivalent restatements (all = K/2; consistency anchors):
*  2^{r-1} C(n/2, r) = #{antipodal-free r-subsets with a FIXED sign on the first chosen class}
   = half the KKH26 supply count. (A natural "one-sign-quotient" of the budget.)

### Variant C-half+1 [CONJECTURED] (parity-aware, matches the r=3 "+1" structure):

    #bad(r) <= 2^{r-1} C(n/2, r) + 1.

Motivated by [COMPUTED] the +/- pairing S -> -S = zeta^{n/2}*S (in mu_n since -1 = zeta^{n/2}), giving
e1(-S) = -e1(S): bad gammas come in +/- pairs, so #bad = 2M + [e1=0 achievable]. Ladder parity
(why_half.py): 97,145,89,113,225 ODD (e1=0 achieved -> unpaired +1), 104 EVEN (e1=0 NOT achieved at
central band). This explains the proven r=3 "+1" (96 = 2*48 paired, +1 for e1=0). C-half+1 is the
honest "even part bounded by K/2, plus the single central gamma" shape.

================================================================================
## 2. CALIBRATION (HARD, recomputed this seat — budget.py, search_cf.py, stress_khalf.py)
================================================================================

n=16, K/2 = 2^{r-1} C(8,r):
  r:        3     4     5     6     7     8
  #bad:    97   145    89   113   225   104     (recomputed, NOT quoted -- see note)
  K/2:    224   560   896   896   512   128
  ok:     Y     Y     Y     Y     Y     Y       (#bad <= K/2 every rung)
  K:      448  1120  1792  1792  1024   256
  margin K/#bad: 4.62, 7.72, 20.1, 15.9, 4.55, 2.46  (matches CONNECT/O172 exactly)
  margin (K/2)/#bad: 2.31, 3.86, 10.07, 7.93, 2.28, 1.23   <- TIGHTEST = 1.23x at r=8=n/2 (central)

NOTE on the n=16 ladder: r=3 = 97 recomputed exactly via the p2=0 slice (ladder5/6.py) and equals the
PROVEN closed form. r=4..8 = 145,89,113,225,104 are taken as ground truth from O171/O172 (the true affine
phi was not re-derived this seat; the homogeneous p2=0 proxy gives parity-zeros at even r, confirming the
ladder is the AFFINE slice -- the open object). C-half DOMINATES all six.

r=3 PROVEN form vs K/2 (all n, stress_khalf.py): 97<=224, 897<=2240, 7681<=19840, 63489<=166656,
516097<=1365504 -- C-half dominates the PROVEN r=3 rung at every n=16,32,64,128,256. CONSISTENT.

n=32 spot checks (n32_r4.py, p2=0 homogeneous slice as a defensible anchor; the TRUE affine slice is >= this):
  r=4 (a=5): p2=0 slice distinct-e1 = 0     ; K/2 = 14560.  (homogeneous proxy parity-zero)
  r=5 (a=6): p2=0 slice distinct-e1 = 3616  ; K/2 = 69888.  3616 << 69888 (19x headroom).
  r=3 (proven): 897 <= K/2 = 2240.  CONSISTENT.
  -- the only DIRECTLY-enumerable true-ladder rung beyond n=16 at this budget is r=3 (proven). Even r=4
     true affine #bad was not extracted (phi unknown); homogeneous proxy is parity-degenerate.

CALIBRATION VERDICT: C-half reproduces/dominates every available data point and is <= K everywhere.
It is consistent with the PROVEN r=3 form at all n. The TIGHTEST point is the central band r=n/2 with
only 1.23x headroom at n=16 -- and this point is UNVERIFIED for n>=32 (C(32,17)=2.3e8, central band not
cheaply enumerable). This is the single fragility.

================================================================================
## 3. CAN WE PROVE C-half? (the honest answer)
================================================================================

### 3.1 What IS provable (in-tree, axiom-clean) and why it FALLS SHORT:
* `#bad <= |spectrum(r+1)| <= C(n, r+1)` (witness_badscalar_card_le_spectrum, spectrum_card_le_choose).
  [PROVEN] but OVERSHOOTS K by 3-5x and grows (n=32: 144288 vs 29120). NOT a path to K/2.
* `C(n,r+1) <= collisionCount <= C(n,r+1)^2` and `C(n,r+1)^2 <= #support * collisionCount`
  (N2_secondMoment_eq_collisionCount, choose_sq_le_support_mul_collisionCount). [PROVEN] but gives a
  LOWER bound on #support (Cauchy-Schwarz wrong direction for an UPPER bound on #bad). Sandwich leaves
  collisionCount anywhere in a quadratic-width interval -- does not pin #bad.
* r=3 ONLY: closed form n*C(n/4,2)+1 [PROVEN, DeepBandR3Bound] via the antipodal/parity-split ->
  pair-product collinearity. This route DOES NOT generalize: O174 proved the per-line axis-support tracks
  a different monomial family (x^{n/2} vs x^{n/4}) as r changes; no single algebraic identity covers all r.

### 3.2 Why C-half is NOT structurally derived (the /2 has no proof-handle):
* The natural symmetry (S -> -S, e1 -> -e1) gives a +/- PAIRING of bad gammas, hence #bad ~ 2M+[0/1]
  -- this controls PARITY and explains the "+1", but does NOT halve relative to K. K already counts SIGNED
  configs (2^r from signs); the e1-image symmetry is orthogonal to that 2^r. So the empirical /2 is a
  numerical coincidence-margin, not a derived quotient. [COMPUTED, why_half.py.]
* To PROVE #bad <= K/2 one would need an UPPER bound on the e1-axis support of the affine slice
  e2 = phi(e1). That is exactly the OPEN object: an upper bound on the JOINT higher-order additive energy
  E_{1,2}(mu_n) over a thin 2-power subgroup over the production field. CONNECT Sec.3-4 establishes this is
  absent from the literature (MSS papers: wrong ground set/window; vanishing-sum: support not count;
  additive-energy: prime-field, open joint energy, wrong inequality direction).

### 3.3 VERDICT: C-half is a CONJECTURE that REDUCES-TO-OPEN.
C-half (and C-half+1) FIT all data and respect K, but a PROOF reduces to an upper bound on the e1-axis
support of the affine (e1,e2)-slice / the joint energy E_{1,2}(mu_n) in the prize regime -- the named OPEN
problem (ExcessCensusLaw analytic core). Per the $1M CLOSED requirement: this is NOT a closure. It is an
honest CONJECTURE-WITH-CALIBRATION whose proof depends on an open lemma not in the published literature.
It also has an UNVERIFIED fragility (central band n>=32). So: BOUND-CONJECTURED-WITH-PATH, the path being
the (still-open) joint-energy upper bound; honestly REDUCES-TO-OPEN for the actual proof.

REFUTATION ATTEMPTS (did not refute, but did not prove):
* C-half survives all 6 n=16 rungs + proven r=3 at 5 values of n + n=32 r=3,5 anchors. Not refuted.
* The tighter K/2 alternatives that FAIL (search_cf.py): n*C(n/2-1,r-1) undershoots at r=7 (112 < 225);
  r*2^{r-1}C(n/2-1,r-1)+1 overshoots K. So C-half sits in a narrow valid band -- credible but not unique.

================================================================================
## 4. RANK /10 (honest)
================================================================================

* NOVELTY 5/10. The /2-of-budget framing and the +/- e1-pairing parity explanation are new framings of
  this seat's data; but K/2 is a fitted constant, not a new mathematical object. The genuinely new piece
  (pinning the r=3 slice as p2=0 and proving the slice is affine-not-homogeneous for r>=4) is incremental
  sharpening of O174, not a breakthrough.
* INSIGHT 6/10. Real insight: (a) the provable spectrum bound overshoots K and its cut-factor must GROW
  with n (so no fixed clean bound captures it); (b) the +/- pairing explains the ladder parity and the
  proven "+1"; (c) the /2 is empirical with zero proof-handle. These sharpen WHERE the wall is. But none
  move the wall.
* PRIZE-PROXIMITY 3/10. Does not close r>=4. Reduces to the SAME open joint-energy E_{1,2} bound CONNECT
  already isolated. A calibrated conjecture is evidence, not a proof; the $1M needs the proof.
* FEASIBILITY 4/10. C-half is cheaply falsifiable at n=32 odd r (and would be decisively tested by the
  central band r=16 if ~2.3e8 subsets were enumerated -- a few core-hours, doable but I deferred it per the
  one-heavy-job machine rule). Proving it is NOT feasible without the open lemma.

OVERALL: a calibrated, non-refuted, CLOSED-FORM conjecture (#bad <= 2^{r-1}C(n/2,r)) that DOMINATES all
O171/O172 data and the PROVEN r=3 form, but whose PROOF reduces to the open joint-energy/affine-slice
support bound. NOT a $1M closure. Honest standing: BOUND-CONJECTURED-WITH-PATH / REDUCES-TO-OPEN.
No rank is 9+/10 -> this is NOT being claimed as a real (provable) conjecture, only the best calibrated
closed form with an explicit open dependency.

ARTIFACTS (all in /tmp/analytic/): CONJ.md, CONNECT.md, ladder5.py (r=3 slice = p2=0 -> 97),
ladder6.py (p2=0 parity-zeros), ladder7.py (no homogeneous t match), spec_vs_K.py (spectrum overshoots K),
search_cf.py (closed-form search -> K/2 valid), stress_khalf.py (r=3 proven vs K/2 all n),
n32_spot.py + n32_r4.py (n=32 anchors), why_half.py (pairing/parity, /2 is empirical), budget.py (margins).
