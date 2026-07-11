# The odd-r tail of the marginal layer: purity exclusion (proven), doubling monotonicity (proven), the sharp r^2 law (certified at its divergence points), and the death-cause anatomy of every settled zero stratum

Lane `nubs/issue232-effective-pa` successor work (tracker #334), 2026-06-11;
finalized + adversarially re-audited 2026-06-12 (see SS4 "FINAL session"
rows; corrections this pass: (64,9) downgraded to OPEN — closure logs
empty, random-null artifact lost; SS6.2 OFF-probe bestcost values fixed to
the surviving climb_off_*.txt artifacts).
Inputs: `scripts/probes/n32census/level2/DERIVED-672.md` (the O108 engine),
`scripts/probes/genlaw/RESULTS-GENERAL-LAW.md` + `FORECAST_n64.json` (O130),
`scripts/probes/genlaw/audit/audit_sweep64.c` (criterion ground truth).
All scripts and raw outputs in `/tmp/exclusion/`.

## 0. Executive summary

Question: for which (s, r), s = 2^j, r odd, is N_r(s) = 0, and why? The shape
on record was r_max = 2j - 5 (j >= 4), "pattern-extrapolated, NOT derived".

1. **T1 (Parity-purity, PROVEN, all odd r, all 2-power s).** In every balanced
   configuration the r O-fibers share one parity. Proof: Lam-Leung 2-power
   criterion + Z[zeta] a domain. Corollary: **N_r(s) = 0 for every odd
   r > s/2** - the entire deep tail, every scale, unconditional.
2. **T2 (Budget parity, PROVEN).** h == b (mod 2) always; gate "(b-h) odd" is
   vacuous (die_par = 0 across ~5.6e8 enumerated configs).
3. **T3 (Doubling monotonicity, PROVEN).** N_r(s) > 0 => N_r(2s) > 0.
4. **T4 (s = 32 tail CLOSED).** N_13(32) = N_15(32) = 0 by exhaustive
   pure-only enumeration (T1 makes this complete); with prior+re-verified
   r = 7, 9, 11 sweeps and T1 for r >= 17: **N_r(32) = 0 for ALL odd r >= 7;
   marginal(32) = 2(N_3+N_5) = 1,728,112 is complete** (was r <= 11 only).
5. **The sharp law (CONJECTURED, 26/26 calibration — 13 known-ON +
   13 settled-zero strata, certified at its divergence points):
   N_r(s) > 0 iff r^2 <= s + 1** (equivalently C(r,2) <= b). Explains the
   s = 8 anomaly (9 <= 9, boundary-tight: b = C(3,2) = 3).
   **r_max = 2j-5 is REFUTED: 6 independently verified explicit certificates
   prove N_11(128) > 0** where 2j-5 predicts 0. Predicted r_max:
   8->3, 16->3, 32->5, 64->7, 128->11, 256->15, 512->21 (certified through
   r = 19 at s = 512; the boundary point (512,21) is law-ON but UNCERTIFIED,
   see SS6.2 correction).
6. **Death-cause anatomy (MEASURED: every zero stratum at s = 16, 32;
   nonzero anatomy through s = 64; (64,9) NOT measured — SS6.1).**
   100.000% of mixed-parity configs die at odd-self-balance (= T1).
   100% of pure configs at zero strata die at PER-AXIS CAPACITY
   (max_c |d_c| >= 2, vast majority) or FORCED-FIBER BLOCKED (light-side
   fiber in O). The budget gates h > b, (b-h) odd, (b-h)/2 > v fire on
   exactly ZERO configs in every stratum measured, zero or nonzero.
   Turn-on at fixed r: doubling s doubles the axis count s/2, the same
   T' = C(r,2)+r+1 terms spread, and max|d| <= 1 becomes satisfiable.

## 1. Setup (criterion identical to audit_sweep64.c)

s = 2^j (j >= 3), n = 2s, pattern (b, r), b = (s+1-r)/2, r odd. Config:
O = {o_1 < ... < o_r} in Z_s; lifts a_i = o_i + s m_i, m_1 = 0; B in Z_s \ O,
|B| = b. Balance multiset M = {a_i+a_j : i<j} u {2 o_i} u {2f : f in B} u
{3s/2} in Z_n; feasible iff mult(t) = mult(t+s) for all t (antipodal balance
= Lam-Leung vanishing). N_r(s) = #feasible (O, m, B).
Per-(O,m) gates (= audit engine, re-verified): G1 odd self-balance; per even
axis c in Z_{s/2}: d_c = cnt[2c]-cnt[2c+s]; G2 max|d_c| >= 2; G3 forced
light-side fiber in O; G4 h = sum|d_c| > b; G5 (b-h) odd; G6 (b-h)/2 > v;
else feasible with ways = C(v, (b-h)/2).

## 2. Proven theorems

### T1 Parity purity
**Theorem.** Feasible => all o_i share one parity. Hence N_r(s) = 0 for odd
r > s/2.
*Proof.* Split O = E u D by parity, |E| = p, |D| = q, E^ = {a_i : o_i in E},
D^ = {a_i : o_i in D}. All of {2o_i}, {2f}, {3s/2} are even; product a_i+a_j
has parity o_i+o_j. Antipode t -> t+s preserves parity, so balance restricts
to the odd part M_odd = {a + a' : a in E^, a' in D^} (each mixed pair once).
By the multiset Lam-Leung 2-power criterion
(`LamLeungMultisetAntipodal.multiset_antipodal_iff`), M_odd balanced iff
0 = sum_{E^} sum_{D^} zeta^{a+a'} = U V, U = sum_{E^} zeta^a,
V = sum_{D^} zeta^{a'}. Z[zeta] is a domain => U = 0 or V = 0. If U = 0 its
exponent multiset is antipodally balanced; but E^ elements are pairwise
distinct mod s (distinct fibers), so each antipodal pair {t, t+s} (equal
residue mod s) holds at most one element; balance forces E^ empty. So p = 0
or q = 0. QED.
Falsifier counters: pass_odd_mixed = 0 and feas_mixed = 0 in every run.

### T2 Budget parity
**Theorem.** For every pure (O,m) passing G1-G3: h == b (mod 2).
*Proof.* Pure configs have no odd terms, so every non-B term contributes
exactly one +-1 to exactly one axis: h = sum|d_c| == sum d_c == T' (mod 2),
T' = C(r,2)+r+1. T' - b = ((r+1)^2 - s)/2 = 2((r+1)/2)^2 - 2^{j-1} == 0
(mod 2) since r+1 is even and j >= 2. QED. (die_par = 0 everywhere.)

### T3 Doubling monotonicity
**Theorem.** N_r(s) >= 1 => N_r(2s) >= 1.
*Proof.* Given feasible (O, m, B) at s with balanced M in Z_{2s}: take
O' = 2O, a'_i = 2a_i (valid lifts: 2a_i = 2o_i + 2s m_i), B_0 = 2B; since
3(2s)/2 = 2(3s/2), the scale-2s multiset with B-part B_0 is exactly 2M, and
t -> 2t maps antipodal pairs to antipodal pairs (2t, 2t+2s). New budget
b' = b + s/2: add s/4 antipodal odd-fiber pairs {2u+1, 2u+1+s} (odd fibers
are disjoint from O' u B_0; each pair's doubles balance). QED.
Corollary: thresholds s*(r) exist; with T1, N_r(s) = 0 for s < 2r.

### T4 s=32 tail closure
**Theorem (enumeration + T1).** N_r(32) = 0 for all odd 7 <= r <= 31;
marginal(32) = 1,728,112 complete.
*Proof.* r >= 17: T1. r = 7,9,11,13,15: pure-only exhaustive enumeration
(legitimate by T1) of 1,464,320 / 5,857,280 / 8,945,664 / 4,587,520 /
524,288 sign-classes: zero feasible (logs pure_s32_r*.txt). r = 7 also
re-verified by full unfiltered sweep of 215,414,784 configs (0 feasible),
agreeing with the prior independent O130 sweeps (r = 7, 9, 11). QED.
(The pure-only r=13 closure took ~4 s vs the in-flight ~18-core-hour raw
sweep; r=15 (9.3e12 raw configs) was otherwise unsweepable.)

## 3. Death-cause diagnostics (the mandated tables)

### 3.1 Zero strata (FULL enumeration unless noted)

| (s,r) | b | C(r,2) | classes | mixed->G1 | pure | G2 axis-cap | G3 blocked | G4/G5/G6 | feas | minD |
|---|---|---|---|---|---|---|---|---|---|---|
| (16,5) | 6 | 10 | 69,888 | 68,096 | 1,792 | 1,732 | 60 | 0/0/0 | 0 | 4 |
| (16,7) | 5 | 21 | 732,160 | 731,136 | 1,024 | 1,024 | 0 | 0/0/0 | 0 | 7 |
| (16,9..15) | <=4 | >=36 | 10.0M | ALL (pure O impossible: r > s/2) | 0 | - | - | - | 0 | - |
| (32,7) | 13 | 21 | 215,414,784 | 213,950,464 | 1,464,320 | 1,463,840 | 480 | 0/0/0 | 0 | 7 |
| (32,9) | 12 | 36 | pure-only (raw zero = prior O130 full sweep) | (T1) | 5,857,280 | 5,857,280 | 0 | 0/0/0 | 0 | 10 |
| (32,11) | 11 | 55 | pure-only | (T1) | 8,945,664 | 8,945,664 | 0 | 0/0/0 | 0 | 13 |
| (32,13) | 10 | 78 | pure-only | (T1) | 4,587,520 | 4,587,520 | 0 | 0/0/0 | 0 | 14 |
| (32,15) | 9 | 105 | pure-only | (T1) | 524,288 | 524,288 | 0 | 0/0/0 | 0 | 17 |
| (64,9) | 28 | 36 | NOT MEASURED (SS6.1: closure did not complete; no surviving artifact) | - | - | - | - | - | - | - |

minD = min over G1-passers of D = sum_c |d_c|. minD <= b at (16,5), (32,7),
(32,9): TOTAL budget would suffice; the kill is strictly per-axis
capacity/blocking. At (32, r >= 11) additionally minD > b. (An earlier
draft listed (64,9) minD = 12 here; that number's source log is lost and
the row is withdrawn to NOT MEASURED.)

**Answer to the mandated question:** at every zero stratum, 100% of mixed
dies at odd-self-balance (G1; explained by T1), 100% of pure dies at
G2 (|d| >= 2) or G3 (blocked). h > b, (b-h) odd, (b-h)/2 > v: never binding,
anywhere (G5 vacuous by T2).

### 3.2 Nonzero strata (same instrument; calibration column)

| (s,r) | b | C(r,2) | pure | G2 | G3 | feas classes | waysum = N_r | min h | max h | calib |
|---|---|---|---|---|---|---|---|---|---|---|
| (8,3) | 3 | 3 | 32 | 18 | 6 | 8 | 8 | 1 | 3 | = C19 |
| (16,3) | 7 | 3 | 448 | 190 | 26 | 232 | 672 | 1 | 7 | = O98/O108 |
| (32,3) | 15 | 3 | 4,480 | 1,110 | 66 | 3,304 | 764,544 | 1 | 7 | = O130 |
| (32,5) | 14 | 10 | 139,776 | 120,916 | 7,052 | 11,808 | 99,512 | 6 | 14 | = O130 |
| (64,5) | 30 | 10 | 6,444,032 | 4,050,164 | 181,868 | 2,212,000 | 141,450,979,280 | 6 | 16 | = FRESH census EXACT |
| (64,7) 1/16 stride | 29 | 21 | 26,968,000 | 26,540,367 (98.41%) | 220,992 (0.82%) | 206,641 (0.766%) | 99,900,599 (sample) | 13 | 25 | feas vs census/16 = 206,256: +0.19%; ways vs /16 = 99,177,530: +0.73% |

Turn-on mechanism, measured: (32,7) -> (64,7), same r: per-axis overload
goes from killing 100.000% of pure to ~99.2%; the axis count doubles while
T' = 29 is unchanged. b grows 13 -> 29 but never binds.

### 3.3 min-h ladder (why C(r,2) <= b is the boundary shape)

min clean h: r=3: 1; r=5: 6; r=7: 13; r=9: 24*; r=11: 41* (* = sampled,
s = 128, upper bounds). T' = 7, 16, 29, 46, 67 => max internal antipodal
absorption (T'-h_min)/2 = 3, 5, 8, 11, 13: LINEAR in r, not quadratic.
Products overwhelmingly cannot pair internally; each unpaired product
consumes one forced B; demand ~ C(r,2) - Theta(r) vs supply b = (s+1-r)/2
=> threshold r^2 ~ s. (Mechanism narrative, not a proof; the implemented
kill is the per-axis form, SS3.1.)

### 3.4 The r=5-lane seed inequality: verified as algebra, refuted as mechanism

The r=5 taxonomy lane (`/home/nubs/r5tax-backup/DERIVED-99512.md`, Lemma A)
claims feasibility at (32,5) "provably needs X + F >= 18 - m" (X = absorbed
even-axis collisions, F = balanced multi-axes; verified [P] on all 11,808
classes there) and that this single inequality IS the turn-on mechanism.
Verification verdict, both directions:

- **As algebra: CORRECT and general.** With T' = C(r,2) + r + 1 non-B even
  terms, the identity h = T' - X - F (their s=32, r=5 case: 16 - X - F) plus
  the budget gate h <= b gives the necessary condition
  **X + F >= T' - b = ((r+1)^2 - s)/2** for every (s, r); at (32,5) that is
  18 - 16 = 2, matching their "18 - m" at m = 16 axes. Moreover the sharp
  law r^2 <= s+1 is EXACTLY the statement "required absorption <= r + 1"
  (T' - b <= r+1 <=> r^2 <= s+1) — so the law's boundary is an absorption
  budget, which is why C(r,2) <= b is the equivalent form.
- **As mechanism: REFUTED by the gate-ordered death census.** If the
  aggregate inequality were the binding constraint, die_hgtb (h > b among
  clean configs) would dominate at zero strata. Measured: **die_hgtb = 0 on
  every stratum, zero or nonzero (~5.6e8 configs)**, and minD <= b at
  (16,5), (32,7), (32,9) — the TOTAL budget would suffice; what
  kills every pure config at a zero stratum is the PER-AXIS constraint
  (|d_c| >= 2, G2) or forced-fiber blocking (G3), i.e. the per-axis
  refinement of the aggregate count. "Collisions mandatory at m = 16,
  generic-live at m >= 32" survives as a true corollary of the necessary
  inequality, but the inequality itself is strictly weaker than the
  actual kill.

## 4. Calibration ledger (all EXACT)

| gate | result |
|---|---|
| diag (8,3) full | 8 cls / 8 ways = N_3(8) OK |
| diag (16,3) full | 232 / 672 OK |
| diag (32,3) full | 3,304 / 764,544 OK |
| diag (32,5) full | 11,808 / 99,512 OK (class count = O130 E5 census base) |
| diag (64,5) full | 2,212,000 / 141,450,979,280 = FRESH N_5(64) OK |
| diag (64,7) stride-16 | SS6 vs known 3,300,096 / 1,586,840,480 |
| brute.c (independent: direct B-subset walk, no axis logic) s=8 r=3,5,7,9 | 8/0/0/0; class-by-class (O,m,ways) == diag |
| brute8.py (3rd impl, Python) s=8 r=3 | identical records |
| brute.c s=16 ALL r=3..15 | 672 at r=3 (232 cls, class-by-class == diag); 0 for r=5..15 (re-establishes DERIVED-672 completeness independently) |
| purity falsifier pass_odd_mixed | 0 everywhere (T1) |
| parity falsifier die_par | 0 everywhere (T2) |
| pure-mode == full-mode | identical feasible sets at (16,3),(32,3),(32,5) |
| search.c on known-ON (64,7) | 15,223 hits / 2e6 trials; 5/5 sampled VERIFIED — log file lost (torn-twin); surviving artifact: det_a/det_b = 2 deterministic climb hits at (64,7), byte-identical across twin runs, VERIFIED |
| verify_hit.py re-run on all_hits.txt (THIS session) | verified=29 failed=0 |
| numeric_check.py (independent complex-sum criterion, THIS session) | ok=29 bad=0 |
| diag==brute class-by-class re-diff (THIS session) | (8,3): 8/8 IDENTICAL; (16,3): 232/232 IDENTICAL |
| diag binary == fresh recompile of diag.c | md5 identical |
| law vs known-nonzero | (8,3),(16,3),(32,3),(32,5),(64,3),(64,5),(64,7) all ON OK |
| law vs known zeros | all 13 settled zero strata OFF OK |
| FINAL session (2026-06-12): diag.c + brute.c recompiled | md5 identical to the binaries that produced every log |
| FINAL session: 29-certificate ledger re-verified | verify_hit.py verified=29 failed=0; numeric_check.py ok=29 bad=0; per-(s,r) breakdown re-counted = SS5 exactly; no r=21 line |
| FINAL session: det_a == det_b, both re-verified | cmp identical; 2/2 VERIFIED (64,7) |
| FINAL session: fresh full re-enumerations (recheck_s*_r*.txt) | (8,3) 8/8, (8,5) 0, (8,7) 0, (16,3) 232/672, (16,5) 0 (1732/60 deaths), (16,7) 0 (1024/0), (32,3) 3304/764544, (32,5) 11808/99512 — all equal to SS3.1/SS3.2 rows exactly |

## 5. The law vs r_max = 2j-5: certificates

First divergence: (128, 11): 121 <= 129 => law ON; 2j-5 caps r_max(128) = 9
=> OFF. Certificates (verify_hit.py rebuilds the raw multiset from (O,m,B),
checks antipodal balance; each VERIFIED line proves N_r(s) >= 1):

- (128,9): 8 verified, e.g. O = {53,45,65,39,125,15,57,91,111}, m = 193.
- **(128,11): 3+3 verified (random + independent hill-climb)** =>
  **N_11(128) > 0, r_max = 2j-5 REFUTED**:
  O = {111,15,125,31,81,13,121,35,79,67,21}, m = 793;
  O = {85,21,99,67,105,7,95,123,55,39,9}, m = 333;
  O = {119,73,41,25,1,67,15,89,61,23,75}, m = 851.
  Random hit rate ~1.5e-7 of pure sign-classes: freshly turned on (121 vs 129).
- **(256,13): 10 random hits, 8 printed+verified** — second refutation
  (2j-5 predicts r_max(256) = 11), e.g.
  O = {45,185,175,199,145,225,41,155,233,255,211,249,137}, m = 3796.
- **(256,15): 3 verified (hill-climb)** — third refutation; e.g.
  O = {68,94,172,144,72,244,52,42,200,212,48,86,74,78,130}, m = 14863.
- **(512,17), (512,19): 2+2 verified (hill-climb)**, far beyond 2j-5's
  r_max(512) = 13. **(512,21): CORRECTION — the earlier "racing run
  verified=6 incl. r=21" claim is WITHDRAWN.** Audit of the artifacts
  (this session) finds NO r=21 HIT line anywhere; all three r=21 climb
  runs report hits 0 (300/600/400 restarts, bestcost 2/2/3). The claim was
  a torn-state misread of duplicate-twin output (the failure mode in the
  SS6.2 engineering note). (512,21) is law-ON, UNCERTIFIED, OPEN.
- ON-side coverage: with T3 (doubling), every law-ON point with r <= 19
  is now either censused (s <= 64), certified (above), or implied upward
  (e.g. N_7(128) > 0 from N_7(64) > 0). The single law-ON point not
  covered is (512,21).

Certificate ledger (re-verified this session, two independent ways):
`all_hits.txt` -> verify_hit.py: **verified=29 failed=0**; plus
`numeric_check.py` (fully independent criterion: evaluates the raw
vanishing sum sum zeta^e in complex arithmetic, no balance combinatorics):
**ok=29 bad=0**. Breakdown: (128,9) x8, (128,11) x6, (256,13) x8,
(256,15) x3, (512,17) x2, (512,19) x2. None at r=21.

OFF-side randomized/structured nulls (evidence, not proof):
- (64,9): WITHDRAWN as evidence — the claimed "0 clean in 3e7 random pure
  trials" has no surviving log (torn-twin casualty), and the exhaustive
  closure did not complete (SS6.1). (64,9) is OPEN, conjectured 0 by the
  law (81 > 65) and the (32,7)/(32,9) mechanism only.
- (128,13): 0 clean in 5e7 random trials (169 > 129: law OFF).
- (256,15) random-only 1e8 null: WITHDRAWN — search_s256_r15.txt is a
  0-byte torn-twin casualty; no artifact. (The 3 climb certificates for
  (256,15) are unaffected and re-verified.) Rate collapse measured at the
  surviving artifacts: 1.5e-3 (128,9) -> 1.5e-7 (128,11) -> 3.3e-7
  (256,13); the (64,7) 2e6-trial search log was also lost (its row in SS4
  is flagged), though det_a/det_b preserve 2 deterministic verified
  (64,7) climb hits.

## 6. Late-run results

### 6.1 (64,9) exhaustive pure-only closure: DID NOT COMPLETE

The attempted pure-only exhaustive enumeration (2 x C(32,9) x 2^8 =
1.44e10 sign-classes, fast9 kernel, 3 stride workers) was launched
2026-06-11 but produced empty output files (pure_s64_r9_w*.txt,
fast_s64_r9_w*.txt — all 0 bytes; the runs were killed before any
worker finished). The separately claimed 3e7-trial random null also has
no surviving artifact. **Status: (64,9) is OPEN; N_9(64) = 0 is
conjectured by the law (r^2 = 81 > 65 = s+1) and the measured
per-axis-overload mechanism at (32,7)/(32,9), not by enumeration.**
Re-running is DEFERRED (machine policy: no s=64 kernel runs this pass);
estimated cost ~1-2 core-h with the fast9 pure-only kernel.

### 6.2 Hill-climb witness engine (climb.c) and the full ON-ladder

Local search (cost = per-axis overload + blocked + budget excess; sign-flip
and fiber-move proposals with mild annealing; restarts) succeeds within
<= 600 restarts at every law-ON point attempted EXCEPT the extreme boundary
point (512,21), and stalls at every law-OFF point. All hits re-verified by
verify_hit.py (raw multiset rebuild):

| (s,r) | r^2 vs s+1 | law | 2j-5 | result |
|---|---|---|---|---|
| (128,9) | 81 <= 129 | ON | ON | 8 certificates (random) VERIFIED |
| (128,11) | 121 <= 129 | ON | OFF | 3 random + 3 climb certificates VERIFIED -> 2j-5 REFUTED |
| (128,13) | 169 > 129 | OFF | OFF | 0 hits/5e7 random, 0 clean; climb stall bestcost 2 |
| (256,13) | 169 <= 257 | ON | OFF | 8 certificates VERIFIED -> refutation #2 |
| (256,15) | 225 <= 257 | ON | OFF | 3 climb certificates VERIFIED -> refutation #3 |
| (256,17) | 289 > 257 | OFF | OFF | climb stall bestcost 3 (400 restarts) |
| (512,17) | 289 <= 513 | ON | OFF | 2 climb certificates VERIFIED |
| (512,19) | 361 <= 513 | ON | OFF | 2 climb certificates VERIFIED |
| (512,21) | 441 <= 513 | ON | OFF | UNCERTIFIED: hits 0 in 300+600+400 restarts (3 runs incl. clean re-run); bestcost 2; prior "verified" claim WITHDRAWN (torn-twin misread) |
| (512,23) | 529 > 513 | OFF | OFF | climb stall bestcost 7 (400 restarts) |
| (64,9) | 81 > 65 | OFF | OFF | OPEN: random-null artifact lost; exhaustive closure DNF (SS6.1) |
| (64,11) | 121 > 65 | OFF | OFF | climb stall bestcost 3 |
| (64,13) | 169 > 65 | OFF | OFF | climb stall bestcost 5 |

**Methodology calibration on PROVEN zeros:** the same climber run on
(16,5) and (32,7) (both proven N = 0 by full enumeration) stalls at
bestcost 1; the open OFF-probes stall at bestcost 2-7 (artifact values:
(64,11) 3, (64,13) 5, (128,13) 2, (256,17) 3, (512,23) 7 — an earlier
draft of this table transcribed several of these as 1-2; corrected
2026-06-12 against the surviving climb_off_*.txt logs). The climber
reached cost 0 only at law-ON points, and a climb "hit" at a proven-zero
stratum would have invalidated the OFF-probe methodology; none occurred.
Stall depth does NOT separate ON from OFF near the boundary — see gap 2.

Engineering note: foreground commands that the harness auto-backgrounds get
re-executed as duplicate twin processes; with deterministic seeds the twins
write identical content, but mid-run reads of shared output files can see
torn state (observed on climb_s512_r21*.txt; resolved by clean re-run with
fresh seed + waiting out the twin).

### 6.3 Updated stratum status grid (law: ON iff r^2 <= s+1)

- s=8: r=3 ON (8, census); r>=5: 0 PROVEN (T1; also enumerated 3-way).
- s=16: r=3 ON (672); r=5,7: 0 ENUMERATED (3-way: diag + brute + prior);
  r>=9: 0 PROVEN (T1).
- s=32: r=3 ON (764,544); r=5 ON (99,512); r=7,9,11: 0 ENUMERATED
  (prior sweeps + this run); r=13,15: 0 ENUMERATED (NEW, pure-only + T1);
  r>=17: 0 PROVEN (T1). => marginal(32) = 1,728,112 COMPLETE.
- s=64: r=3,5,7 ON (censuses; N_5 reproduced exactly, N_7 sample-validated);
  r=9: OPEN, conjectured 0 (law OFF: 81 > 65; exhaustive closure DID NOT
  COMPLETE and the random-null artifact is lost — SS6.1; re-run DEFERRED);
  r=11..31: conjectured 0 (climb probes at r=11,13); r>=33: 0 PROVEN (T1).
- s=128: r<=7 ON (T3 from s=64); r=9,11 ON CERTIFIED; r=13..63:
  conjectured 0 (r=13 probed); r>=65: 0 PROVEN (T1).
- s=256: r<=11 ON (T3); r=13,15 ON CERTIFIED; r=17..127: conjectured 0
  (r=17 probed); r>=129: 0 PROVEN (T1).
- s=512: r<=15 ON (T3); r=17,19 ON CERTIFIED; r=21: law-ON, UNCERTIFIED
  (climb stalls at bestcost 2; OPEN both ways); r=23..255: conjectured 0
  (r=23 probed); r>=257: 0 PROVEN (T1).

## 7. Honest gap ledger

1. Proven exclusion covers only r > s/2 (T1). The band sqrt(s+1) < r <= s/2:
   CLOSED by enumeration at s = 16, 32 (all r); OPEN (conjectured 0,
   mechanism measured not proven) at s = 64 r = 9..31 (the (64,9) closure
   did not complete, SS6.1) and all s >= 128 bands. A structural proof must
   lower-bound per-axis overload for pure (O,m) with C(r,2) > b; attempted
   routes (parity floor, additive energy, Archimedean |E1|^2 <= s+3 at all
   conjugates, 4th moment) fall short of r ~ sqrt(s); the obstruction
   involves the SET-ness of B (capacity 1/side/axis) and O-blocking.
2. ON-side above s = 64: proven exactly at certified points; no closed-form
   N_r(s) for r >= 5. **(512,21) is the one law-ON point with no
   certificate** (prior claim withdrawn; three climbs stall at bestcost 2).
   Caveat on interpreting that stall: proven-zero strata stall at
   bestcost 1 and true-OFF probes at 2-7, so stall depth does NOT separate
   ON from OFF at this scale; (512,21) is genuinely open in both
   directions and is the sharpest falsification target for the law.
3. OFF-side at ALL unswept points: randomized/climb nulls only; the
   (256,15) pre-certificate random null AND the (64,9) random null are
   withdrawn (0-byte / missing artifacts — torn-twin casualties).
4. All char-0; per-prime transfer unchanged from O130 SS5.
5. SS3.3 minima at s = 128 are sampled upper bounds.

## 8. Artifacts

/tmp/exclusion/: diag.c (instrumented enumerator, gates G1..G6, pure mode),
brute.c (independent direct-B-subset checker), brute8.py (3rd impl),
search.c (randomized witness search), climb.c / climb2.c (hill-climb
witness finders), fast9.c / fast9b.c (the (64,9) pure-only kernels —
built but never produced output, SS6.1),
verify_hit.py (certificate verifier), numeric_check.py (independent
complex-arithmetic vanishing-sum verifier, this session), all_hits.txt /
all_hits_verified.txt (29-certificate ledger), raw logs diag_s*_r*.txt,
pure_s32_r*.txt, brute_s*_r*.txt, search_s*_r*.txt, climb_*.txt,
det_a/det_b (determinism pair), recheck_s*_r*.txt (2026-06-12 fresh
re-enumerations), diag_v3/brute_v3 (2026-06-12 recompiles, md5-identical).
Known-empty (failed-run) files kept as evidence: pure_s64_r9_w*.txt,
fast_s64_r9_w*.txt, search_s256_r15.txt, climb_s512_r21_hunt.txt,
recovered_r21_hits.txt.
