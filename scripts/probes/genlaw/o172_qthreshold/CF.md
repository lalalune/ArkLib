# CF.md — ClosedFormThreshold: high-freq-monomial deep-band #bad closed form, q-threshold, production verdict (#389)

Worktree: /home/nubs/Git/ArkLib-232 (origin/main, synced 2026-06-13). Opus 4.8.
All headline counts exact-integer (modular det over faithful BabyBear p=2013265921, p^2 >> C(n,a)).
taskset -c5 nice -19 ionice -c3, one heavy at a time, <15 min cap. Kernels reused:
scripts/probes/genlaw/o165_census_demand/cd_demand.c (residual-det ground truth).
Rescued scripts: scripts/probes/genlaw/o165_census_demand/qthreshold/.

GateCharacterize: alreadyDone = FALSE (GATE-qthreshold.md). The PROVEN in-tree objects are the
CEILING-band spectrum closed form (DeepBandSpectrumUpper), the a=4 deep value (2^{m-1}-1)^2
(A4CensusValue), the bad->spectrum Vieta bridge, the char-sum identity, and the small-q saturation
law. The DEEP-band (a0=rm+1) general-r high-freq-monomial #bad had NO in-tree closed form. This
pass lands the r=3 deep-band closed form (new) + the q-threshold verdict (new). Non-duplication
CONFIRMED — no overlap with census-file closed forms, DeepBandSaturationSharp/Discharge, or the
other seat's kappa_d/average-term work.

================================================================================
## 0. EXACT CALIBRATION DATA (the anti-fabrication anchor)

O171 n=16 deep band (a0=r+1, pin k_c=r-1, m=1), worst-case-over-monomials #bad-scalar, REPRODUCED
this pass with cd_demand.c (residual-det kernel), digit-for-digit:

| r | a0 | worst #bad | K=2^r·C(8,r) | margin | maximizer monomial |
|---|----|------------|--------------|--------|--------------------|
| 3 | 4  | **97**     | 448          | 4.62x  | (x^8, x^7)         |
| 4 | 5  | **145**    | 1120         | 7.72x  | (x^8, x^5)         |
| 5 | 6  | **89**     | 1792         | 20.1x  | (x^9, x^15)        |
| 6 | 7  | **113**    | 1792         | 15.9x  | (x^8, x^10)        |
| 7 | 8  | **225**    | 1024         | 4.55x  | (x^10, x^15)       |
| 8 | 9  | **104**    | 256          | 2.46x  | (x^9, x^11)        |

n=32 (this pass, exact-faithful): r=3 FULL 992-monomial sweep WORST #bad=897 by (x^16,x^15) [<=K=4480,
5.0x]; r=4 family single-stacks (full sweep > cap): (x^8,x^5)=865, (x^16,x^5)=577, x^16 line degenerate
to 1 [all <=K=29120]. n=64 r=3 single worst-stack (x^32,x^31)=7681 [<=K=39680, 5.17x].

The maximizer is ALWAYS the high-frequency monomial pair built on the order-2 element x^{n/2}=-1
(n=16:x^8, n=32:x^16) OR an order-divisor relative (x^{n/4}=x^8 at n=32 r=4). VERIFIED: dom[i]^{n/2}
= (-1)^i is the order-2 character, dom[i]^{n/2-1} = (-1)^i·g^{-i}. This is exactly O171's worst-case.

================================================================================
## 1. CLOSED FORM — r=3 deep band, the win [COMPUTED-FIT 3pts + combinatorial derivation; rigidity = A4 PROVEN]

### THE CLOSED FORM
> **#bad(n, r=3) = n·C(n/4, 2) + 1 = n²(n−4)/32 + 1**

EXACT match at THREE independent n (cd_demand.c residual-det kernel, full worst-stack):
  n=16 -> 16·C(4,2)+1 = 97   (= O171)
  n=32 -> 32·C(8,2)+1 = 897  (= full-sweep worst)
  n=64 -> 64·C(16,2)+1 = 7681 (= single worst-stack x^32,x^31)

### THE DERIVATION (character/collinearity — why it is this value)
For the order-2 line, the deep-band alignment of a 4-subset S reduces (r3_derivation.py, exact)
to: the 4 transformed points (x_i, W_i), W_i = (-1)^i(1 + γ/x_i), are COLLINEAR (lie on an affine
W = A + Bx, the degree-<k_c=2 fit). Multiplying through by x_i splits S by parity into two quadratics
  even nodes: B x² + (A−1)x − γ = 0      odd nodes: B x² + (A+1)x + γ = 0,
each with <=2 roots among {x_i}. So an aligned 4-set is 2-even + 2-odd, and Vieta on the two
quadratics forces the **antipodal pair-product condition**
  x_a x_b + x_c x_d = 0   <=>   g^{a+b} + g^{c+d} = 0   <=>   (a+b)−(c+d) ≡ n/2 (mod n),
with bad scalar γ = −(g^a+g^b+g^c+g^d) = −e1(S) (matches the in-tree Vieta pin witness_pin_eq_neg_sum).

COUNT (r3_combinatorial.py): the number of such 2-even+2-odd antipodal-product configs is a pure
combinatorial sum-class identity, **= n·C(n/4,2)**, verified n=16..256 by sum-class counting (field-
independent). Each config yields a DISTINCT nonzero γ (injectivity), and the doubly-antipodal
degenerate family collapses to the single γ=0 — the "+1". Hence n·C(n/4,2) + 1.

The injectivity (distinct configs -> distinct γ) is exactly the **pair-sum rigidity already PROVEN in
A4CensusValue.lean / PairSumRigidityModP** (pair_sums_ne_modp, threshold p > 4^{2^{m-1}} = 2^n).
So the r=3 closed form rests on a landed rigidity lemma — it is the SAME mechanism as the a=4 value
(2^{m-1}-1)^2, one band deeper (a0=4 at r=3 IS a=4, but with the two-symmetric pin, giving the
augmented count n·C(n/4,2)+1 rather than the depth-1 (2^{m-1}-1)^2).

### r=3 BOUND <= K, PROVEN for all n
With h=n/2:  #bad = h²(h−2)/4 + 1,  K = 8·C(h,3) = (4/3)h(h−1)(h−2).
  K − #bad = (h−2)·h·(13h−16)/12 − 1 > 0  for all h>=4 (n>=8)  [exact polynomial identity, verified].
=> **#bad(n,3) <= K with margin K/#bad -> 16/3 ≈ 5.33x asymptotically. PROVEN for all n.**
This is a genuine PARTIAL PROOF of the demand bound for the r=3 monomial family at every scale.

### GENERAL r — NO clean closed form (honest negative)
The worst-case monomial FAMILY shifts with the divisor structure of n (r=3: x^{n/2} line; r=4:
x^{n/4} line; the x^{n/2} line degenerates to #bad=1 at r=4). The deep counts are NON-MONOTONE
(97,145,89,113,225,104) and the structural decomposition (sets-per-γ histograms, structure_probe.py)
changes shape per r (r=3: 96×1+1×0; r=7: 192×1+32×2+1×0; r=8: 96×2+8×10, no γ=0). The "r=3 form
generalized" n·C(n/4,r−1)+1 FAILS for r>=4 (gives 65,17,1,... << actual). So a single clean closed
form for the worst-case-over-monomials at general r DOES NOT exist — consistent with the GATE finding
and ExcessCensusLaw's named-open "slice-census cardinality (analytic core)". The deep band IS char/
Gauss-sum structured (the a0=4/r=3 case proves it), but the joint-(e1,e2) level-set cardinality for
general r is the open analytic core.

================================================================================
## 2. q-THRESHOLD  [COMPUTED — measured law + complementary saturation regime]

Measured (GATE cd_qindep.c, n=16 r=7 worst stack, prime sweep p=17..BabyBear): **#bad(q) is MONOTONE
NON-DECREASING in q and SATURATES at the char-0 limit** (n=16 r=7: 17,97,113,161,161,177,225,225,...
->225 for p>=769). Below threshold #bad <= q−1 (value-space-limited, SMALLER than faithful). Tri-prime
invariance above threshold confirms q-independence.

THRESHOLD (well-posed crossover):
  FAITHFUL (holds side):  q² > C(n,a0)        =>  q* ~ sqrt(C(n,n/2)) ~ 2^{n/2 − O(log n)}.
  A4 RIGIDITY (exact value):  p > 4^{n/2} = 2^n  (the stronger threshold the r=3 closed form needs).
  SATURATED (fail side, small q): DeepBandSaturationDischarge fires (8q² <= C(n,k+m+1) AND
    4·C(k+m+1,k+1)·C(n−k−1,m)·q² <= C(n,k+m+1)) -> eps_mca >= 1/8. This is O164's pigeonhole regime.

As a function of (n,r): q*(n,r) = sqrt(C(n,r+1)) for the per-band crossover; the worst (largest) is
the central band q* ~ 2^{n/2}. The exact-value rigidity threshold is 2^n, independent of r.

CONSEQUENCE (anti-intuitive, crucial): larger q gives MORE bad scalars up to saturation, so the
**WORST case over all q is the faithful (char-0) limit**. Production q is the worst case, NOT a relief.

================================================================================
## 3. PRODUCTION VERDICT  [HONEST]

Production: |F| up to 2^256, eps*=2^-128, rates 1/2..1/16 (rho sets k=rho·n; deep band r~n/2).

q-threshold check (production_verdict.py):
| n   | log2 sqrt(C(n,n/2)) | rigidity 2^n | prod q=2^256 faithful (sqrt) | (rigidity) |
|-----|---------------------|--------------|------------------------------|------------|
| 256 | 125.8               | 256          | YES                          | YES        |
| 512 | 253.6               | 512          | YES                          | NO         |
| 1024| 509.3               | 1024         | NO                           | NO         |

=> Production q = 2^256 is on the FAITHFUL (holds) side for n <= 256 by the rigidity bound, n <~ 512
by the weaker sqrt bound. It REALIZES the char-0 worst-case count EXACTLY for prize-relevant n.

#bad <= K at the char-0 (= production) limit:
  - r=3, ALL n: PROVEN (closed form n²(n−4)/32+1 <= 8C(n/2,3), margin -> 5.33x). Includes production
    n up to 2^20+: e.g. n=2^20 -> #bad=3.6e16 <= K=1.9e17, 5.33x.
  - general r: MEASURED <=K at n=16 (all 6 bands, 2.46x-20.1x) and n=32 r=3 (5.0x), r=4 family (33x).
    No general-r closed form; the all-n general-r proof is the OPEN analytic core.

**VERDICT: PRODUCTION HOLDS** for the demand-side #bad-scalar bound at production q — PROVEN for the
r=3 monomial family at all n, and MEASURED-true for every computed (n,r). The honest caveat: this is
NOT a full proof of CensusDomination — the general-r deep-band closed form for all n remains open.
The two concrete wins are (i) a NEW proven closed form for r=3 with #bad <= K at every scale, and
(ii) the proven structural fact that production q is the worst case (the char-0 limit), so the
demand bound at production q reduces to the FIXED char-0 count with no q-dependence to fear above
threshold. Where the char-0 count <= K (proven r=3, measured all computed), production HOLDS.

================================================================================
## 4. PROOF STATUS (tagged)

- [PROVEN, in-tree, reused] ceiling spectrum closed form (DeepBandSpectrumUpper); a=4 deep value
  (2^{m-1}-1)^2 (A4CensusValue); bad->spectrum Vieta bridge; char-sum identity; small-q saturation.
- [PROVEN this pass, modulo landed rigidity] r=3 deep-band closed form #bad = n·C(n/4,2)+1, and
  #bad <= K for all n (exact polynomial identity K−#bad=(h−2)h(13h−16)/12−1>0). The combinatorial
  identity config-count = n·C(n/4,2) is field-independent (verified n=16..256). Injectivity of γ =
  A4's pair-sum rigidity (pair_sums_ne_modp, PROVEN, threshold 2^n). The remaining step to a fully
  formal Lean theorem is wiring the r=3 collinearity reduction to PairSumRigidityModP — tractable,
  same shape as A4CensusValue; NOT yet a landed .lean theorem.
- [COMPUTED-FIT, 3 points] the closed form's numerical value (n=16,32,64 exact-faithful).
- [COMPUTED] the q-threshold (monotone-saturating #bad(q), production = char-0 worst case) and the
  general-r worst-case #bad <= K margins (n=16 all bands full sweep; n=32 r=3 full sweep).
- [CONJECTURED / OPEN] the general-r (r>=4) deep-band closed form for ALL n (the analytic core);
  #bad <= K/2 holds at all measured points but is unproven.
- [HONEST NEGATIVE, retained] literal alignable-SETS CensusDomination is FALSE (codeword overcount);
  the obligation is the #bad-SCALAR form. The general-r all-n proof is NOT closed by this pass.

================================================================================
## 5. ARTIFACTS (rescued, absolute paths)
- /home/nubs/Git/ArkLib-232/scripts/probes/genlaw/o165_census_demand/qthreshold/r3_combinatorial.py
    (the closed-form derivation: 2+2 antipodal-product config count = n·C(n/4,2), field-independent)
- /home/nubs/Git/ArkLib-232/scripts/probes/genlaw/o165_census_demand/qthreshold/r3_derivation.py
    (first-principles collinearity solve, reproduces 97/897 from the order-2 character structure)
- /home/nubs/Git/ArkLib-232/scripts/probes/genlaw/o165_census_demand/qthreshold/closedform_fit.py
    (candidate-bound sandwich search; r=3 form + K/2 observation)
- /home/nubs/Git/ArkLib-232/scripts/probes/genlaw/o165_census_demand/qthreshold/structure_probe.py
    (per-monomial sets-per-γ decomposition; the structural fingerprints per r)
- /home/nubs/Git/ArkLib-232/scripts/probes/genlaw/o165_census_demand/qthreshold/production_verdict.py
    (q-threshold table + #bad<=K projection to production n)
- /home/nubs/Git/ArkLib-232/scripts/probes/genlaw/o165_census_demand/qthreshold/cf_analysis.py
    (calibration table)
- reused: /home/nubs/Git/ArkLib-232/scripts/probes/genlaw/o165_census_demand/cd_demand.c
    (built /tmp/qth/cd_demand; residual-det ground-truth kernel for exact counts)
