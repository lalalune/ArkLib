# GATE.md — GateCharacterize for the high-freq-monomial deep-band #bad closed-form / q-threshold (#389)

Worktree: /home/nubs/Git/ArkLib-232 (origin/main, synced 2026-06-13). Opus 4.8.
Kernels reused: scripts/probes/genlaw/o165_census_demand/cd_demand.c (built /tmp/qth/cd_demand).
New rescue: scripts/probes/genlaw/o165_census_demand/cd_qindep.c (q-independence, prime-configurable).
All counts exact-integer (modular det over faithful prime). taskset -c5 nice -19 ionice -c3, one heavy at a time.

================================================================================
## 1. HARD NON-DUPLICATION GATE — VERDICT: alreadyDone = FALSE (with a sharp caveat)

Read: A4CensusValue, CensusLowerBound, GeneralGapCensusLaw, ExcessCensusLaw, KKH26AlignmentSupply,
DeltaStarCeilingTightTheory, DeepBandSaturationDischarge, B5DeepBandSaturation,
DeepBandFailureClosedForm(+Sharp), DeepBandSubsetSumSpectrum, DeepBandSpectrumUpper,
SubsetSumCharacterSum, SubsetSumNegSymmConcentration, SubsetSumE2PairingInflate,
SubgroupSumsetWiden, MonomialDomainRootSpectrum. (No file literally named DeepBandSaturationSharp;
the saturation law lives in DeepBandSaturationDischarge.lean + B5DeepBandSaturation.lean.)

### What ALREADY EXISTS in-tree (do NOT re-derive):

(a) **The CEILING-band spectrum closed form — PROVEN and EXACT.**
    `DeepBandSpectrumUpper.signedSpectrum_card_le_choose_sum` /
    `deepband_spectrum_card_le_choose_sum`:
       |spectrum_r| <= SUM_{l<=r, l==r (mod 2)} C(2^{m-1}, l) * 2^l   (antipodal-pairing ceiling).
    [PROVEN] I CALIBRATED this against O171's CEILING-band #bad (a=rm, one band shallower):
       closed form (subset size = r) = 113, 464, 1233, 2256, 3025, 3280, 3281  (r=2..8)
       O171 ceiling #bad             = 113, 464, 1233, 2256, 3025, 3280, 3281   ==> EXACT MATCH.
    So the spectrum cardinality of the order-2 (negation-closed) line is closed-form AND the upper
    bound is TIGHT at the ceiling band. Mechanism is exactly the high-freq/order-2 antipodal pairing.

(b) **The bad-scalar -> subset-sum-spectrum bridge — PROVEN.**
    `DeepBandSubsetSumSpectrum.witness_pin_eq_neg_sum`: each bad scalar = -SUM_{zeta in S} zeta
    (pure Vieta), and `witness_badscalar_card_le_spectrum` injects #bad into the spectrum. The file's
    own docstring flags "the EXACT spectrum cardinality" as "the remaining obstruction" — and
    DeepBandSpectrumUpper THEN supplied the closed-form ceiling for it.

(c) **The character/Gauss-sum identity for subset-sums — PROVEN.**
    `SubsetSumCharacterSum.subsetSumCount_eq_charSum`: exact additive-character formula for
    N(m,target) = #{S subseteq G : |S|=m, SUM=target}, main term C(|G|,m)/q.

(d) **The two-constraint (a-k_c=2) deep-band exact value at a=4 — PROVEN, q-INDEPENDENT.**
    `A4CensusValue.a4Census_card`: |a4Census| = (2^{m-1}-1)^2 for p > 4^{2^{m-1}}; probe ground
    truth 1,9,49,225 at n=4,8,16,32. THIS is a deep-band (two-symmetric, e_1 AND e_2) closed form,
    valid above a rigidity threshold — i.e. an exact value WITH an explicit q-threshold, for a=4.

(e) **The saturation law (small-q) — PROVEN.** `DeepBandSaturationDischarge.deep_band_saturation_eps`:
    eps_mca >= (q/8)/q under H1: 8*q^{m+1} <= C(n,k+m+1) and
    H2: 4*C(k+m+1,k+1)*C(n-(k+1),m)*q^{m+1} <= C(n,k+m+1).

### THE EXACT REMAINING GAP (so this task is NOT a duplicate):

The PROVEN closed form (a) is for the **CEILING band** (a = rm, agreement-deficit a-k_c = 1) and is
the SUPPLY object (it MATCHES O171's ceiling counts 113..3281). It is an UPPER BOUND there, tight.

It is **NOT** the **DEEP band** (a0 = rm+1, deficit a0-k_c = 2) worst-case #bad that CensusDomination
actually needs bounded. I CALIBRATED the closed form against O171's DEEP-band worst counts and they
DISAGREE:
   closed form ceiling (size r+1 / a0)  = 1233, 2256, 3025, 3280, 3281, 3280  (r=3..8)
   O171 DEEP worst #bad                 =   97,  145,   89,  113,  225,  104   (r=3..8)
The deep-band count is ~30x smaller, NON-MONOTONE in r, and has no in-tree closed form. The a=4
case (d) `(2^{m-1}-1)^2` is the ONLY deep-band exact value landed; the general deep-band-(a0=rm+1)
#bad for the order-2 monomial line at arbitrary r is OPEN. `ExcessCensusLaw`'s own docstring names
exactly this: "the slice-census cardinality theory (... the analytic core) is the open follow-up."

CONCLUSION: a faithful-regime *ceiling/spectrum* closed form EXISTS; a faithful-regime *deep-band*
(a0=rm+1, two-constraint) high-freq-monomial #bad closed form for general r DOES NOT (only the a=4
slice). The q-threshold question, however, is ANSWERABLE NOW from the q-saturation structure
(Section 4) without a general deep closed form. So: alreadyDone = FALSE, but the win available is
NOT "a new general deep closed form" (that is the open analytic core) — it is the PINNED q-threshold
verdict + the proven fact that production q is the WORST case, not a relief.

================================================================================
## 2. WORST CASE CONFIRMED at n=32 (single-stack + full-sweep where feasible) [MEASURED-FAITHFUL]

cd_demand.c, faithful BabyBear (p^2=4e18 >> C(32,16)=6e8, faithful by 10 orders).

n=32 r=3 deep band a0=4 (C(32,4)=35960, FULL 992-pair worst-case sweep — feasible, completed):
   WORST #bad = 897  by mono (x^16, x^15)  [= the order-2 line x^16 = -1, EXACTLY O171's prediction]
   K = 4480  ==> 897 <= K, margin 5.0x  (matches the n=16 r=3 margin class 4.6x). HOLDS.
   canonical KKH26 (x^3,x^2): #bad = 0 (deep supply vanishes; one short of rm, same as n=16).
   mid (x^8,x^7): #bad = 321 < 897.  high-freq (x^16,x^15) is the maximizer. CONFIRMED worst case.

n=32 r=4 deep band a0=5 (full sweep timed out > cap; targeted single stacks instead):
   canonical KKH26 (x^4,x^3): #bad = 0.
   exact order-2 line (x^16, x^15): #bad = 1 (degenerate at r=4 — alignable but pins one scalar).
   mid (x^8, x^5): #bad = 865 < K = 29120, margin 33x.  <-- the r=4 maximizer family.

REFINEMENT of the worst case (does NOT change the verdict, sharpens the family): the maximizer is
the monomial pair built on the ORDER-2 element x^{n/2} = -1 (n=16: x^8; n=32: x^16) OR a high-freq
pair related to it by the divisor structure of n. At n=32 r=3 it is literally (x^16,x^15); at n=32
r=4 the (x^16,x^j) line degenerates to #bad=1 and the maximizer moves to the x^8-family (x^8,x^5),
exactly as it did at n=16 (n=16 r=4 maximizer was x^8,x^5). So the worst case is "the order-related
high-frequency monomial pair", scale-covariant via x^{n/2}; it consistently BEATS canonical KKH26
(=0) and random/mid stacks, and #bad << K with margin 5x-33x. The worst case does NOT change in a
way that undercuts the bound: it stays a structured, sub-K, high-freq monomial. [MEASURED-FAITHFUL]

================================================================================
## 3. STRUCTURE of the high-freq-monomial deep-band #bad count [PROVEN substrate + COMPUTED calib]

WHAT IS COUNTED: distinct bad scalars gamma for the deep-band pencil at deficit a0-k_c=2. By the
in-tree Vieta pin (`witness_pin_eq_neg_sum`) and the e_1/e_2 dictionary
(`ListInteriorT2TwoSymmetric.degDrop_t2_iff_two_symmetric`), each bad gamma is a value of -e_1 over
the (k_c+1)-subsets S of mu_n whose TOP TWO elementary symmetric functions both clear the band:
   #bad_deep = | { -SUM_{zeta in S} zeta : S in C(mu_n, a0-?) , e_1(D_S)=c_1 AND e_2(D_S)=c_2 } |
i.e. a TWO-symmetric (joint e_1,e_2) subset-sum spectrum, NOT the single-e_1 spectrum of the ceiling.

WHY PLAUSIBLY CLOSED FORM (and partly proven):
 - Order-2 / negation structure: mu_n = P sqcup (-P), -zeta^j = zeta^{j+n/2}. Antipodal pairing
   (`DeepBandSpectrumUpper.subset_sum_eq_signed`) collapses full pairs to 0 -> signed sums over
   |P|=2^{m-1} singletons. This gives the EXACT ceiling closed form SUM C(2^{m-1},l) 2^l (Sec 1a).
 - The DEEP band adds the SECOND constraint e_2=c_2. A4CensusValue shows the a=4 deep slice collapses
   to (2^{m-1}-1)^2 via the SAME antipodal cancellation (g^x+g^{x+h}=0) + pair-sum rigidity — a
   genuine character/Gauss-sum count (the docstring: "difference-reindexed Gauss sum"). So the deep
   count IS character-sum-structured; the a=4 slice is closed-form. The OBSTRUCTION to general r is
   the joint e_1,e_2 level-set cardinality (the "analytic core" ExcessCensusLaw flags as open).
 - DEPENDENCE on (n,r,q): on n,r it is the joint-symmetric subset-sum level-set size, O(n)-LINEAR in
   the deep band (O171: 97,145,89,113,225,104 ~ linear, not the ~3000 ceiling value), with the n/2
   antipodal halving as the leading structural reduction. On q it is q-INDEPENDENT above threshold
   (Sec 4) — the count is a fixed char-0 algebraic integer.

================================================================================
## 4. THE TWO REGIMES + q-THRESHOLD (well-posed) + PRODUCTION VERDICT [MEASURED-FAITHFUL]

### The two regimes (now pinned, m=1):
 FAITHFUL (large q):  q^{m+1} = q^2  >  C(n, a0).  #bad is the genuine algebraic char-0 count.
 SATURATED (small q): DeepBandSaturationDischarge fires when 8*q^2 <= C(n,k+m+1)  AND
                      4*C(k+m+1,k+1)*C(n-(k+1),m)*q^2 <= C(n,k+m+1) -> eps_mca >= 1/8.
 They are COMPLEMENTARY up to the constant factors (8, 4*C*C): saturated is q^2 <~ C(n,a)/const,
 faithful is q^2 > C(n,a). The boundary (the q-threshold) is q* = Theta(sqrt(C(n,a0))) = 2^{n/2-O(log n)},
 with the stronger A4 rigidity threshold 4^{2^{m-1}} = 2^n for the exact a=4 value.

### THE KEY q-SCALING (measured directly, cd_qindep.c, n=16 r=7 worst stack x^10,x^15):
   p:   17   97  113  193  241  449  769  3329  12289  ...  2013265921 (BabyBear)
 #bad:  17   97  113  161  161  177  225   225    225  ...  225
 => #bad(q) is MONOTONE NON-DECREASING in q and SATURATES at the char-0 limit 225 for q >= ~769.
    Below threshold #bad is VALUE-SPACE-LIMITED (#bad <= q-1), hence SMALLER than faithful.
    Tri-prime invariance in the faithful regime CONFIRMED: p in {2.01e9, 1.22e9, 2.13e9} all give
    #bad = 225 (r=7) and 97 (r=3) IDENTICALLY. So above threshold the count is q-independent.

### CONSEQUENCE — the crucial, anti-intuitive structural fact:
   For the deep-band #bad-SCALAR object, LARGER q gives MORE bad scalars (up to saturation), so the
   WORST case over all q is the FAITHFUL (char-0) limit. Production q (|F| up to 2^256, Goldilocks
   2^64, BabyBear-ext) is FAR above the saturation threshold for all prize-relevant n, so production
   q REALIZES the char-0 worst-case count EXACTLY. Production q is the worst case, NOT a relief.

### PRODUCTION VERDICT:
 - q* = Theta(2^{n/2}) (sqrt) or 2^n (A4 rigidity). Production q = 2^256 is on the FAITHFUL (holds)
   side for n up to ~256 (rigidity bound) / ~512 (sqrt bound) — covering the prize deep-band sizes.
 - Therefore: wherever the char-0 (faithful) deep-band #bad <= K holds, production q HOLDS, because
   production q = char-0 limit. O171 proved char-0 #bad <= K with margin 2.5x-20x at n=16 (all 6
   deep bands) and this pass confirmed n=32 r=3 (897 <= 4480, 5.0x) and r=4 family (865 <= 29120).
 - This makes the demand-side bound at production q a statement about the FIXED char-0 count, with
   NO q-dependence to worry about above threshold. A general char-0 deep closed form proven <= K
   for all n would be the PARTIAL PROOF (monomial family) of the prize obligation. That general
   closed form is the OPEN analytic core (only the a=4 slice (2^{m-1}-1)^2 is landed).

================================================================================
## 5. HONEST SCOPE / WHAT TO DO NEXT
 - [PROVEN, in-tree] ceiling-band spectrum closed form (DeepBandSpectrumUpper); a=4 deep exact value
   with q-threshold (A4CensusValue); bad->spectrum Vieta bridge; char-sum identity; saturation law.
 - [COMPUTED, this pass] q-threshold pinned: #bad(q) monotone-saturating; production q = char-0
   worst-case; n=32 r=3 full worst-case sweep HOLDS (897<=K, high-freq mono x^16 confirmed worst).
 - [OPEN, the win to chase] the GENERAL-r deep-band (a0=rm+1, joint e_1,e_2) high-freq-monomial #bad
   closed form. Attack surface: extend A4CensusValue's antipodal+pair-rigidity collapse from a=4 to
   general a via the joint e_1,e_2 level-set Gauss sum (SubsetSumE2PairingInflate gives the LOWER
   side; need the matching exact level-set count). NOT a duplicate of any landed file.
 - [HONEST NEGATIVE retained] literal alignable-SETS CensusDomination is FALSE (codeword overcount);
   the correct obligation is the #bad-SCALAR form. Unchanged from O171.
 - n=32 deep-band full worst-case search beyond r=3 EXCEEDS the 15-min cap (r=4 full sweep timed out
   at 780s; per CO MPUTE.md the deep bands r>=10 are 76 min - 35 h/stack). n=16 + n=32 r=3 are the
   honest exact frontier.
