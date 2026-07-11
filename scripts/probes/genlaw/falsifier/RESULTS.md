# The per-prime falsifier at n=64: exhaustive mod-p enumeration of the (15,3) and (14,5) marginal strata — THE CHAR-0 → MOD-P TRANSFER FAILS AT BOTH PRODUCTION PRIMES

Lane `nubs/issue232-effective-pa`, 2026-06-10. Closes RESULTS-GENERAL-LAW.md (O130)
caveat 2 for BabyBear and p2 — in the negative direction: the per-prime counts are
now exhaustive, and they are **not** equal to the char-0 counts.

## TL;DR

The O130 n=64 marginal counts (764,544 r=3 classes; 99,512 r=5 classes) are
**char-0 truths that do NOT transfer verbatim** to the two production primes.
Exhaustive per-class meet-in-the-middle enumeration of the membership equation over
ALL pattern-(15,3) and (14,5) classes (including char-0-infeasible ones) finds
genuine spurious mod-p marginal codewords at **both** BabyBear (p = 15·2^27+1) and
p2 (3·2^30+1):

| stratum | prime | char-0 classes | mod-p count | spurious excess | spurious (O,m)-classes |
|---|---|---|---|---|---|
| r=3 (15,3), 19,840 classes × C(29,15) | BabyBear | 764,544 | **764,555** | **+11** | 2 (both char-0-infeasible) |
| r=3 (15,3) | p2 | 764,544 | **764,598** | **+54** | 10 (all char-0-infeasible) |
| r=5 (14,5), 3,222,016 classes × C(27,14) | BabyBear | 99,512 | **132,965** | **+33,453** | 4,242 |
| r=5 (14,5) | p2 | 99,512 | **116,453** | **+16,941** | 2,409 |

Every r=3 spurious config (all 65) was triple-checked: (i) MITM count == full
direct brute force over all C(29,15) = 77,558,760 B-subsets of the exact flagged
class, (ii) each explicit spurious (B,O,σ) rebuilt by independent raw polynomial
arithmetic in Python — each yields a **genuine monic deg-34 e with coeff(X^33)=0,
coeff(X^32)=λ**, i.e. w−e is a true deg<32 RS codeword mod p agreeing with w on
exactly 33 points, (iii) each is **not** char-0 balanced (α ≠ 0 in ℤ[ζ₆₄]) with
α(ζ→h) ≡ 0 mod p verified directly. These are real marginal-layer codewords mod p
that do not exist in characteristic 0. The 45 historical spot checks missed them
because the spurious rate is ~10⁻¹¹ per config.

**What this means:** ℓ₌₃₃ mod p ≠ ℓ₌₃₃ char-0 at the production primes. Any
per-prime statement at n=64 must add the (computable, now computed) per-prime
correction; the effective-transfer threshold (p > N(α) bound) is not just a proof
artifact — sub-threshold primes really do pick up extra codewords.

## The reduction the falsifier rests on (verified, not assumed)

`verify_reduction.py` (this dir): for e = ∏_{c∈B}(X²−z_c)·∏ᵢ(X−xᵢ)·(X−ξ),
ξ = −Σxᵢ, the identity

  coeff(X^s) of e = λ − α,   α := e₂(x⃗) + e₁(O_z) + e₁(B_z) − z*

holds **as field elements** (not just as a membership biconditional), pinned
against raw polynomial multiplication on 120 random configs at each of
(BabyBear, p2) × (n=32, 64) + (97, n=32) + (193, n=64): 720/720 exact. Hence
marginal-layer membership of (B,O,σ) mod p is the ONE linear equation

  Σ_{c∈B} G[c] ≡ z* − (e₂(x⃗) + e₁(O_z))  (mod p),   G[c] = ζ^{2c} = H[2c],

and per fixed class (O,σ) the mod-p count is an exact subset-sum count, computed
by meet-in-the-middle (split candidate fibers ~half/half; left half bucketed by
(sum, size) and sorted; right half probed with binary search). Conventions exactly
those of `construct_n64.py`: H = powers of h = g0^((p−1)/n), g0 = 31 (BabyBear) /
5 (p2, found by primitive-root search), z* = H[s/2], λ = p − z*.

char-0 truth per class: independent re-implementation of the DERIVED-672
placement rule (forced/free axes, C(v,(b−h)/2)), cross-checked per class.

## Calibration gates (all passed before any n=64 run)

| gate | result |
|---|---|
| n=16 (s=8, pattern (3,3)), BabyBear, brute+MITM | 224 classes; char0=8=modp; spur 0; brute==MITM; per-class == audit DP (8 cls, w=8) |
| n=32 (s=16, pattern (7,3)), BabyBear | 2,240 cls × C(13,7)=1,716 brute: char0 = modp = **672** ✓; spur 0; brute==MITM per class |
| n=32, p2 | modp = **672** ✓, spur 0, brute==MITM |
| n=32, p=97 (small split prime, positive control) | brute==MITM exactly; **massive spuriousness: modp 39,388 vs 672 → +38,716** over all 2,240 classes (uniform heuristic 2240·1716/97 ≈ 39,629); 672 classes with ξ∈μ₃₂∪{0} mod 97 |
| per-class char-0 vs audit_sweep64 DP (s=8, 16) | exact dict equality on (O,m)→(h,v,w) |
| n=64 r=3 char-0 side | Σ = 764,544 ✓, 3,304 feasible classes ✓, per-class == audit DP at both prime runs |
| n=64 r=5 char-0 side | Σ = 99,512 ✓, 11,808 feasible classes ✓, per-class == audit DP |
| second-session re-verification (2026-06-11) | binary recompiled, s=8/s=16 calibration logs byte-identical; reduction re-pinned 720/720; all 65 r=3 spurious configs re-confirmed; 4 flagged classes (2 per prime) reproduced by a from-scratch dict-MITM in Python (`indep_check.py`) sharing no code with falsify.c |

The 97 gate proves the pipeline *detects* spuriousness at the predicted magnitude
when it exists; the BabyBear/p2 n=32 gates reproduce the exhaustive O98 census
(zero spurious there, as proven).

## The n=64 r=3 finding in full

Spurious classes (each lists its excess; every one char-0-INFEASIBLE — the mod-p
solutions appear in classes the placement rule kills in char 0; xiH: none, all
agree exactly 33):

- BabyBear: O=(5,20,31) σ-mask 2 → +10; O=(14,17,21) mask 1 → +1.
- p2: O=(0,21,23)m1 +2; (1,20,22)m1 +3; (1,22,31)m0 +2; (4,24,29)m1 +1;
  (6,10,21)m1 +6; (8,10,15)m3 +10; (9,12,14)m1 +15; (10,11,12)m3 +4;
  (12,24,29)m2 +1; (24,29,31)m2 +10.

Mechanism (alpha_analysis.py): each spurious class realizes exactly **one**
nonzero lattice vector α ∈ ℤ[ζ₆₄] (L1 norm 14 or 18) with α(h) ≡ 0 mod p; the
class's excess is the number of B-subsets realizing that same e₁(B_z) value
(the usual placement coset). At p2, **six of the ten classes share literally the
same bad α** — one vanishing lattice vector fanning out across (O,σ)-space. So
spuriousness is driven by a handful of "bad alphas" per prime (BabyBear: 2
distinct, p2: 5 distinct at r=3), each below the norm-transfer threshold.

## The n=64 r=5 stratum

**The surplus scales dramatically with pattern complexity.** Full both-prime scan of all
3,222,016 (O,mask) classes (crossfoots exact: char-0 Σ = 99,512, 11,808 feasible classes,
per-class char-0 == audit DP at both primes):

- **BabyBear: mod-p = 132,965 = char-0 + 33,453** (33.6% relative; 4,242 spurious classes)
- **p₂: mod-p = 116,453 = char-0 + 16,941** (17.0% relative; 2,409 classes)

vs r=3's +11/+54 (1.4×10⁻⁵ relative). The r=5 surplus sits at the uniform-heuristic scale:
the (14,5) pattern's α-lattice is rich enough that p | N(α) is statistically generic at
~2³¹-size primes — the structural char-0 core keeps a large generic mod-p halo. Locality:
at BabyBear every spurious solution lands on a char-0-INFEASIBLE class (0 excess on the
11,808 feasible ones); at p₂, exactly ONE feasible class carries excess 1 — the first
observed mod-p inflation of a feasible class count.

Verification (`r5_finals_extract.txt`, `brute_r5_*.txt`, `alpha_r5_report.txt`): 25-class
full-brute samples per prime — 50/50 mitm == brute, genuine_bal == char0; 447 explicit
spurious configs (238 BB + 209 p₂) ALL reconstructed by raw polynomial arithmetic as
monic deg-34, coeff(X³³)=0, coeff(X³²)=λ, agreement exactly 33; α-spectrum: every sampled
class has a UNIQUE α (no sharing, unlike r=3 at p₂), L1 norms 12–20, all α(ζ) ≡ 0 mod p
verified. xiH = 0 at both primes.

## L4 mod p (ξ slipping into μ₆₄)

At both production primes, across all 19,840 r=3 AND all 3,222,016 r=5 classes: ξ ∈ μ₆₄ never occurs mod p (xiH=0 at both primes).
classes have ξ ∈ μ₆₄ ∪ {0} mod p (r=3: zero at both primes). At p=97 (control)
this happens constantly (672/2,240 classes), confirming the check is live.

## Positive control at n=64

p = 193 (split, far below every bound), r=3 stratum, same pipeline:
**modp = 7,972,868,496 vs char-0 764,544 → excess +7,972,103,952, every one of
the 19,840 classes spurious** — within 0.01% of the uniform heuristic
19,840·C(29,15)/193 ≈ 7.973×10⁹; additionally 6,272 classes (1,023 of them
char-0-feasible) have ξ ∈ μ₆₄ ∪ {0} mod 193, i.e. at tiny primes the L4 break
(marginal element promoted to agree-34) also fires constantly. The n=64
machinery, not just the n=32 calibrator, visibly detects spuriousness when the
prime is small.

Heuristic context for the production primes: the same uniform model predicts
~764 (BabyBear) / ~477 (p2) excess at r=3 — the observed +11 / +54 are far
below it, i.e. at 31-bit primes the surviving spuriousness is the structured
tail (a handful of bad alphas), not uniform-density mass.

## Method / artifacts (this dir)

- `falsify.c` — the falsifier. Modes: exhaustive `scan` (per-class placement-rule
  char-0 + MITM mod-p count; SPUR/XI/C0REC lines; worker split), `brute`/`both`
  (direct enumeration, used for the n≤32 calibration gates), `class` (full
  C(M,b) brute of one class + explicit spurious-B dump + independent
  antipodal-balance check per hit). Meet-in-the-middle: left-half subset sums
  radix-sorted by (popcount, value); right half probed by binary search;
  exact per-class counts, no sampling, no hashing collisions possible.
- `verify_reduction.py` — pins the coefficient identity (the only algebra the
  scan trusts) against raw polynomial arithmetic, all primes, both scales.
- `compare_recs.py` — per-class char-0 cross-check vs `audit_sweep64.c` (the
  O130 audit's independent DP sweeper), exact at s=8/16/32, r=3/5.
- `verify_spurious.py`, `verify_spurious_r5.py` — the triple-check: rebuild every
  dumped spurious config by polynomial multiplication, assert genuine mod-p
  marginal codeword + char-0 imbalance + α(h)≡0.
- `alpha_analysis.py` — the bad-alpha census above.
- `aggregate_r5.py` — r=5 worker aggregation + sample drawing.
- Logs: `cal_*` (calibration), `r3_*`, `r5_*` (scans), `brute_*` (class-mode
  triple-checks), `audit_*` (audit DP reference records).

Machine etiquette: every process `nice -n 19 ionice -c3`, ≤ 3 concurrent.

## Honest caveats

1. **Scope**: exhaustive for the (15,3) and (14,5) strata — the entire char-0-
   active marginal layer — over ALL (O,σ)-classes including char-0-infeasible
   ones, plus the L4/ξ check per class. NOT scanned mod p: odd r ≥ 7 patterns (r runs to 31); r = 1 is excluded mod p by the same prime-independent argument as char-0 (ξ = −x₁ ∈ μ₆₄ always, forcing agreement 34, never 33)
   (char-0 empty but mod-p spurious solutions there are not excluded by anything
   above — same mechanism could light them up), and the witness layer's own
   mod-p surplus. The full interpolation census (C(64,33) ≈ 7×10¹⁷) remains
   infeasible; this falsifier is the strongest feasible per-prime statement of
   its kind.
2. The r=5 triple-check is on a 25-class random sample per prime (every dumped
   spurious B verified), not all flagged classes — r=3 was triple-checked
   exhaustively. MITM itself was validated brute-equal per class at every
   calibration scale and on all 12 r=3 flagged classes.
3. char-0 reference = placement rule, cross-checked per class against the audit
   DP — both ultimately rest on the O130 lemma chain (independently audited);
   the falsifier re-verifies balance directly per hit in class mode.
4. Spurious counts are for the fixed embedding ζ → g0^((p−1)/64). Galois
   conjugate embeddings permute classes but preserve totals; the count "mod-p
   marginal codewords for w" is embedding-independent only as a total — per-class
   labels follow construct_n64.py's convention.
