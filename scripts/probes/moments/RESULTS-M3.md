# The third moment IS domain-dependent — verdicts of the M3 probe program

Issue #334, agreement-spectrum moments lane. Pre-registration: `HYPOTHESES-M3.md`
(written before any probe ran). Raw tables: `RESULTS-M3-RAW.md`. Everything below is
EXACT integer arithmetic; the decomposition engine was cross-validated byte-exactly
against an independent brute-force ground truth on 7 setups (k ∈ {2,3}, subgroup and
non-subgroup domains, q ∈ {5,7,13}) before any experiment was believed.

## Headline

**M1 and M2 of the agreement spectrum are domain-independent (O120/O122); M3 is NOT.
Domain-dependence of the agreement-spectrum moments begins exactly at (k, r) = (3, 3),
and the invariant M3 sees is the pencil census — the (A, s, t₂) histogram of the
q²+q+1 Möbius involutions x ~ y ⟺ φ₀xy − φ₁(x+y) + φ₂ = 0 restricted to the domain.**

| hypothesis | verdict | evidence |
|---|---|---|
| H4 (the reduction) | **CONFIRMED** | decomp == brute force exactly, 7/7 setups |
| H2 (k=2 rigidity) | **CONFIRMED** | subgroup vs 2 randoms at q=41, n=8: tensors EXACTLY equal |
| H1 (k=3 separation) | **CONFIRMED** | subgroup outside the random cloud at every cell (below) |
| H5 (t₂ mean pinned) | **CONFIRMED** | Σ_φ t₂ = C(n,2)·(q−1) asserted on every run, every domain |
| A5 (normalizer spikes) | **CONFIRMED for n ≥ 10**, refined at n=8 | big-spike set == predicted family EXACTLY at (41,10), (113,16), (257,16) |
| A4 (moment fingerprint) | **PARTIALLY CONFIRMED** | AP separates at n=16 (additive pencils), not at n=8; gpset does not separate |
| A2 (exact ΔM3 formula) | **ESTABLISHED COMPUTATIONALLY** | M3 is a closed-form function of the (A,s,t₂) histogram + MDS weights (the engine IS the formula); write-up pending |
| A1 (moduli law) | k=2/r=3 and k=3/r=3 cells confirmed; (2,4) cross-ratio cell **untested** | next cycle |
| A3 (δ*-relevance) | first look: relative deviations are tiny (below) | quantification pending |

## The separation, measured against the random cloud

Metric: max-abs-entry distance between full M3 tensors; "cloud" = the sampled random
domains (3–5 seeds); separation = min distance from the structured domain to any
random, vs the cloud's own diameter. (3–5 seeds is a yardstick, not a p-value; the
assumption-free facts are the exact inequalities and equalities themselves.)

| cell | cloud diameter | subgroup | AP | gpset |
|---|---|---|---|---|
| q=41, n=8 | 3.24e13 | **1.11e14 (3.4×)** | 4.6e12 (inside) | 4.6e12 (inside) |
| q=41, n=10 | **0** (3 randoms identical!) | 2.45e17 (∞) | 1.20e16 (∞) | — |
| q=113, n=16 | 1.53e33 | **2.15e34 (14.1×)** | 5.9e33 (3.9×) | — |
| q=257, n=16 | 4.24e38 | **4.60e39 (10.8×)** | 1.57e39 (3.7×) | — |

* The subgroup deviates from every sampled random domain in the SAME direction
  (M3[2,2,2] strictly larger) at every cell; the maximal deviation always sits at
  (j₁,j₂,j₃) = (2,2,2) = (k−1,k−1,k−1).
* **Coset invariance (exact, unplanned find):** D = gH has M3 IDENTICAL to H — in fact
  M_r is invariant under the affine action x ↦ ax+b on domains for every r, since
  p ↦ p(ax+b) permutes the code. Trivial to prove, worth a lemma; it means "smooth
  coset" and "smooth subgroup" are indistinguishable to ALL agreement moments.
* The q=41, n=10 degeneracy (three random 10-subsets with literally identical M3) is
  the (A,s,t₂)-histogram concentrating at small q — the structured domains still
  separate from that common value.

## The mechanism, exactly as predicted (and one surprise)

The subgroup's pencil spectrum at n=16 (both q=113 and q=257):

    t₂ histogram: {0: ..., 1: ..., 2: ..., 3: 544–800} ∪ {7: 8, 8: 9}   — NOTHING at 4–6

* The 17 = n+1 spike pencils are EXACTLY the predicted torus-normalizer family:
  φ = (1, 0, f₂) with −f₂ ∈ H (the involutions x ↦ c/x, c ∈ H: t₂ = (n−2)/2 when c is
  a square in H — 2 fixed points — and n/2 otherwise) plus φ = (0,1,0) (x ↦ −x,
  present since −1 ∈ H for even n). Set equality verified exactly at (41,10),
  (113,16), (257,16); at (41,8) the threshold-3 band also catches 16 non-normalizer
  involutions stabilizing 6 of 8 points — small-scale noise, gone by n=10.
* **The spectral gap (surprise):** for the subgroup at n=16, NO pencil has t₂ ∈ {4,5,6}
  — the noise band caps at 3 and the normalizer band sits isolated at {(n−2)/2, n/2}.
  Random domains instead fill the gap with a decaying tail (max t₂ = 4–5). Conjecture
  (provable via Weil-type bounds on (1,1)-curves against subgroup characters, cf. the
  MSS Cor 4.1 energy line): for q ≳ n², non-normalizer pencils have t₂ = O(n²/q + 1)
  while the normalizer band is pinned at ~n/2 — the gap is a theorem in waiting.
* AP domains spike the ADDITIVE pencil family φ = (0,1,c) (x+y = c), as predicted
  (A4); their energy at matched (q,n) is below the subgroup's (3.7–3.9× vs 10.8–14.1×).

## A3 first look (honesty paragraph)

Relative deviations are tiny: |ΔM3|/M3 at the argmax entry ≈ 1.9e−11 (q=113) and
5.6e−13 (q=257) at n=16 — scaling like ~q⁻⁴ at fixed n. The third moment SEES the
domain, but at magnitudes far below what a 2⁻¹²⁸-resolution tail argument would need
at prize parameters. The honest A3 statement stands as the working expectation:
moment-3 information distinguishes smooth from random, but plausibly cannot move δ*
by magnitude — to be quantified through the Chebyshev/third-moment tail machinery.

## A3 quantified — the prize-regime answer (2026-06-14, D1 / #407)

`probe_m3_prize_regime_excess.py` (this dir) runs the separation at PRIZE shape: PROPER
2-power subgroups μ_n = μ_{2^μ} of F_p\* with p = n·m+1, p ~ n^β, β ∈ {2,3,4}, single +
multi prime. Two exact new facts:

* **Rigidity sharpened.** Not only Σ_φ t₂ (the published H5) but ALSO **Σ_φ t₂²** is
  EXACTLY domain-independent (subgroup == random, to the integer, every cell). The
  agreement-spectrum's domain-dependence enters the pencil census ONLY at the THIRD
  power-sum **Σ_φ t₂³** — sharper than the "t₂ variance" framing.
* **The structured signal is q-INDEPENDENT and → n⁴/8; relative excess decays only
  polynomially.** The *absolute* third-moment excess
  `D3 := Σ_φ t₂³(μ_n) − E_rand[Σ_φ t₂³]` is essentially q-independent (≈ 0.057·n⁴ at
  n=8 across q = 17…1049, a 60× span) and equals the torus-normalizer-band mass
  `(n+1)·(n/2)³ = n⁴/8` (verified → 1/8, n up to 128 at p ~ n⁴). The random baseline
  grows ~q, so the *relative* excess r3 = D3/E_rand decays — but only **polynomially in
  q** (fitted exponent in (−1, 0), range-dependent ≈ q^{−0.14…−0.58}), NOT the q⁻⁴ that
  the raw-tensor |ΔM3|/M3 above measured. The q⁻⁴ was the wrong normalization for a tail
  argument (it divides by the full M3 ~ q^{n+3k}); the decision-relevant ratio is the
  t₂-cube excess.

**Transfer-direction verdict (D1).** The smooth domain M3 is STRICTLY LARGER than random
at every cell, same sign, argmax always (k−1,k−1,k−1): smooth does **not inherit** the
random third moment — it exceeds it by the involution-energy of the torus normalizer.
The literal derandomization "random good ⇒ smooth good at the same (t,L)" therefore FAILS
*as a moment inequality*. But the excess is a fixed q-independent structured signal ~n⁴/8
(polynomial), so whether it moves δ* is an upper-tail question against 2⁻¹²⁸ resolution —
plausibly NO by magnitude, but only polynomially (not exponentially) small relative excess.
Crucially the object is a Weil-(1,1)-pencil involution count, **NOT** a character sum:
this thread is BGK-INDEPENDENT (it does not reduce to the max_b‖η_b‖ Paley/BCHKS wall).
The open quantitative core is the spectral-gap theorem (non-normalizer t₂ = O(n²/q+1) by
Weil) feeding a 3rd-moment tail bound at prize resolution.

## What this changes for the program

1. O120's question "does the smooth domain's tail exceed the random domain's?" now
   has a moment-level answer: **the first statistic that sees the domain is M3, and
   what it measures is involution energy.** Any future domain-independence claim for
   a statistic class must exclude moment 3 — and any derandomization argument that is
   "moment-blind past M2" is now provably blind to real structure.
2. The separating invariant is finite, computable, and classified: (A,s,t₂)-census =
   MDS data + normalizer band + noise band (+ gap). The k=3 theory bricks are now
   sharply posed: (i) k=2 rigidity as a theorem (PGL₂ 3-transitivity); (ii) affine
   invariance lemma; (iii) the ΔM3 closed form as a function of the census (the
   engine's formula, written as mathematics); (iv) the spectral-gap theorem.
3. The moduli law (A1) predicts the next cell: M4 at k=2 should separate AP from
   random via cross-ratio energy. Untested — next cycle's falsifier.

## Reproduction

    python3 probe_agreement_m3_bruteforce.py --q 7 --k 3 --domain subgroup:6
    python3 probe_agreement_m3_decomp.py     --q 7 --k 3 --domain subgroup:6
    # identical JSON; then:
    python3 probe_agreement_m3_experiment.py   # writes RESULTS-M3-RAW.md + experiment/

Validation artifacts: `validation/` (10 setup pairs, byte-exact; audit note: the k=2 subgroup-vs-random control is engine-structural — the independent k=2 evidence is the brute-vs-decomp byte-exact validations). Engine internal
asserts include: the ordered-pair partition of q^{2k}; MDS weight distribution
(closed form == enumeration); the t₂ first moment; N(profile) vs brute word counts;
the full ordered-pair profile histogram vs the class decomposition (q^k ≤ 1400);
fiber relation vs direct kernel-basis fibers (q ≤ 13); GL₂ brute check of the
(q−1)·(distinct triples) basis-counting lemma; M2/M1 marginals; S3 symmetry; total
mass q^{n+3k}.
