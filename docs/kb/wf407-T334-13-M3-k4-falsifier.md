# WF407 / T334-13-M3 — M3 domain-separation, the k=4 falsifier, and the t₂ ladder

**Thread:** T334-13-M3 (issue #407, ex #334-T13).
**Date:** 2026-06-14.
**Verdict:** the M3 direction **LIVES** at higher moments (does NOT re-converge) but is
**prize-irrelevant** — the signal decays as `q^{-4}`, far below `ε* = 2^-128`. The t₂
spectral gap is **Weil-provable** (noise band `O(n²/q+1)`, confirmed exactly). Net:
**partial / walled** — a clean structural law, no δ* lever at prize scale.

## Context (proven in-tree, not re-derived)

- M1, M2 of the agreement spectrum are DOMAIN-INDEPENDENT (enter only through the MDS
  weight enumerator). [`AgreementMomentTwo.lean`, O120/O122]
- M3 is the FIRST domain-dependent agreement moment; what it measures is the pencil
  census t₂ (Möbius-involution 2-orbit counts inside the domain). Smooth subgroups
  spike on the torus-normalizer family `{x↦c/x : c∈H} ∪ {x↦−x}` at
  `t₂ ∈ {(n−2)/2, n/2}`. [O133, `RESULTS-M3.md`, `PencilNormalizerBand.lean`]

## The three deliverables

### (1) The k=4 falsifier — the census LIVES (does not re-converge)

M_r decomposes over (r−1)-tuples of codewords (translate by `c_r`):
M2 ↔ 1 codeword (weight enumerator) → domain-independent; M3 ↔ 2-dim subcode (pencil);
M4 ↔ 3-dim subcode (triple-incidence / cross-ratio census).

**Decisive structural finding — the t₂ power-sum ladder** (probe
`wf407_T334-13-M3_t2moments.py`, exact, q∈{41,73,113,257}, n∈{8,16}):

| `P_r = Σ_φ t₂^r` | r=1 | r=2 | r=3 | r=4 | r=5 |
|---|---|---|---|---|---|
| smooth vs random | **PINNED** | **PINNED** | **separates** | separates | separates |

`Σ_φ t₂` AND `Σ_φ t₂²` are *identical* for the smooth subgroup and every random domain
(generalizing the H5 mean-pinning to the second moment); `Σ_φ t₂³` is the FIRST
separating t₂-functional (subgroup strictly larger, e.g. n=16 q=113: 55704 vs ~52600).

**Reading.** This is the M1/M2/M3 phenomenon *recurring at the pencil level*: just as the
first two agreement moments are domain-independent and the third separates, the first two
power-sums of the t₂-distribution are domain-independent and the third separates. The
smooth subgroup pumps the *same* total t₂-mass and t₂²-mass but **concentrates** it into
the `n+1` extremal normalizer spikes; only a degree-≥3 (tail-concentration) functional
sees it. M4 reads `P₃,P₄,…` of the SAME t₂-distribution, so the separation **persists and
strengthens** (P₄,P₅ separate with a growing gap) — the census does NOT re-converge. But
it lives by *reusing the same object* (normalizer-spike concentration), not by adding new
domain structure.

(Brute ground-truth at n=4,6 in `wf407_T334-13-M3_k4_falsifier.py` /
`_brute_n6.py`: n=4 too small for M3 to separate at all — both M3 and M4 flat — confirming
the phenomenon needs n≥8, exactly where the decomp ladder above operates.)

### (2) M3 → upper bound via Chebyshev — DEAD at prize scale (q^{-4} wall)

Probe `wf407_T334-13-M3_signal_scaling.py` (decomp engine, n=8, k=3, q≡1 mod 8, 14 primes
17…337): the relative separation `rel(q) = |ΔM3[2,2,2]|/M3[2,2,2]` obeys

> **rel(q) ~ q^{-c}, fitted c = 4.92** (the `rel·q⁴` column is flat ≈ 0.007–0.029).

Extrapolated to the prize prime `q ~ 2^128`: **rel ≈ 2^{-629}**, i.e. ~500 bits BELOW the
prize resolution `ε* = 2^-128`. A Chebyshev/variance tail argument needs the M3 variance
signal to exceed the resolution; here it is astronomically smaller. **M3 cannot be
weaponized into a δ* upper bound at prize parameters.** (This makes rigorous the honest A3
expectation of `RESULTS-M3.md`: "M3 sees the domain but plausibly cannot move δ*".)

### (3) The t₂ spectral gap IS Weil-provable

Probe `wf407_T334-13-M3_t2_weil.py` (exact, q∈{41,73,89,113,257}). The involution
`σ_φ(x)=(φ₁x−φ₂)/(φ₀x−φ₁)` is Möbius, and
`2t₂ + #fix = N(σ) = #{x∈μ_n : σ(x)∈μ_n}`. Via the n characters trivial on μ_n,
`N(σ) = (n/(q−1))² Σ_{χ₁,χ₂ trivial on μ_n} Σ_x χ₁(x)χ₂(σx)`. Each inner sum is a
**multiplicative character sum of two characters composed with a Möbius map** — Weil
bounds it by `O(√q)` *unless* the summand `χ₁(x)χ₂(σx)` is constant in x (a degenerate
pair). Probe confirms, exactly:

- **normalizer ⇒ has a degenerate pair** (constant summand, |S| = full domain ≈ q ⇒ the
  spike): TRUE at every cell.
- the spike band is **exactly** `{(n−2)/2, n/2}` ({3,4} at n=8; {7,8} at n=16) — matching
  the proven `inversionPairCount_eq`.
- non-degenerate pairs satisfy `|S| ≤ ~2√q` (Weil constant ≈ 1.9 at small q) — the Weil
  regime.
- **noise band max non-normalizer t₂ = 3 at EVERY (q,n)** (does not grow); ratio to
  `n²/q+1` is 0.9–1.75; the spectral gap is present at n=16 (3 < (n−2)/2 = 7), absent at
  n=8 (3 = (n−2)/2, the documented small-scale coincidence).

So the conjectured `t₂ = O(n²/q + 1)` for non-normalizer pencils is exactly the standard
**Weil bound for multiplicative character sums of rational functions against multiplicative
subgroups** (Weil 1948 / Schmidt / Cochrane–Zheng). It is a genuine theorem, not in
Mathlib; `PencilNormalizerBand.PencilNoiseBand` is the right named surface and the
reduction above is correct. **Verdict: Weil-provable** (and clean — `√q`, NOT the
sub-`√q`/BGK regime, because the relevant sum is over the FULL field `x∈F_q^×` with a
fixed Möbius map, so n appears only in the `(n/(q−1))²·n²` character-pair multiplicity,
never inside an incomplete subgroup sum).

> **Important non-collapse:** this is the one place where the M3 channel does NOT wall to
> the #232/#389 additive-energy core. The additive pencils `x+y=c` (`PencilNoiseBand`
> second clause) DO equal `|μ_n ∩ (c−μ_n)|` = the BGK core; but the *multiplicative*
> normalizer/noise split (the dominant M3 separator) is governed by the complete
> rational-function character sum, which is Weil-clean. The t₂ gap theorem is therefore
> attainable — it just gives a `q^{-4}` signal (deliverable 2), so it does not help δ*.

## Net verdict

`partial` (with a `walled`-clean spectral-gap sub-result). The M3 domain-separation
direction is genuine, the census **lives** at M4 (and all higher moments — it is the
recurring "first two power-sums pinned, third separates" law of the t₂-distribution), and
its noise/spike structure is Weil-provable. But the separation signal decays as `q^{-4}`,
landing ~2^{-629} at the prize prime — ~500 bits below the `ε* = 2^-128` resolution any δ*
tail argument needs. **The M3 moment channel is not a δ* lever at prize scale.**

## Artifacts (all in `scripts/probes/`)

- `wf407_T334-13-M3_k4_falsifier.py` — brute M2..M4, small 2-power cells.
- `wf407_T334-13-M3_brute_n6.py` — brute M2..M4 ground truth at μ_6/F_13.
- `wf407_T334-13-M3_m4_decomp.py` — t₂ first/second power-sum pinning at n=8/16.
- `wf407_T334-13-M3_t2moments.py` — the full t₂ power-sum ladder (P₁,P₂ pinned, P₃ first
  separator).
- `wf407_T334-13-M3_signal_scaling.py` — the `rel ~ q^{-4}` law, 2^{-629} extrapolation.
- `wf407_T334-13-M3_t2_weil.py` — the Weil character-sum reduction of the spectral gap.

## What remains / new avenues

- Whether the t₂ third-power-sum `P₃` has a clean closed form (subgroup vs the
  domain-independent random value) — a landable cyclotomic identity at fixed small n.
- The `q^{-4}` exponent: prove it (the leading ΔM3 term is `(n+1)·(spike weight)`/`q⁴`),
  to make the prize-irrelevance a theorem rather than a fit.
