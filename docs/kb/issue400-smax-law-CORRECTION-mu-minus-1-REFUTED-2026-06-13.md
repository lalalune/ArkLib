# CORRECTION: s_max=μ−1 is REFUTED at n=64 (s_max≥6); the decomposition + P(ζ)²=P(ζ²) reform STAND (2026-06-13)

**Retraction.** The prior note `issue400-smax-law-mu-minus-1-deltastar-staircase` claimed the closed law
`s_max(μ_{2^μ}) = μ−1`, verified at n=8,16,32 (→2,3,4). **This law is FALSE.** Pushed it prematurely
(verified only to n=32); the very next data point breaks it:

| n | μ | s_max | μ−1 |
|---|---|---|---|
| 8 | 3 | 2 | 2 |
| 16 | 4 | 3 | 3 |
| 32 | 5 | **4** (s=5,6 fail) | 4 |
| 64 | 6 | **≥ 6** | 5 ✗ |

The `n=64, s=6` config is INDEPENDENTLY verified (`probe_smax_verify_n64.py`): A has 6 singles,
`valid_fast=True` AND `P(ζ)²=P(ζ²)` poly-check `=True`. So `s_max(64) ≥ 6 > μ−1=5`. The sequence
`2,3,4,≥6` is NOT `μ−1` (jumps by ≥2 from n=32→64). The companion "single classes have distinct
2-adic valuations" hypothesis is ALSO refuted (104 violations at n=16). **No closed s_max law is known.**

## What SURVIVES (independently verified, solid)
1. **Decomposition theorem:** `e_1(A) = Σ_{singles} ±ζ^j` (full antipodal pairs cancel). #bad=Θ(n^{s_max}).
2. **Algebraic reformulation (VERIFIED, 50626 cases, 0 mismatches):** `e_2(S)=0 ⟺ P(ζ)² = P(ζ²)`,
   where P = 0/1 indicator polynomial of A. Equivalently (singles form): the signed pairwise-single-sum
   equals the sum of full-pair squares in ℤ[μ_{n/2}]. This is a clean "exact freshman's-dream" condition.
3. **Exact balance criterion** (full pairs hit even positions bijectively; valid ⟺ D_HH=0 on odd,
   |D_HH|≤1 on even) — validated against full enumeration at n=8,16.
4. **#400's O(n) is still refuted** (s_max≥3).

## What is RETRACTED
- The closed law `s_max=μ−1` (false at n=64).
- The "distinct 2-adic valuations" structural claim (false at n=16).

## The δ* staircase CONCEPT survives but is NOT closed
`δ* = band where per-band s_max crosses log_n(ε*q)` remains a valid q-independent REFRAMING — it does not
depend on the (wrong) global law. But without a closed s_max law, this is not a closure. **s_max grows
faster than μ−1** (≥6 at n=64), so #bad=Θ(n^{s_max}) for the near-capacity direction is at least
n^{≥6} there — even larger than the μ−1 estimate. The exact per-band s_max function is open.

**Honest status:** the structural decomposition and the P(ζ)²=P(ζ²) reformulation are real, verified
contributions. The s_max=μ−1 LAW was wrong and is retracted. The δ* staircase is a reframing, not a
closure. Lesson: do not commit a "closed law" verified at only 3 points — the 4th broke it.
