# Energy transfer ≠ supply transfer: the n^2.3 threshold does NOT close the supply wall at production

2026-06-13. Cross-check (Opus 4.8, adversarially verified, confidence 0.9, 0 fatal/major;
independent re-computation of all 50 measured α-norms, 0 `p|N(α)` violations). **No overclaim
found — moon's energy result is correctly scoped to energy.** This note documents the
distinction so the clean energy transfer is not later mis-applied to the marginal-supply Prop.

## Two different quantities, two different transfer thresholds

| | quantity | char-0 value | transfer threshold | shape |
|---|---|---|---|---|
| **Energy** (moon, #389 `19b77bfdc` + `E(μ_n)=3n(n−1)` theorems) | `#{(a,b,c,d)∈μ_n⁴ : a+b=c+d}` | `3n(n−1)` | `p ≳ n^2.3` (= 2^13.8 at n=64) | **polynomial** |
| **Codeword-supply** (my falsifier O134/O135) | `#` agree-exactly-`(s+1)` marginal codewords | 764,544 (r=3) / 99,512 (r=5) | `p > max N(α)` over the bad α-lattice | **super-polynomial**, exponent `n/2` |

- The supply surplus is caused by `p | N(α)` for bad lattice vectors `α ∈ ℤ[ζ_n]` (the
  marginal-config difference, L1 norm 12–20, degree φ(n)=32 at n=64). Independently
  recomputed via exact Bareiss determinant of mult-by-α mod `x^32+1`, cross-checked against
  the complex conjugate product: **every measured bad α has `p | N(α)`, 0 violations across
  50 distinct α; realised `|N|` ∈ [2^41.5, 2^66.90]**.
- The super-polynomial exponent (`n/2`) is the ArkLib tree's own formalized law
  `FoldedSumThreshold.foldedSum_vanishing_iff_char0`: threshold `(2^(m−1)·L1)^(2^(m−1))`,
  `n = 2^m`. Energy's exponent is a constant (~2.3); supply's grows like `n/2`.

## The decision-relevant consequence for #389

**BabyBear (2^30.9) and p2 (2^31.6) sit ABOVE the energy threshold but BELOW the supply
norms** — so the split-case energy IS exactly char-0 there, while the supply count is NOT:
**+33,453 (+33.6%) / +16,941 (+17.0%) spurious marginal codewords at r=5** [measured,
exhaustive]. Even Goldilocks (2^64) is exceeded by the highest-norm tail (2 of 25 sampled
p2 r=5 α at 2^66.90 > 2^64; it does transfer the bulk 2^41..2^63).

So: **the clean energy transfer is NECESSARY but NOT SUFFICIENT for the supply transfer.**
Any per-prime supply statement at production must carry the norm-divisibility correction
(char-0 count + `p|N(α)` surplus); the energy route does not by itself close the supply wall
at production scale. (Per-prime placement rests on the MEASURED realised norms 2^41..2^66.90,
not the conservative formula bound 2^274, which only fixes the exponent shape.)

Reproduce: `falsifier/norms.py`, `falsifier/crosscheck.py` (exact ℤ[ζ_64] norms).
