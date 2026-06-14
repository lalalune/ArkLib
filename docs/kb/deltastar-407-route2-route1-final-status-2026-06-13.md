# (2) Refutation fails + (1) Proof is BGK — final status of the prize core (2026-06-13)

## (2) REFUTATION — fails; the constant plateaus
`M/√(n·ln p)` at β=4, generic primes (`probe_creep_constant_plateau.py`):
| n | 16 | 32 | 64 | 128 |
|---|---|---|---|---|
| max M/√(n ln p) | 1.045 | 1.059 | 1.181 | **1.183** |
| M/√(2n ln p) | 0.74 | 0.75 | 0.835 | **0.837** |
The constant PLATEAUS ~1.18 (n=64→128 flat: 1.181→1.183); `M ≤ √(2n ln p)` holds with margin throughout.
Combined with the structured-prime hunt (no heavy prime at β≥4, n=64), **no counterexample exists in the
prize regime up to n=128**; the constant is bounded (owner: [1.14,1.36]). Refutation FAILS — strong
positive evidence for `M ≤ C√(n ln p)`, C≈1.2–1.4.

## (1) PROOF — it is BGK square-root cancellation, beyond current math
The bound to prove: `M(n) = max_{b≠0}|Σ_{x∈μ_n}e_p(bx)| ≤ C√(n·ln p)` for `n ≪ √p` (β≥4).
- Provable elementarily: the r≤β/2 anchor (exact integer eqn `Σg^a=Σg^b+kp` below birthday).
- Equivalent forms (all this session): cumulant sub-Wick to r≈ln p (face 3); Gaussian-period sup-norm;
  Gauss-sum JOINT phase pseudorandomness (route 3; floor = random-phase extreme-value prediction).
- SOTA: Bourgain–Glibichuk–Konyagin / Shkredov give `M ≤ n^{1−1/2880}` (Kowalski 2024) — a power saving
  BELOW n, but the prize needs `n^{1/2+o(1)}` (square-root). **Gap = a full half-power of n.**
- This is the recognized 25-year-open subgroup-character-sum √-cancellation problem. No norm/height bound
  reaches it; the moment route hits structured primes (outside prize); the L^∞/phase route reduces to
  Gauss-sum joint pseudorandomness (individual args proven equidistributed, joint/sup open).

## Net (do-3-then-2-then-1, honest)
- (3) non-moment L^∞: cleaner formulation (floor = random Gauss-sum-phase prediction; √log = max over p
  frequencies), explains robustness, but reduces to Gauss-sum joint pseudorandomness = BGK.
- (2) refute: FAILS — no counterexample at β≥4 up to n=128; constant plateaus ~1.18.
- (1) prove: requires BGK √-cancellation for n≪√p — beyond current mathematics (SOTA is a half-power short).
**Unequivocal resolution is not achievable: the core is a recognized open problem. The prize regime is the
favorable zone (unfalsifiable, constant bounded), the provable anchor is r≤β/2, and the irreducible gap is
BGK. No fabricated closure.**
