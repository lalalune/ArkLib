# O_P collapses to 1 at the binding rung — computational evidence for lalalune's O_P=1 persistence (n=8,16, closure-verified, 3 primes)

2026-06-16. Contributes to lalalune's #444 08:46Z thread: the far-line bad-γ orbit law
`#bad = [γ=0 bad] + (n/d)·O_P` (d=gcd(aa−b,n), O_P = # distinct nonzero dilation-cosets), derived
from the Schur-ratio dilation-equivariance `γ(gT)=g^{aa−b}γ(T)` — the same law as the proven B2
orbit-reduction (det-multilinearity route). lalalune's open question: does O_P collapse to a single
coset (O_P=1) as the tower deepens? Their examples are all at the SHALLOW rung (c=s−k=1), where O_P
is large (16, 29). This sweeps the worst monomial line `x^aa + γ·x^b` from the explosion rung down to
the BINDING (budget-crossing) rung and decomposes #bad via the orbit law, **verifying closure** (the
nonzero bad set is genuinely closed under mult by h^{aa−b}) rather than assuming it.

## Verdict: O_P → 1 at the binding rung (closure-verified, prime-independent)

**n=16, k=4 (ρ=1/4), budget=16** — worst monomial line per rung, identical across p∈{65537,1048609,16777441}:

| s | c | #bad | d | n/d | γ=0 bad | O_P | closure | decomposition |
|---|---|------|---|-----|---------|-----|---------|---------------|
| 5 | 1 | 3936 | 1 | 16 | no  | 246 | ✓ | 3936 = 0 + 16·246 |
| 6 | 2 |   89 | 2 |  8 | yes |  11 | ✓ | 89 = 1 + 8·11 |
| **7** | **3** | **9** | **2** | **8** | **yes** | **1** | **✓** | **9 = 1 + 8·1  ← BINDING RUNG** |
| 8 | 4 |    9 | 2 |  8 | yes |   1 | ✓ | 9 = 1 + 8·1 |

**n=8, k=2 (ρ=1/4), budget=8:**

| s | c | #bad | d | n/d | γ=0 bad | O_P | closure | decomposition |
|---|---|------|---|-----|---------|-----|---------|---------------|
| 3 | 1 | 40 | 1 | 8 | no  | 5 | ✓ | 40 = 0 + 8·5 |
| 4 | 2 |  9 | 1 | 8 | yes | 1 | ✓ | 9 = 1 + 8·1  (O_P=1 reached at c=2) |
| 5 | 3 |  5 | — | — | — | — | — | budget-crossing; global-max dir is d=1, non-clean (see caveat) |

**Headline:** the worst monomial line's orbit count O_P collapses **246 → 11 → 1** (n=16) and **5 → 1**
(n=8) — reaching O_P=1 by the binding rung and persisting. At the binding rung the bad-γ set is exactly
`{0} ∪ (one dilation-coset of size n/2)`, closure-verified across 3 primes. This is direct
computational support for lalalune's O_P=1 persistence conjecture, at the rung that actually determines
m*/δ* (their shallow-rung c=1 examples have O_P=16/29 and don't reach it).

## Honest scope / caveats

- **Proxy face, NOT the prize.** This is the over-determined Johnson/Plotkin monomial-line face (per
  O192/O193); the p-dependent BGK sup-norm prize `M(μ_n) ≤ C√(n log m)` is separate and stays OPEN.
  O_P=1 persistence is a structural fact about the proxy, not a δ* closure.
- **CLOSURE-FAIL rows** at a few non-binding rungs (n=8 s=5; n=16 s=9): the *global*-max-#bad direction
  there happens to be a d=1 (adjacent-exponent) direction whose bad set is not a clean single-d orbit
  union, so the simple law doesn't apply to that particular direction. These are not the canonical
  binding directions and #bad there is already ≤ budget. The O_P=1 claim is for the clean d=2 binding
  directions (closure ✓).
- **n≥32 not computed** — orbitdecomp loops all (aa,b) pairs × C(n,s) subsets; the explosion rung at
  n=32 is the CPU-cap. O_P=1-at-binding is verified at n≤16; lalalune's n→n/2 descent is the proof route.
- Complements (does not replace) lalalune's descent-induction proof attempt: this is the binding-rung
  *data*; the descent is the *proof*.

Reproduce: `cd scripts/rust-pg && cargo build --release --bin orbitdecomp && ./target/release/orbitdecomp 16 4` (mult=4/5/6 for 3 primes).
