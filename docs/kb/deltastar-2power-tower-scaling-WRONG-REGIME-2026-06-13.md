# Negative: 2-power tower B-scaling shows √-cancellation but ONLY in the accessible n≲√p (easy) regime (2026-06-13)

Tried the one structural angle specific to the prize's actual domain `μ_{2^k}` that the general BGK
bound ignores: the recursive square-root tower. Measured `B(μ_{2^k}) = max_{b≠0}|η_b|` at a FIXED prime
`p=301057` (ln p=12.62, `p−1` divisible by `2^9`), `k=1..9` (`scripts/probes/probe_2power_tower_scaling.py`):

| k | n | B | B/√n | exp = log B/log n |
|---|---|---|---|---|
| 4 | 16 | 14.08 | 3.52 | 0.954 |
| 6 | 64 | 33.51 | **4.19 (peak)** | 0.844 |
| 9 | 512 | 79.10 | 3.50 (↓) | 0.701 |

`B/√n` peaks at k=6 then DECREASES; exponent trends 1.0 → 0.70 → (toward 0.5). Clean **square-root
scaling `B ~ √(n·log p)`** — consistent with the prize target.

## Why this is NOT evidence for the prize (honest)
The reachable range is `n ≲ √p` (at k=9, `n=512 ≈ √p=549`). That is the **EASY regime**: the Gauss-sum
baseline `|η_b| ≤ √p` (Kowalski 2401.04756 p.2: "non-trivial for |H| a bit larger than √p") already
gives cancellation there. The prize is `n ≪ √p` (`n=p^{0.156}`), computationally unreachable
(`b∈[1,p]` with `p≈2^192`). The tower gives **no regime-independent recursion** transferring the
measured `√`-cancellation down to `n≪√p`. So "extrapolate the 2-power tower" is **refuted as a route** —
the only regime where I can see √-cancellation is the one that was never open.

## Standing conclusion (unchanged)
The gate (square-root cancellation for `n=p^γ`, `γ<1/2`) remains open and computationally + analytically
inaccessible in the prize regime; the 2-power structure does not provide a shortcut. No closure claimed.
