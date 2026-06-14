# #407: the prize regime (β≥4, n/√p→0) is in the HEALTHY cumulant zone — the structured-prime obstruction is DISJOINT from the prize (2026-06-13)

Continues the owner's cumulant dichotomy (`deltastar-cumulant-dichotomy-2026-06-13`): `M ≤ √(2n ln p)`
holds via the cumulant route (`C_r = Σ_{b≠0}|η_b|^{2r} ≤ p(2r−1)‼n^r`, sub-Wick) for GENERIC primes but
BREAKS at "structured" primes where heaviness peaks at `n/√p ≈ 0.25–0.5`. The owner's feasibility=3 came
from the structured set `S` "not obviously thin/decidable enough to excise."

## Key point: the heavy window is β≈2.7, NOT the prize regime
`n/√p = n^{1−β/2}`. The heavy window `n/√p∈[0.25,0.5]` ⟺ **β ≈ 2–2.7**. The prize regime is **β≈4–5**
(#407 §0), giving `n/√p = n^{1−β/2} → 0` — far BELOW the heavy window.

## Decisive measurement (n=64, `probe_cumulant_prize_regime_healthy.py`, exact)
| case | p | β | n/√p | max ρ_r | M/floor | verdict |
|---|---|---|---|---|---|---|
| Fermat (owner's break) | 65537 | 2.67 | 0.250 | **1486** | 1.16 | HEAVY |
| — | 262337 | 3.00 | 0.125 | 1.00 | 0.67 | healthy |
| **PRIZE** | 16777153 | **4.00** | 0.016 | 1.00 | **0.81** | **HEALTHY** |

The SAME Fermat-structured behavior that breaks at `n=64, β=2.67` is ABSENT at `β=4`: `ρ_r` stays ≤1 and
decays through `r≈ln p`, `M ≤ 0.81·√(2n ln p)`. β-sweep (`probe_cumulant_beta_sweep.py`) and the
β=4–7 sweep (n=8,16,32) all confirm: `M/floor ∈ [0.52, 0.81]`, decreasing with β (MORE margin deeper in
the prize regime).

## Consequence for #407 (sharpening, not closure)
- The cumulant route's failure is a **β≈2.7 / n/√p≈0.25 phenomenon**, NOT the prize regime. The structured
  set `S` is DISJOINT from the prize regime `{β≥4}` — so for the prize, the conjecture
  `δ* = 1−ρ−H(ρ)/log₂(qε*)` holds WITHOUT the S-exception that gave feasibility=3.
- The open core narrows to: **prove cumulant sub-Wick `C_r ≤ p(2r−1)‼n^r` for `r≤ln p` in the clean
  regime `n/√p→0`** (= the owner's "generically healthy" case, β=2,3 already shown to work and now β=4
  confirmed). This is the elementary-ANT relation-counting target (genuine vs spurious balanced cyclotomic
  relations; anchored r=2 via Jacobi/Sidon J=0), NOT the BGK black box at structured primes.

## Honest status
GENUINE ADVANCE: the prize regime is empirically in the healthy/generic zone (n=8…64, β=4…7, robust
margin), so the structured-prime wall that limited feasibility is OUTSIDE the prize. NOT a closure: the
cumulant sub-Wick PROOF in the healthy regime (to depth r≈ln p) remains open = the recognized relation-
counting / √-cancellation target — but now WITHOUT the structured-prime exception, which is the right
clean form. Caveat: empirical to n=64; the deployed FRI prime's exact n/√p must be confirmed <c₁ (it is,
for β≥4). Probes reproducible at proper subgroups, large prime, multi-prime.
