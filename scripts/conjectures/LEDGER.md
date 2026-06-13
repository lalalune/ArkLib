# Novel Conjecture Ledger (#389 adjacent) — survivors through refute/survive

All statements are about **computable** structural quantities of the 2-power multiplicative
subgroup `μ_n ⊆ F_p` (`n = 2^m`) in the no-genuine-relation regime (`p` large vs `n`). They are
**decidable in principle** (finite computation per instance), so they do NOT reduce to the
past-Johnson barrier — the swarm can prove or disprove each in Lean. Each is a CONJECTURE
(empirically survived at the listed scales), not a theorem. Engine: `scripts/conjectures/`.

## Survivors (empirically verified, fit-then-confirmed on independent larger instances)

| id | statement | verified at | novelty |
|----|-----------|-------------|---------|
| C2  | `E_3(μ_n) = 15n³ − 45n² + 40n` (6th additive moment) | n=2,4,8,16; **conf n=32** | NOVEL |
| C3  | `|μ_n + μ_n| = n²/2 + 1` (sumset size) | n=2..32 | NOVEL |
| C5  | `|μ_n − μ_n| = n²/2 + 1` (difference set size) | n=2..32 | NOVEL |
| C6  | `#{(a,b)∈μ_n² : a+b ∈ μ_n} = 0` for n≥4 | n=4..32 | NOVEL |
| C7  | `Z_3(μ_{2^m}) = 0` (3-term zero-sums vanish) | n=2..32 | NOVEL |
| C8  | `E_4(μ_n) = 105n⁴ − 630n³ + 1435n² − 1155n` (8th moment) | n=2,4,8,16; **conf n=32** | NOVEL |
| C9  | **leading coeff of `E_r(μ_n)` is `(2r−1)!!`** (3,15,105…) | r=2,3,4 | NOVEL (general) |
| C10 | `Z_4(μ_n) = 3n² − 3n = E_2` (negation identity `r(−v)=r(v)`) | n=2..32 | NOVEL |
| C11 | `Z_{2j+1}(μ_{2^m}) = 0` (all odd-length zero-sums vanish) | j: 1,2,3 × n=2..16 | NOVEL |
| C12 | `#{t≠0 : |μ_n ∩ (μ_n−t)| = 2} = (n²−2n)/2` | n=4..32 | NOVEL |
| C13 | `#{t≠0 : |μ_n ∩ (μ_n−t)| = 1} = n` (the `2a`-translates) | n=4..32 | NOVEL |
| C14 | **subleading coeff of `E_r` is `−(2r−1)!!·C(r,2)`** (−3,−45,−630) | r=2,3,4 | NOVEL (general) |
| Cmeta | `E_2(μ_n) > 3n²−3n` iff `p < n²` (no-4-term-relation threshold `~n²`) | n=8..64 | NOVEL (threshold) |

## Deaths (honestly refuted)
- C2-orig `E_3 = 15n³−45n²+31n` — refuted (E_3(2)=20≠2); corrected to C2 above.
- C9-orig (finite-ratio test) — test artifact; corrected via clean polynomial fit (now C9 survives).
- C10-orig `Z_4=3n²−2n` — refuted (Z_4(2)=6); corrected to `3n²−3n` (= E_2).
- E_4 naive fit (small prime) — refuted at n=64; revealed the `p > n^r` threshold (→ Cmeta).

## Structural pattern (open meta-conjecture)
`E_r(μ_n) = (2r−1)!!·n^r − (2r−1)!!·C(r,2)·n^{r−1} + … ` — a degree-`r` integer polynomial whose
top two coefficients are pinned by C9, C14; the full coefficient sequence is the next target.
