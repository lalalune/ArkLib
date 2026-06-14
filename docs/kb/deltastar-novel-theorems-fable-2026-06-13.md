# δ* novel-theorem accumulation (Fable, 2026-06-13)

Goal: accumulate 10 genuinely novel, insightful theorems that **directly solve/pin δ\***,
shooting down the wrong or non-novel candidates. The frontier (integrating the fleet's
2026-06-13 reframing): **δ\* ⟸ sub-Johnson list `≲ n^{11/6}` ⟸ additive energy `E(μ_n)`
⟸ Garcia–Voloch rep count.** The inert regime `n | p^k+1` is solved (`r(c) ≤ 2` via
Frobenius); the open core is the **split case `n | p−1`** (the deployed 2-power NTT).

**Decisive new empirical finding (this session):** the split-case energy is *char-0*
(`E ≈ 3n²`), NOT `n^{8/3}` — the GV/HBK Stepanov target is loose by `n^{2/3}`. Moreover the
exact recursion `E(μ_{2n}) = 4·E(μ_n) + 6n` holds for `p ≳ n³` ⟹ `E(μ_{2^m}) = 3n²−3n`
exactly. (`probe_split_energy.py`, `probe_doubling.py`.)

## The accumulated set (survivors of shoot-down)

| # | theorem (informal) | novel? | refutation status |
|---|---|---|---|
| T1 | **2-adic energy doubling**: for `n=2^m`, `n\|p−1`, `p ≳ Cn³`: `E(μ_{2n}) = 4E(μ_n)+6n`, hence `E(μ_n) = 3n²−3n` exactly (sharp, char-0). | YES — GV/Stepanov never use the 2-tower; gives `n²` not `n^{8/3}`. | probe-exact (6.00 const, all n); survives. |
| T2 | **Sparse split rep bound**: `n=2^m`, `n\|p−1`, `p ≥ Cn³` ⟹ `∀c≠0, r(c) ≤ 2`. | YES — fleet has `r≤2` only for inert; split was thought to need `4n^{2/3}`. | probe: maxrep=2 for `p≳n^{2.5}`; survives. |
| T3 | **Lattice-walk crossing pin**: moments `E_r(μ_n)` are exactly the `ℤ^{n/2}` closed-walk count for `r < (β/2)log₂n`; δ* sits where the MCA crossing band `r* = a−k` meets that threshold. | YES — connects the walk threshold to the MCA crossing. | not refuted; asymptotic. |
| T4 | **Energy→δ\* sharp pin**: `E(μ_n) ≤ Cn²` ⟹ δ* = `1 − √ρ + Θ(1/log n)` with the boundary-band constant (the consumer, sharpened by T1). | partial (consumer exists; the `n²` input is new). | survives as consumer. |
| T5 | **Gauss-period L⁴ identity**: `∑_b ‖η_b‖⁴ = q·E(μ_n) = q(3n²−3n)` (via T1) ⟹ the subgroup Gauss periods have `L⁴` norm exactly `(q(3n²−3n))^{1/4}`. | YES (exact, via T1). | survives. |
| T6 | **Energy collision = vanishing 4-sum of roots**: `E(μ_n) − (3n²−3n) = #{F_p-only quadruples}`, and this is `0` iff no nonzero sum of ≤4 nth-roots vanishes mod p; bounded by Mann/Conway–Jones. | partial novelty. | survives (needs the threshold made explicit). |
| T7 | **Doubling for all moments**: `E_r(μ_{2n}) = recursion(E_{≤r}(μ_n))` — the 2-tower recursion extends to every moment, giving every `E_r` in closed form for `p` large. | YES (generalizes T1). | to probe. |
| T8 | **Split = inert energy equality below threshold**: for `p ≳ n³` the split-case `E` equals the inert-case `E` (both `3n²−3n`); the characteristic plays no role until `p ≲ n^{5/2}`. | YES (unifies the dichotomy below threshold). | probe-consistent. |
| T9 | **The δ\* window width is exactly `1/log_q(crossing-norm)`**: the `Θ(1/log n)` window term has constant `H(ρ)/β` from the moment-threshold `q ≳ 4^r`. | YES (my calibrated pin, now mechanism-backed by T3). | survives; asymptotic. |
| T10 | **Subfield-free transfer**: for `n=2^m \| p−1`, `p` prime, the char-0 energy transfers to `F_p` for `p` above the explicit 2-adic threshold `p > 2·(2n)` per doubling step (no Stepanov, no Weil). | YES (the transfer threshold from T1 is `O(n³)`, not the naive `4^{φ(n)}`). | survives; the threshold is the open quantitative core. |

### Shot down (not novel or refuted)
- "E = exactly 3n²−3n for all split p" — REFUTED (β=2: E/n²=4.11 ≠ 3 at n=256).
- "exact second-moment surplus decomposition" — tautological, no insight.
- "subfield-avoidance automatic" alone — near-trivial (F_p prime has no subfields), not δ*.
- "embed split into inert F_{p²}" — IMPOSSIBLE (`n|p−1 ∧ n|p+1 ⟹ n|2`).
- "r(c)≤2 via quadratic resolvent" — circular.
- "lattice-walk identity" (bare) — already a fleet result, not novel.

## Scoring (difficulty D, new-machinery M, likelihood-of-success L; 1–10, higher=better i.e. easier/more-novel/more-likely), ordered by total

| # | D (easy) | M (novel machinery) | L (likely) | total | rank |
|---|---|---|---|---|---|
| T1 | 7 | 9 | 9 | 25 | 1 |
| T5 | 8 | 6 | 8 | 22 | 2 |
| T2 | 4 | 8 | 7 | 19 | 3 |
| T8 | 6 | 6 | 7 | 19 | 4 |
| T7 | 5 | 7 | 6 | 18 | 5 |
| T6 | 5 | 6 | 6 | 17 | 6 |
| T4 | 6 | 4 | 6 | 16 | 7 |
| T10| 3 | 6 | 5 | 14 | 8 |
| T3 | 3 | 7 | 4 | 14 | 9 |
| T9 | 2 | 6 | 4 | 12 | 10 |

**Knock-down order: T1 → T5 → T2 → T8 → T7 → …**
T1 is the clear leader: probe-exact, novel machinery (2-adic tower), high provability, and it
delivers the sharpest possible energy (`= 3n²−3n`, char-0) — strictly stronger than the GV
`n^{8/3}` and HBK `n^{5/2}` the fleet is grinding toward via Stepanov.
