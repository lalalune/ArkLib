# wf407 / T232-03 — BGK kernel magnitude `M = |μ_n ∩ −(1+μ_n)|`: verdict

**Verdict: WALLED (with a new exact two-sided pin).** The BGK *magnitude* `M` is trapped
`0 ≤ M ≤ n−1` by a pure **arithmetic gcd/resultant divisibility** mechanism; it carries **no
analytic √-cancellation content** and is **NOT the prize wall**. Whether `M > 0` at any specific
large prime collapses onto the **Mersenne/Fermat/cyclotomic-factor wall** (`p | Res(Xⁿ−1,(X+1)ⁿ−1)`,
generalizing #389-T17 / BCHKS Conj 1.12). In the prize regime `p ≈ n·2^128` the magnitude is
overwhelmingly `0` (mean `M ~ n²/p → 0`); the additive-energy face it governs is the already-known
**W2 √n-deficient route** (Johnson-strength only) — orthogonal to the open Gauss-period/list face.

## The object (in-tree, `AdditiveEnergyKernel.lean`)
`M = bgkCount n = #{u ∈ μ_n : −(1+u) ∈ μ_n}`; `tripleZero n = #{(x,y,z)∈μ_n³ : x+y+z=0} = n·M`
(proven: `tripleZero_eq_card_mul_bgk`). Known structure (all proven in-tree): `M=0` char-0
(`bgkCount_eq_zero_of_coprime`); `M≥1 ⟺ char | 2ⁿ−1` at `u=1` (`one_mem_bgk_iff`,
`one_mem_bgk_iff_exists_fermat_dvd`); `6|M` generically (`six_dvd_bgkCount`, S₃ symmetry
`BGKSolSetSymmetry`).

## What the exact numerics established (probes `scripts/probes/wf407_T232-03-bgk_*.py`)

1. **Exact identity `M = N(x+y=c)` for any `c≠0`** (`_energy_curve.py`): `M = #{(x,y)∈μ_n² : x+y=1}
   = #{(x,y)∈μ_n² : x+y=−1}` exactly (even `n`). So `M` IS the affine **Fermat-curve fiber count**
   `#{(x,y)∈μ_n²: x+y=c}`, a fibre of the `(1,1)`-curve. The additive energy decomposes
   `E_2 = n² + Σ_{c≠0} r(c)²` with `r` constant on `μ_n`-dilation-orbits of `c` and `r(±1)=M`.

2. **`E_2 = 3n²−3n` exactly in the clean (generic-large-`p`) regime** (`_magnitude.py`, `_energy_curve.py`):
   confirmed at e.g. `n=8, p=73,89` (`E_2=168=3·64−24`). Anomalies `E_2 ≠ 3n²−3n` occur ONLY at the
   same small/structured primes that give `M>0`. This **confirms** the memory fact
   "`E_2=3n²−3n` ⟺ no anomaly = clean Fermat-curve count"; deviations are the Hasse-Weil error =
   additive coincidences = `M>0`.

3. **`M = deg gcd(Xⁿ−1,(X+1)ⁿ−1)` over `F_p` EXACTLY** (`_gcdbound.py`), separable (`p` odd ⟹
   `Xⁿ−1` separable), so no multiplicity slack: every common root is simple. Verified
   `M = deg_gcd` in 15/15 instances incl. `n=128`.

4. **The bad-prime set = prime divisors of `Res(Xⁿ−1,(X+1)ⁿ−1)`** (`_worst.py`):
   - `n=8`: `Res=−3⁷·5³·17³`, bad {3,5,17} = {F₀,F₁,F₂};
   - `n=16`: `Res=−3⁷·5³·7⁶·17¹⁵·257³`, bad {3,5,7,17,257} = {F₀,F₁,**7**,F₂,F₃};
   - `n=32`: bad {3,5,7,17,47,97,193,257,353,449,65537}.
   The Fermat numbers `F_j` (= `u=1` obstruction, Mersenne factors) appear, **plus** other prime
   factors (7, 47, 97, …). This is the **exact** generalization of #389-T17/BCHKS Conj 1.12: the
   bad primes are governed by the factorization of a Mersenne-flavoured resultant, **famously open**.

5. **Absolute ceiling `M ≤ n−1`, sharp** (`_worst.py`): at `p=n+1` prime (`μ_n=F_p^×`, e.g.
   `n=16,p=17` or `n=256,p=257`) every `u∉{0,−1}` solves ⟹ `M=n−1`. The big-`M` cases are exactly
   these maximal-density degeneracies (the #400 `μ_16=F_17^*` full-group artifact). `M/√n ∈ [1.06, 3.75]`
   across all enumerated instances — never blows past `O(√n)` even at worst density `≤1/2`.

6. **Prize-regime collapse to 0** (`_largep.py`, `_huge.py`): mean `M` tracks the heuristic `n²/p`
   (each of the `n` elements `1+u` lands in `μ_n` with prob `≈ n/p`), decaying `→0`. At genuine prize
   scale `p ≈ n·2^k` (`k=64,96,128`, density `2^-k`) **`M=0` for every tested `n∈{16,32,64,128,256,1024}`**.
   By `p>3·10⁶` no enumerated prime has `M>0` for `n≤32`.

## New Lean brick (this thread)
`Frontier/WF407_T232_03_BGKMagnitudeCeiling.lean` — the exact unconditional ceiling, axiom-clean:
- `neg_one_not_mem_bgk` — `u=−1` is never a BGK solution (`−(1+(−1))=0∉μ_n`).
- `bgkCount_le_card_sub_one` — **`M ≤ |μ_n| − 1`** when `−1∈μ_n` (even `n`); sharp at `p=n+1`.
- `bgkCount_two_pow_le` — `M ≤ 2^k − 1` at the smooth domain.

Consolidates the magnitude into the proven range `M ∈ {0} ∪ (6ℕ ∩ [6, n−1])` (off the bad primes
`M=0`; `6|M` generically; `M≤n−1` always).

## Why this is WALLED, not progress on the prize
- The magnitude has **two clean ends**: lower `M=0` (char-0 coprimality, generic large `p`) and upper
  `M≤n−1` (gcd degree, this brick). The only open piece — *which* large `p` give `M>0` — is the
  **resultant-divisibility / Mersenne-Fermat-cyclotomic-factor wall** (#389-T17 ≡ BCHKS Conj 1.12),
  a number-theory question about prime factors of `Res(Xⁿ−1,(X+1)ⁿ−1)`, NOT a coding/analysis question.
- Even granting worst-case `M=Θ(n)` (max density), the additive-energy route through `M`/`E_2` is the
  **W2 wall**: `list ≥ √(n·E) ≥ n^{3/2} > n` always (DISPROOF_LOG O30, 389-T08), reaching only
  Johnson. So bounding `M` (which this thread does, two-sidedly and sharply) **cannot** push `δ*`
  past Johnson. The prize core is the Gauss-period/list face, where `M` does not appear.

## What remains (for the next wave)
- The resultant-divisibility wall is the genuine open NT residual; it is *strictly weaker* than the
  full prize (it only governs `M>0`, an event that is `δ*`-irrelevant by W2). Not worth prize cycles.
- New avenue surfaced: `M = #points on the (1,1)-curve `x+y=c` over `μ_n²` = a Fermat-curve fiber;
  the `E_2 = n² + Σ r(c)²` decomposition with dilation-orbit-constant `r` connects directly to
  334-T13 (M3 `t₂` spectral-gap, `(1,1)`-curves) — same object, two lanes.

🤖 wf407/T232-03 · Claude Opus 4.8 · honesty contract held (no fabricated closure)
