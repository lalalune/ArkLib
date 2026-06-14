# δ* (#407) — the EXACT CONSTANT is gated on the deep-moment wall (value-distribution face)

**Status:** new synthesis + reproducible probes; honest, NOT a closure. Sharpens *which* part of
δ* is open down to the **constant**, corrects a standing KB claim, and kills one hoped-for proof
mechanism. Author: δ* lane (#407), 2026-06-13.

This round independently rediscovered the campaign's three standing reframings of the open core
(confirming they are robust) and then pushed past them on the one axis they had left fuzzy — the
**exact multiplicative constant** in the law `B(μ_n) ≈ C·√(n·log(p/n))`, i.e. the exact constant in
the conjectured pin `δ* = 1−ρ − H(ρ)/(β log n)`.

## 0. Confirmed by independent rediscovery (match the standing KB)
- **Gauss-sum-DFT identity** (`deltastar-salem-zygmund-gausssum-chaining`): re-derived from scratch
  and **numerically verified to 1e-12** (`probe_betascaling_tail_law.py` test C):
  `S_b = (1/m)[−1 + Σ_{j=1}^{m−1} χ̄_j(b)·τ(χ_j)]`, `|τ(χ_j)|=√p`, so the period sequence over the
  coset group `Q=F_p^×/μ_n ≅ ℤ/m` is the **inverse DFT of the Gauss-sum sequence**, and
  `B = (1/m)·‖IDFT(τ(χ_j))‖_∞`.
- **Salem–Zygmund face**: `B` is the sup-norm of a degree-`m` trig polynomial with `m−1`
  flat-modulus (`√p`) coefficients; the prize ⟺ the deterministic Gauss-sum coefficients are
  "Salem–Zygmund-generic". Rigorous bracket from this face alone: `√n ≤ B ≤ √(n·m)=√p`.
- **Definitive wall** (`deltastar-gate-is-sqrt-cancellation-BGK-fullpower-short`): the bound is
  square-root cancellation for incomplete subgroup sums, `n=p^{1/β}≪√p`; best known (di Benedetto
  et al. 2020, `~/papers/arklib/_407/2003.06165.pdf`) is `t^{1−31/2880+o(1)}` — a **full half-power**
  short. The 5-paper scout (`deltastar-407-reading-list`) confirms: no `√(n·polylog)` exists for any
  subgroup family with `t=o(√p)`.

## 1. NEW — the exact constant, and why it is subtle (two different limits)
The conjectured pin `δ* = 1−ρ − H(ρ)/(β log n)` silently uses the **bare-Gaussian** max constant
`C=1` (`B ≈ √(n·log(p/n))` with leading constant 1). We tested this two ways
(`probe_constant_additive_vs_mult.py`, `probe_betascaling_tail_law.py`):

- **Fixed-n, `m=(p−1)/n → ∞`** (NOT the prize regime): the ratio `max|η|²/n / ln m → 1` (n=16:
  1.04 at `ln m=14.3`). Here the subgroup becomes *negligibly thin* relative to `F_p`, its elements'
  additive relations vanish, and the period sums obey an **exact CLT → sharp Gaussian constant 1**.
  **This is the limit the standing `…-salem-zygmund…` §R.3 "sharp constant →1" measurement was in —
  and it is the wrong axis for the prize.**
- **Prize diagonal `m = n^{β−1}`** (β fixed; both `n,m→∞`, `ln m/ln n = β−1`): the subgroup stays a
  *fixed power* of `p`; additive relations never vanish. Multi-prime measurement at β=4
  (`/tmp/diag.py` over `probe_constant_additive_vs_mult` engine, `odd_part>1`, 1–5 primes/point):

  | n | #primes | mean `C=B/√(n ln m)` | spread | `C²` (inflation) |
  |---|---|---|---|---|
  | 16 | 5 | 1.176 | [1.15,1.21] | 1.38 |
  | 32 | 5 | 1.248 | [1.20,1.31] | 1.56 |
  | 64 | 4 | **1.347** | [1.24,1.49] | 1.82 |
  | 128 | 3 | **1.323** | [1.28,1.37] | 1.75 |
  | 256 | 1 | **1.324** | — | 1.75 |

  `C` **rises then PLATEAUS at ≈1.33 (`C²≈1.75`) for `n≥64`** — flat, not growing (the n=16,32 rise
  is finite-size). The FORM survives with a *stable* constant; the **bare-Gaussian constant does not**.

> **Correction to the standing KB:** `B/√(n·log(p/n)) → 1` is true only in the fixed-`n` limit (CLT
> artifact). In the **prize diagonal** the constant **plateaus at `C≈1.33`, `C²≈1.75`** — inflated,
> stable, and notably *above* the proven 4th-moment ratio `3/2` (so deep moments genuinely matter).
> Any "exact" δ* using the bare entropy/Gaussian constant `H(ρ)/β` is off by `C²≈1.75`.

## 2. NEW — the inflation's origin is PROVEN at leading order, and gated on the wall beyond
The value distribution of `S_b/√n` is non-Gaussian (heavier tail) because the Gauss sums `τ(χ_j)`
are correlated via **Hasse–Davenport/Jacobi relations**. The 2r-th moment of the period equals the
`r`-fold additive count of `μ_n` (additive energy at level `r`), so:
- **Leading correction (PROVEN):** the 4th moment ratio is `E₂(μ_n)/2n² = (3n²−3n)/2n² → 3/2`
  (Duke–García `subgroup_gaussSum_fourthMoment`, in-tree). A complex-Gaussian period would give 1;
  the subgroup gives 3/2 — a genuinely heavier tail, the source of `C>1`.
- **All even moments are known:** `E_r(μ_n) = (2r)!·[x^r] I₀(2√x)^{n/2}` (in-tree Bessel even-moment
  law). So the *limiting* value distribution is moment-determined and explicit.
- **But the max-constant needs the FAR tail:** `max` over `m=n^{β−1}` samples probes
  `≈√(2 log m)=√(2(β−1)log n)` standard deviations → needs moments to depth `r ≍ log m`. That is
  **exactly the deep-moment depth `r_max ≈ 2 log_n p` where the char-0/Bessel validity breaks**
  (the BGK/Shkredov wall, `deltastar-389-deep-moment-wall`).

> **Net (the sharpened honest statement):** the prize is one wall **all the way down to the
> constant**. The *form* `√(n log(p/n))` is rigorous-bracketed and empirically pinned; the *exact
> constant* (hence the exact δ*) has a **proven leading inflation `3/2` (4th moment)** but its true
> value is gated on the **same deep-moment / square-root-cancellation wall** as the bound. There is
> no independent closed form for the constant that bypasses the wall.

## 3. NEW (negative) — phase-alignment is NOT a universal descent mechanism
The standing hope ("turn the tower-recursion of the `cos=1.0000` phase alignment into a named
lemma") was tested directly (`probe_tower_alignment_law.py`). The exact recursion is
`F_μ(t)=F_{μ−1}(t)+F_{μ−1}(t·η_μ)`, `η_μ` a primitive `2^μ`-th root, trivial bound `B_M ≤ 2B_{M−1}`.
At the **true maximizer** the per-level child alignment `cos(A,B)`:
- is `+1.000` at most levels for the smaller/structured cofactors (n=32,64,128), BUT
- **degrades to a `±1` mix with near-cancellations** for the most generic cofactor (n=256:
  `cos=−1` at μ=4,2, `|F₄|=0.20`).
So the alignment is a partial structural feature that **washes out toward generic behaviour**, not a
universal tower law. It cannot, as stated, be the non-average descent mechanism a proof would use.
(`n=16` is excluded throughout: my prime-finder hit `p=65537`, a Fermat prime where `p−1=2^16` makes
the field fully dyadic — the forbidden #400 trap; corrected by requiring `odd_part((p−1)/n)>1`.)

## 4. Conjecture ranking (per the #407 rubric — honest)
Sharpened target: **`δ*(RS[n,ρn], q=n^β, ε*) = 1−ρ − (C²·H(ρ))/(β·log₂ n)·(1+o(1))`**, where the
form is rigorous and `C²≈1.7` is the diagonal inflation, with proven leading term from `E₂` ratio.
- **Novelty 7/10** — the three faces pre-exist; the *exact-constant correction* (fixed-n vs diagonal;
  inflation gated on the wall) and the phase-alignment negative are new.
- **Insightfulness 9/10** — unifies the constant question with the deep-moment wall via the value
  distribution; the `3/2` 4th-moment is a proven, concrete handle.
- **Proximity 10/10** — dead-on the prize diagonal `n=2^μ`, large prime, β≈4, ε*=2^−128; explicitly
  excludes the fixed-n / Fermat / full-group artifacts.
- **Feasibility 2/10** — the proof reduces to the BGK square-root-cancellation wall (record is a full
  half-power short, 25-y open). **Fails the 9/10-all-axes bar on feasibility.**

> **The honest verdict the rubric forces:** no closed conjecture that *pins δ\* exactly including the
> constant* and *reduces only to known-proven math* exists, because the constant — not merely the
> bound — is gated on a recognised open problem (square-root cancellation for thin subgroup sums =
> Gauss-sum-phase Salem–Zygmund = generalized-Paley almost-Ramanujan). The contract holds: **not
> fabricated.** What *is* delivered closed: the rigorous bracket `√n ≤ B ≤ √p`, the exact
> Gauss-sum-DFT identity (verified), the proven `3/2` leading inflation, and the precise location of
> the residual.

## 5. Reproduce
- `scripts/probes/probe_tower_alignment_law.py` — true maximizer + per-level alignment trace.
- `scripts/probes/probe_betascaling_tail_law.py` — B² vs log(p/n), tail exponent, Gauss-sum identity (1e-12).
- `scripts/probes/probe_constant_additive_vs_mult.py` — fixed-n additive(sharp) vs diagonal(inflated).
- Papers: `~/papers/arklib/_407/` (5 PDFs); list in `deltastar-407-reading-list-2026-06-13.md`.
