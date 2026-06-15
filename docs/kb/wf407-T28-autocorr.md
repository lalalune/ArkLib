# wf407 / T28-autocorr — char-p autocorrelation recursion `E_{r+1}=n·E_r+cross_r`

**Verdict: WALLED** (to the W4 / B-form Gauss-period wall) — with the recursion + free-deep-tail
already landed axiom-clean, and the part-(2)/(3) "sub-trivial cross decay" hope **REFUTED by exact
numerics**: `cross_r/E_r → n(n−1)` (the trivial bound is asymptotically TIGHT), so the threshold
cannot be pushed below `~1.36 n` by any cross-term bound that does not already bound `B = max_{b≠0}|η_b|`.

Date: 2026-06-14. Thread row: `UNFINISHED_THREADS_407.md` 407-T28 (Cluster 2). Status before:
"trivial `C_r≤E_r` gives DM_r free for r≳1.36n; close band `[β log n, 1.36n]` via non-trivial cross_r".

---

## What was already in tree (verified axiom-clean, exit 0)

`ArkLib/.../Frontier/Sweep_A02_AutocorrelationRecursion.lean` already proves, char-free, over any
finite abelian group `G` and any `Finset H`:

- `energy_succ_eq` : **the exact recursion** `E(conv1H f H) = |H|·E(f) + crossTerm f H`
  (= `E_{r+1} = n·E_r + cross_r` for `f = 1_H^{*r}`, `n=|H|`). Holds in every characteristic.
- `autocorr_le_energy`, `crossTerm_le` : the trivial cap `C_r(z) ≤ C_r(0)=E_r` ⟹ `cross_r ≤ (n²−n)E_r`.
- `energy_succ_le_sq` : `E_{r+1} ≤ n²·E_r` (the crude recursion bound).
- `free_deep_tail` : if `n^r ≤ (2r−1)‼` (Stirling: `r ≳ e·n/2 ≈ 1.36 n`) then the crude bound
  `E_r ≤ n^{2r−1}` **already implies** the DM target `E_r ≤ (2r−1)‼·n^{r−1}` — unconditionally, no
  char-0 / Lam–Leung / transfer input. (`free_tail_n8`/`_n16` decidable; `_below` pins the crossover.)
- `CrossBandResidual` : the open band `[β log n, 1.36 n)` stated as an explicit named Prop.

Axiom audit on `energy_succ_eq`, `energy_succ_le_sq`, `free_deep_tail`:
`[propext, Classical.choice, Quot.sound]` (clean). So part (1) — verify the recursion — is DONE.

## What this pass settled (the actual open research question, parts 2 & 3)

**Part (2): Is there sub-trivial decay `cross_r ≤ (1−ε)·n(n−1)·E_r` in the band?  → NO.**

Exact integer computation over `G = ℤ/p`, `H = μ_n` (full additive convolution, no sampling),
probe `scripts/probes/wf407_T28-autocorr_recursion.py`:

| n | cross_r/E_r as r grows | trivial cap n(n−1) |
|---|---|---|
| 8 | 13 → 22 → … → **55.999** | 56 |
| 16 | 33 → 117 → … → **239.93** | 240 |
| 32 | 173 → 633 → … → **991.998** | 992 |
| 64 | 1025 → 3779 → … → **4031.999** | 4032 |

`cross_r/E_r` is **monotone INCREASING toward the trivial maximum `n(n−1)`** — the opposite of decay.
Equivalently `E_{r+1}/E_r → n²` exactly. The recursion verified exactly (recur=True) at every
(p,n,r) tested, char-p AND char-0 (`wf407_T28-autocorr_char0.py`, recur=True; same saturation).

**The Fourier explanation** (probe `wf407_T28-autocorr_fourier.py`, Parseval identity matched to
machine precision): `E_r = (1/p)·Σ_b |η_b|^{2r}`, `η_b = Σ_{x∈μ_n} e_p(bx)`, `η_0 = n`. Then
`E_{r+1}/E_r` is the `|η_b|^{2r}`-weighted average of `|η_b|²`, dominated by the **principal frequency
b=0** (`|η_0|²=n²`). So the cross term saturating `n(n−1)` is *forced by the principal term*, and the
only sub-trivial slack is

  `n(n−1) − cross_r/E_r  =  Θ( (B/n)^{2r} · n )`,   `B = max_{b≠0}|η_b|` = **the prize quantity**.

Measured gap-to-trivial decays geometrically (n=32: 811→358→69→10→1.38), rate set by `B`.

**Part (3): How far down can a cross bound push the 1.36n threshold?**
Probe `wf407_T28-autocorr_threshold.py`: under a hypothetical uniform `cross_r ≤ c·E_r`, the
DM-free threshold is `r* ≈ 1.36n` at `c=n(n−1)` (confirmed: 1.125n,1.188n,1.250n,1.297n,1.353n,1.359n
→ e/2). To pull `r*` down to the prize depth `r ~ β log n` (β≈5) requires:

| n | c needed for r*~β ln n | trivial c=n(n−1) | slack factor needed |
|---|---|---|---|
| 2^6 | 17.0 n | 63 n | 3.7× |
| 2^10 | 27.6 n | 1023 n | 37× |
| 2^20 | 53.8 n | 1048575 n | 19 488× |
| 2^30 | 79.1 n | 1.07e9 n | **13.6 million×** |

But the *measured* `cross_r/E_r` saturates AT `n(n−1)` from below with slack `O((B/n)^{2r})`. Reaching
`c ≈ 79n` at n=2^30 requires `(B/n)^{2r}` to be tiny over the band — which IS the prize's
`B ≤ C√(n log(q/n))` Gauss-period bound. **Circular: a non-trivial cross bound ⟺ a B-bound.**

## The precise wall

The cross term `cross_r` is **the additive-energy / `Σ|η_b|^{2r}` object itself**, and its only
controllable structure is the second-largest Gauss period `B`. So:

- **407-T28 ≡ W4 (moment-method `√(log)`-short) ≡ B-form** (`CharSumMomentDeepWall`, `GaussPeriodCosetReduction`,
  `WorstPeriodLowerBound`). The recursion is an exact reformulation, not a new lever: it routes
  through the same `E_r = (1/p)Σ_b|η_b|^{2r}` Parseval identity the moment method already uses.
- The "free deep tail" `r ≳ 1.36n` is real and unconditional, but the band `[β log n, 1.36n)`
  containing the optimum `r≈log q` is exactly where `B` is needed; the cross term gives NOTHING there.

This matches and sharpens the census note and the W4 wall in `MEMORY.md`
(`arklib-389-deep-moment-wall`): moment-optimal `r≍log q` vs char-0 validity `r_max≍2log_n p`.

## Artifacts

- `scripts/probes/wf407_T28-autocorr_recursion.py` — exact recursion + cross/E saturation (char-p).
- `scripts/probes/wf407_T28-autocorr_band.py` — `E_r/clean` vs r; "true DM onset" vs 1.36n.
- `scripts/probes/wf407_T28-autocorr_char0.py` — char-0 recursion (char-free) + same saturation.
- `scripts/probes/wf407_T28-autocorr_fourier.py` — Parseval `E_r=(1/p)Σ|η_b|^{2r}`, gap = `(B/n)^{2r}`.
- `scripts/probes/wf407_T28-autocorr_threshold.py` — c-vs-threshold curve; slack-factor-to-prize.
- `ArkLib/.../Frontier/Sweep_A02_AutocorrelationRecursion.lean` — the landed axiom-clean recursion brick
  (recursion, trivial bound, free deep tail, residual Prop) + axiom audit.

## What remains

Nothing actionable *on this lane*: the recursion is exact, the free tail is landed, the band residual
is provably the B-form wall. The genuine prize input is unchanged — bound `B = max_{b≠0}|η_b|`
(Paley-graph / BGK / Gauss-period). The autocorrelation recursion is a clean exact lens onto it, not a
way around it.
