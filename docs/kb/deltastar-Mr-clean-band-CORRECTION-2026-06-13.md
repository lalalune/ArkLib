# CORRECTION: the `b≠0` moment `M_r` never departs upward — bridge cleanness holds past `log_n p` (2026-06-13)

Direct computation (`scripts/probes/probe_Mr_cleanband.py`) of the EXACT object the Markov bridge
minimizes — `M_r = Σ_{b≠0} η_b^{2r}` (`η_b = Σ_{x∈μ_n} e_p(bx)`, real for 2-power `n`) — versus the
Gaussian baseline `p·(2r−1)!!·n^r`, for `r = 1..15`:

| n | p | log_n p | max ratio `M_r / Gaussian` | trend through r=15 |
|---|---|---|---|---|
| 8 | 521 | 3.0 | 0.985 (r=1) | monotone ↓ to ~1e−4 |
| 8 | 32801 | 5.0 | 1.000 (r=1) | monotone ↓ |
| 16 | 4129 | 3.0 | 0.996 (r=1) | monotone ↓ |

**`M_r ≤ Gaussian` for every `r`, with the ratio SHRINKING** — no blow-up at `r > log_n p`.

## What this corrects
`deltastar-moment-hierarchy-correction-…` claimed the moment "departs from clean at `p < n^j`",
suggesting the bridge fails past `r ≈ log_n p`. That conflated two objects:
- **raw energy `E_r`** (= `(M_r + n^{2r})/p`): its `n^{2r}/p` term *does* grow once `r > log_n p` —
  but that term is the `b=0` contribution, a **red herring** (already flagged in the markov-mechanism note);
- **the `b≠0` moment `M_r`** (what the bridge actually uses): stays `≤` Gaussian with growing room.

So the bridge's cleanness hypothesis is **empirically robust well past `log_n p`**, and the extracted
sup-norm comes in UNDER prediction: `n=8,p=521`, `r=15` → `B ≈ M_r^{1/2r} ≈ 7.15 < √(2n ln p)=10.0`.

## What it does NOT do (honesty)
This is small-`(n,p)` data, not a proof. The bridge needs `M_r ≤ Gaussian·poly` at `r ≈ ln p`
**proven for `n=2^30, p≈2^192`** — i.e. BCHKS Conj 1.12. The crux survives: the would-be inductive
step `M_{r+1} ≤ (2r+1)n·M_r` (which the monotone ratio would follow from) requires `max η_b² ≤ (2r+1)n`,
i.e. `B² ≤ (2r+1)n` — TRUE iff `r ≳ B²/2n ≈ ln p`, exactly the point we need and exactly circular.
The gate is genuinely at `r≈ln p` and genuinely open. **No closure claimed; the correction strengthens
confidence in the REDUCTION, not a proof of the gate.**
