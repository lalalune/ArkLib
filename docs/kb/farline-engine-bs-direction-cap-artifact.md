# Engine pitfall: the `b ∈ [k, s)` direction cap fakes a past-proxy δ\* "deviation" at n ≥ 32

**Status:** verified gotcha (mechanism + authoritative in-tree record). 2026-06-15, #444/#407.
**TL;DR:** The Rust/CUDA far-line δ\* engines restrict far directions to `b ∈ [k, s)`. That cap
*silently excludes the binding antipodal direction* `(a,b) = (n/2, n/2±1)` at the binding rungs,
so the engine reports a **spuriously large** δ\* at n ≥ 32 (e.g. δ\*(μ₃₂, k=8, ρ=¼) = 0.594 instead
of the true Plotkin-proxy ≈ 0.531 = Johnson). Do **not** read that bump as a structural
past-Johnson/past-proxy signal — it is an artifact. Use the full b-range (or restrict-and-add the
order-2 family, as `lcfast` does) when you care about the worst-case far incidence at n ≥ 32.

## The cap

`scripts/rust-pg/src/main.rs:149` builds the far-direction set as
```rust
let dirs = ((k)..(s)).flat_map(|b| ((k)..(n)).filter(|&a| a != b).map(|a| (a,b)));
```
i.e. `b ∈ [k, s)`, `a ∈ [k, n)`. The CUDA port (`scripts/cuda-pg`) mirrors this. So for every rung
`s`, *no direction with `b ≥ s` is ever evaluated* — even though the in-tree `farIncidence`
definition (`B1IncidenceBridge.lean:96`, worst case over **all** `(u₀,u₁)`) has no such restriction.

## Why it produces a fake deviation

The over-determined incidence is exactly quantized: `incidence(a,b;s) = d·orbits`,
`d = n/gcd(n, a−b)` (proven axiom-clean, `DeepBandR4Bound.lean`; DISPROOF_LOG O177). The worst-case
(maximizing) over-det direction is the **antipodal one** `(n/2, n/2−1)` with closed-form max
`2m³−2m²+1 ~ n³/32` (m = n/4, `OverdetIncidenceMaxClosedForm.lean`). That direction has `b = n/2−1`,
so the cap `b < s` excludes it for **every** `s ≤ n/2−1` — i.e. throughout its entire BAD phase. The
engine therefore never sees the direction that determines the true binding rung.

- **n ≤ 28 (ρ=¼):** the cap happens not to matter — other in-range (`b < s`) directions cross the
  budget at the same rung as the antipodal one, so the engine still returns the correct proxy value
  (`δ* = ½ + (1/(2ρ)−1)/n`, matched exactly at n = 16, 20, 24, 28: 0.5625, 0.5500, 0.5417, 0.5357).
- **n = 32:** the in-range directions all drop below budget by `s = 13`, while the excluded
  antipodal/high-b directions are still BAD until `s ≈ 15 = 2k−1`. The engine, blind to them,
  reports `s* = 13` (δ\* = 0.594) instead of the true `s* ≈ 15` (δ\* ≈ 0.531). The n = 34, 38 GPU
  values (0.6176, 0.6579) are the same artifact.

Because the engine can only *under*-count incidence (it drops directions), it can only
*over*-estimate δ\*. So any δ\* that sits **above** the Plotkin proxy is suspect by construction.

## The authoritative truth this is consistent with

The true over-determined far-line δ\* is the **Plotkin upper-bound proxy → ½** (half-agreement),
*below* the floor `1−ρ−Θ(1/log n)` and below Johnson `1−√ρ` for ρ<¼ — see
`DISPROOF_LOG.md` ("over-det δ\* DECOUPLING is REAL but reaches only PLOTKIN ½, NOT the floor") and
[`farline-incidence-is-plotkin-proxy-not-mca-deltastar.md`](farline-incidence-is-plotkin-proxy-not-mca-deltastar.md).
The fake bump does **not** change any of that: far-line δ\* is a *proxy* (rigorous upper bound on the
true MCA δ\* via `epsMCA ≥ far_inc/q`, `FarCosetExplosion.lean:87`); the open prize is the *floor*,
which numerics provably cannot reach (see
[`CRITICAL-numerics-cannot-distinguish-johnson-from-floor.md`](CRITICAL-numerics-cannot-distinguish-johnson-from-floor.md)).

## What to do

- For worst-case far incidence at **n ≥ 32**, use the **full b-range** `b ∈ [k, n)`, or — for speed —
  the `lcfast` Prony tool, which restricts to a `~3√(kn)` window **and explicitly adds the order-2
  family** (`b = n/2`, `a = n/2`). `lcfast` reports `window = [k, n)`, i.e. it does not inherit the
  `b < s` cap.
- Treat any engine δ\* **above** `½ + (1/(2ρ)−1)/n` as an artifact until reconfirmed with the full
  b-range. A direct full-range recompute at n = 32 (`lcfast 32 8`) is the clean confirmation; it is
  Prony-cost `552 × C(32,9) ≈ 1.5×10¹⁰` and needs an uncontended box (it starved out at load 200+).
- The `incidence = d·orbits` quantization and the exact p-independence of the over-det δ\* are
  **real and unaffected** by this pitfall.
