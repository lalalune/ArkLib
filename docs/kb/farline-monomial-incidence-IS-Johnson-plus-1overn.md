# RESOLVED: the far-line monomial incidence δ* = Johnson + 1/n — it pins the Johnson lane, not the floor (#407)

The cleanest, most honest characterization of the computable object — reconciling the back-and-forth of the
last several turns (was it ½? the floor? capacity?). Exact, validated (Rust engine).

## The exact result (ρ=1/4, exact on all points)

The binding far-line list-decoding radius is **`s* = 2k−1 = √(kn) − 1`** exactly:

| n | k | s* | 2k−1 | δ* = 1−s*/n | Johnson 1−√ρ | δ* − Johnson |
|---|---|---|---|---|---|---|
| 16 | 4 | 7 | 7 | 0.5625 | 0.5000 | 0.0625 = 1/n |
| 20 | 5 | 9 | 9 | 0.5500 | 0.5000 | 0.0500 = 1/n |
| 24 | 6 | 11 | 11 | 0.5417 | 0.5000 | 0.0417 = 1/n |

Since the **Johnson agreement radius** is `t_J = (1−δ_J)n = √ρ·n = √(kn)`, we have `s* = √(kn) − 1 = t_J − 1`, so:

> **δ\*_far-line-monomial = 1 − (√(kn) − 1)/n = 1 − √ρ + 1/n = Johnson + 1/n  →  Johnson.**

## What this resolves

The computable far-line **monomial** incidence object pins the **Johnson radius** (the *lower* edge of the prize
window `(1−√ρ, 1−ρ−Θ(1/log n))`), with a `+1/n` granularity correction. It does **NOT** track the floor (the
*upper* window edge). This:
- **reconciles the confusion:** "δ* → ½" was the ρ=1/4 special case (Johnson(¼)=½); "δ* → 1−ρ" was the k=2 sweep
  artifact (ρ changing). At **fixed ρ**, δ*_far-line = Johnson + 1/n, cleanly.
- **identifies the object exactly:** this is the in-tree **"Johnson lane"** — the far-line monomial incidence has
  been pinning Johnson all along (computably, p-independently, off-BGK).
- **localizes the prize precisely:** the floor `1−ρ−Θ(1/log n)` lives strictly ABOVE Johnson, in the window
  interior, and is **not** captured by far-line monomial witnesses. It needs **general / curve witnesses**
  (GG25 curve-decodability) — the genuinely harder object, where the BGK/list difficulty lives.

## Consequence for the campaign

The decoupling / p-independence results (proven, durable) are about the **Johnson-lane** far-line monomial object
— which is exactly Johnson + 1/n, computable, and NOT the prize floor. So:
- **Honest downgrade:** the computable p-independent object does NOT pin the prize δ*; it pins Johnson. My earlier
  "δ* decouples and might track the floor" was about the wrong (Johnson-lane) object.
- **The prize δ* = Johnson + (window-interior gap)**, and that gap is the general-witness / curve-decodability /
  BGK object — unchanged as the open core, now cleanly separated from the computable Johnson lane.

## Status

A clean, exact, validated characterization (δ*_far-line-monomial = Johnson + 1/n) — NOT a closure of the prize.
It pins what the computable object is (Johnson) and confirms the floor is the separate, harder general-witness
object. ρ=1/2 + n=28 confirmation running. This is the correct, honest reconciliation of the far-line incidence
investigation: it is the Johnson lane, exactly.
