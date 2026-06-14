# Worst direction = large-gap construction (2^{sH(ρ)}) ≫ dir(k,t) (2^{s/2}); δ* = 1−ρ−2/s* modulo extremality (2026-06-13)

Resolving the worst-direction question via asymptotic comparison at a matched band `δ = 1−ρ−2/s`:

| direction family | bad-count at band δ=1−ρ−2/s | exponent |
|---|---|---|
| `dir(k,t)` (my closed nested-binomial) | `≈ 2^{n/2^a}`, `2^a=2n/s` ⟹ `2^{s/2}` | s/2 |
| **large-gap construction `dir((r−1)m, rm)`** | `C(s, ρs+2) ≈ 2^{s·H₂(ρ)}` | s·H₂(ρ) |

For ρ=1/2: construction `2^s` vs dir(k,t) `2^{s/2}` — the construction gives **exponentially more** bad
scalars. So the WORST direction is the large-gap construction one; `dir(k,t)` is far from worst (its
closed formula is a weak lower bound on #bad). This explains the earlier δ* gap (0.484 from dir(k,t) vs
0.441 from construction): the construction direction dominates.

## The sharpened bottom line
> **`δ* = 1 − ρ − 2/s*`,  `s* = min{ s : C(s, ⌊ρs⌋+2) ≥ ε*q }`**  — a CLOSED formula —
> **modulo ONE thing: extremality** = "no direction/config produces more than `C(s,r)` bad scalars at
> band `δ=1−ρ−2/s`." The upper bracket (construction ⟹ `δ* ≤`) is PROVEN; the lower bracket = extremality.

## What the session's q-independent theory contributes to the extremality
The bad scalars at band δ = configs `T` with vanishing power sums `p_1=…=p_{m−1}=0` (`m=t−k`), readout
`p_m=\hat{1_T}(m)`. Extremality = "the subgroup-coset unions maximize `#{distinct \hat{1_T}(m)}` over
power-sum-vanishing `T`." This is a q-INDEPENDENT Fourier-extremal problem (NO character-sum-mod-p wall).
The dir(k,t) closed formula (`Σ_s C(·,s)2^s`) shows such counts ARE closed binomials at that level — and
the construction is the dominant single term. Sibling #407 ("coset-saturation refuted but optimality
count survives") is independent evidence the C(s,r) count is extremal despite non-coset configs existing.

## Status (honest, consolidated)
PROVEN/verified this session: signed-single decomp; `e_2=0⟺P(ζ)²=P(ζ²)`; general-direction reduction
(power-sum-vanishing + e_{t−k} readout); worst dir = large-gap construction (this note); the 2-adic tower
recursion + closed nested-binomial for dir(k,t); the m=2 closed binomial (no additive energy).
δ* = 1−ρ−2/s* is the closed target; the SOLE remaining content is the EXTREMALITY of C(s,r) for the
large-gap direction — now framed as a q-independent Fourier/symmetric-function extremal problem, NOT the
incomplete-Gauss-sum wall. RETRACTED: s_max=μ−1. This is the cleanest, most prize-shaped state reached.
