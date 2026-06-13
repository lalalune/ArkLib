# The machine-checked δ* bracket at all four prize rates (#389 calibration)

`probe_deltastar_bracket_allrates.py`, exact-integer deep-band activation at ε* = 2⁻¹²⁸.
Extends moon's `probe_ceiling_march.py` (ρ = 1/4) to ρ ∈ {1/2, 1/4, 1/8, 1/16}.

## The bracket (both sides in-tree, axiom-clean)
- LOWER δ_J = 1 − √ρ (Johnson, BCIKS/Hab25 MCA floor)
- UPPER δ_ceil = 1 − (k+m*+1)/n (moon's `mcaDeltaStar_le_of_deep_band`, deepest activated band)

## Verdict (n = 64..1024, q ∈ {n², n³})
1. **Non-empty at EVERY prize rate**: δ_ceil > δ_J for all (ρ, n, q) tested — δ* is genuinely
   bracketed strictly inside the window (1−√ρ, 1−ρ) at all four rates, not just ρ = 1/4.
   Widths grow from ~0.05–0.10 (n=64) toward √ρ−ρ (the full Johnson-to-capacity gap) as n grows.
2. **The ceiling tracks KKH26**: the gap-to-capacity g = (1−ρ) − δ_ceil has g·log₂n converging
   (decelerating) to a rate-dependent constant ≈ 0.25–0.35 — consistent with g = Θ(1/log n),
   i.e. the deep-band ceiling sits at the known capacity-side frontier 1−ρ−Θ(1/log n) at every
   rate. So the UPPER side of the δ* bracket is essentially at the best known bound.
3. **Consequence — pinning δ* is a LOWER-bound problem.** Because both proven upper bounds
   (deep-band ceiling, KKH26) → capacity as n → ∞, the bracket width → √ρ−ρ (the whole window)
   and the upper side gives no asymptotic pin. The entire remaining content of "pin δ*" is
   lifting the Johnson floor 1−√ρ up into the window — exactly the sub-Johnson supply wall
   (#389's single open statement). This is now confirmed identically across all four prize rates.

Exact integers throughout (the activation test is `q·Λ² < (P·Λ // q^m) << 128`); floats only
for the √ρ display and the g·log₂n scaling fit. Calibration only — no new bounds claimed; reads
the landed ceiling/Johnson lemmas as ground truth.
