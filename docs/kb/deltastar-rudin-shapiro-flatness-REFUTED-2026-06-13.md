# Rudin–Shapiro flatness route for the 2-power period tower — REFUTED (#407)

**Status: refuted numerically.** A genuine new attempt to close the prize-regime worst-case bound
`M(μ_n) ≤ C√(n log)` by connecting the 2-power Gaussian-period tower to *proven* flat-polynomial
(Golay–Rudin–Shapiro) theory. The tower is NOT flat; the route is dead. 2026-06-13.

## The idea
The in-tree parallelogram recursion (`GaussPeriodTower.lean`)
`‖η_b(μ_n)‖² + ‖η^χ_b(μ_n)‖² = 2(‖A‖² + ‖B‖²)`, `A=η_b(μ_{n/2})`, `B=η_{bζ}(μ_{n/2})`, is
structurally a Golay–Rudin–Shapiro butterfly `P_{k+1}=P_k+x^{2^k}Q_k`, `Q_{k+1}=P_k−x^{2^k}Q_k`,
whose flatness `|P|²+|Q|²=const` is a THEOREM. If the period tower were RS-flat, i.e.
`g(b) := ‖η_b(μ_{n/2})‖² + ‖η_{bζ}(μ_{n/2})‖²` were constant in `b`, the telescoped flatness would
give `M(μ_n) ≤ C√n` reducing to proven flat-polynomial theory — a closure off the BGK wall.

## The refutation (`scripts/probes/probe_rudin_shapiro_flatness.py`)
Measured `CV(g) = std(g)/mean(g)` over `b≠0`, n=16..256, indices 40..1000:
`mean(g) ≈ n` (Parseval ✓) but **`CV(g) ≈ 0.76–1.06`, NOT decaying to 0** as n or index grows.
RS-flatness requires `CV→0`. The tower is decisively NOT flat.

## What it reveals (the honest content)
`CV(g) ≈ 1` is the exact signature of the periods being **complex-Gaussian** (`|η|²` exponential,
CV=1) — the "random-like" behaviour. So the worst period is the extreme value of `m≈index`
random-like exponentials, `M² ≈ n·log(index)`, `M ≈ √(n log index)` — the CONJECTURED bound. But
this is the equidistribution/BGK statement, NOT a rigid flat construction: the tower is random-like,
so flat-polynomial theory cannot apply, and the proof of `M ≤ √(n polylog)` genuinely needs
sub-Gaussian equidistribution of the period family = the recognized open BGK / Paley-graph problem.

**Net:** one more elementary closure route (flat polynomials) ruled out; the random-like CV≈1
confirms the conjectured value while confirming the open core is the equidistribution wall.
Related: `deltastar-cumulant-dichotomy-2026-06-13.md`, `deltastar-constant-index-sqrt-cancellation-2026-06-13.md`.
