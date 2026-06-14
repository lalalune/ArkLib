# (3) Non-moment L^∞ route = Gauss-sum phase pseudorandomness; floor = random-phase prediction (2026-06-13)

The lead: `M(n)≤√(2n ln p)` survives even where the cumulant is heavy ⟹ a NON-MOMENT reason. Pursued it.

## The Gauss-sum decomposition (verified, `probe_gauss_phase_coherence.py`)
For χ trivial on μ_n (order | f=(p−1)/n): `η_b = (1/f)Σ_χ \bar{χ}(b)·g(χ)`, each `|g(χ)|=√p`.
Reconstruction matches M exactly. So `η_b` = average of f phased Gauss-sum vectors of length √p.

## The decisive structure: floor = random-phase extreme value
Measured coherence at the worst `b*`: `|Σ_s \bar{χ_s}(b*)g(χ_s)| / (Σ|·|)` ≈ **2.3–2.8× the incoherent
floor 1/√f** — partial alignment by a `√(log)`-ish factor (matching M/√n ≈ 2.3–2.8).
**Random-phase heuristic is exact:** if the f phased Gauss sums behave randomly, `max_b|Σ| ≈ √(f·ln p)·√p`
(extreme value of p Rayleigh(√f) trials), so `η_b ≈ (1/f)√(f ln p)√p = √(p ln p / f) = √(n·ln p)` = THE FLOOR.
> So the floor `√(n·log p)` is precisely the random-Gauss-sum-phase prediction; the `√(log p)` factor is
> the max over the p frequencies b (no moment hierarchy needed). This EXPLAINS why the floor is √(n log),
> not √n, and why the bound is robust to moment-heaviness (it's an L^∞/phase fact, not an L² one).

## Where it lands (honest)
The non-moment statement = **the Gauss-sum phases `arg g(χ_s)` don't conspire** (joint pseudorandomness),
so no single b aligns them beyond `√(log)`. PARTIAL known: individual Gauss-sum argument equidistribution
is PROVEN (Patterson; Heath-Brown–Patterson for cubic). OPEN: the JOINT distribution of the f Gauss sums
and the sup over b = BGK. So (3) is a cleaner, non-moment FORMULATION (floor = random prediction; explains
the √log and the robustness) but reduces to the same wall — Gauss-sum joint phase pseudorandomness.
No non-moment escape; no provable partial beyond BGK n^{1−1/2880}.

**Net for (3):** genuine clarification (the floor IS the random-phase value; the route is L^∞/phase not
moment), but the irreducible core is Gauss-sum phase non-conspiracy = BGK. Not a closure.
