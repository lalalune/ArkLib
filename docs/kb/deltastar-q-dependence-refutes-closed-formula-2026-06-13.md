# Interior δ* is q-dependent in the prize regime — refutes every (ρ,B)-only closed formula, 2026-06-13

## Claim (verified, reproducible)

For the prize-shaped smooth Reed–Solomon family `C = RS[F_q, μ_n, k]` with
`n = 16`, `k = 2` (`ρ = 1/8`), budget `B = q·ε* ` fixed at the prize shape `B = n = 16`,
the **interior far-line incidence `I_q(a)` at the critical agreement level
`a = 5` is NOT a function of `(n, k, a)` alone** — it depends on the arithmetic of
`q` (which additive/multiplicative coincidences μ_16 ⊂ F_q* exhibits).

Consequently the interior threshold
`δ*(C, ε*) = 1 − amin(q)/n`, `amin(q) = min{ a : I_q(a) ≤ B }`,
**moves with `q` at completely fixed `(ρ, B)`** — so no closed formula in `(ρ, B)`
alone (Johnson `1−√ρ`, the entropy candidate `δ_ent`, or any other) can exactly
pin δ* in the prize regime.

## Data (deterministic power-word centers only, no random sampling)

`I_q(5)` = max over power words `u = x^j|_{μ_16}` of the number of distinct
degree-≤3 polynomials agreeing with `u` on ≥ 5 of the 16 subgroup points
(the dim-`(k+1)=3` super-code agreement list, = far-line incidence).
Proper-subgroup primes only (`16 | q−1`, `q > 17`, so `μ_16 ≠ F_q*`):

| q | I_q(5) | witness | δ* verdict (B=16) |
|---|---|---|---|
| 97 | 64 | x^6 | δ* < 0.6875 |
| 113 | 64 | x^7 | δ* < 0.6875 |
| 193 | 18 | x^9 | δ* < 0.6875 |
| 241 | 16 | x^5 | δ* = 0.6875 |
| 257 | 16 | x^7 | δ* = 0.6875 |
| 337 | 18 | x^9 | δ* < 0.6875 |
| 353 | 18 | x^8 | δ* < 0.6875 |
| 401 | 16 | x^5 | δ* = 0.6875 |
| 433 | 16 | x^5 | δ* = 0.6875 |
| 449 | 2 | x^8 | δ* = 0.6875 |
| 577 | 32 | x^7 | δ* < 0.6875 |
| 641 | 2 | x^8 | δ* = 0.6875 |
| 673 | 2 | x^8 | δ* = 0.6875 |
| 769 | 2 | x^8 | δ* = 0.6875 |

`I_q(5) ∈ {2, 16, 18, 32, 64}` — a 32× spread at fixed `(n,k,a)`. The δ* crossing
flips between `0.625` (a=6) and `0.6875` (a=5) depending on `q`.

Probe: `scripts/probes/probe_deltastar_qdependence_v2.py` (and `_qdependence.py`
for the full per-agreement sweep). Reproducible; exact (Lagrange interpolation
over every `(k+2)`-subset, precomputed inverse table).

## Why this refutes the tail-gate `δ_ent`

The tail-gate conjecture (`deltastar-tail-gate-conjecture-2026-06-13.md`) asserts
`δ*(C, ε*) = δ_ent(ρ, B) = 1 − ρ − H₂(ρ)/log₂ B` up to radius granularity.
Here `δ_ent = 1 − 1/8 − H₂(1/8)/log₂ 16 = 0.7391`, a **constant** in `q`. But the
measured δ* is both **strictly smaller** (`≤ 0.6875`) *and* **q-varying**. So
`δ_ent` is not an exact pin — at best a q-independent envelope that overshoots.
The same refutation kills any Johnson/entropy/single-formula candidate.

## Interpretation — this is the recognized open core, made explicit

`I_q(a)` at the critical level is exactly the subgroup additive-energy /
vanishing-subset-sum count of `μ_n ⊂ F_q*` (cf. [[issue389-additive-energy-crux]],
[[issue389-deltastar-frontier-map]], and the #400 `Θ(n²)`, q-dependent
value-set count). The q-dependence here is the *same* arithmetic appearing at the
exact threshold rather than near capacity. The prize-as-an-exact-clean-formula is
therefore **impossible**; the honest residual is the q-dependent bound
`I_q(a) ≤ B`, i.e. the open additive-energy/character-sum estimate.

This extends the earlier single-point observation (`I(6)=7 ≠ C(8,6)/6` at F₁₇,
[[issue389-deltastar-frontier-map]]) to a robust 14-prime prize-shape sweep with
deterministic witnesses and an explicit 32× incidence spread.

## Reconciliation with the s_max integer-staircase claim

`issue400-smax-law-mu-minus-1-deltastar-staircase-2026-06-13.md` proves
`#bad = Θ(n^{s_max})` with `s_max = log₂ n − 1` a **q-independent integer**, and
concludes "δ* is a q-independent integer staircase (the s_max: 2→3 transition)."
That is correct for the **exponent** but does **not** pin the exact δ* the prize
demands. The data here shows the **O(1) constant** `C_q` in
`#bad ≈ C_q · n^{s_max}` is q-dependent (the 2→64 spread), and against the
*absolute* budget `B = q·ε*` that constant shifts the crossing by a full integer
agreement level (`a = 5` vs `a = 6`, i.e. `δ* = 0.6875` vs `0.625`). So:

- **q-independent:** the staircase *exponent* `s_max` (asymptotic order of #bad).
- **q-dependent:** the exact threshold δ* at finite `n`, because the prize budget
  `B` is an absolute count and the leading constant decides which side of `B` the
  band falls on.

The staircase pins δ* only up to its band; *within* the band the q-dependent
constant resolves the exact value, and that constant is the open additive-energy
quantity. "Exact, worst-case δ*" (the prize wording) is therefore not q-independent.

## What survives as the closed target

`δ*(RS[F_q, μ_n, k], ε*) = 1 − amin(q)/n` is the *exact* characterization (a
finite, decidable quantity per `q`). What is open and unavoidable is a closed
**bound** on `I_q(a)` uniform in `q` — and the data shows that bound cannot be a
clean function of `(ρ,B)`; it must carry the arithmetic of the subgroup. Any
prize solution must either (i) prove the q-uniform additive-energy bound directly,
or (ii) abandon "exact closed δ*" for an explicit tight lower bound (capacity).
