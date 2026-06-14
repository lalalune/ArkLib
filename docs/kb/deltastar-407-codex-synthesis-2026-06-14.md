# #407 δ* synthesis — Codex pass (2026-06-14)

## What I did

- Read issue #407 and the local ProximityGap guide/workbench.
- Checked the newest local KB notes, especially the orbit-count and sparse-cyclic reformulations.
- Downloaded five open-access papers into `research/proximity-407-papers/`:
  - `arxiv-2601.07137-kopparty-noisy-character-values.pdf`
  - `arxiv-2504.10202-kalmynin-additive-irreducibility-subgroups.pdf`
  - `arxiv-2307.01344-gorodetsky-kovaleva-high-traces-character-sums.pdf`
  - `arxiv-1207.1607-demirci-akarsu-marklof-incomplete-gauss-sums.pdf`
  - `arxiv-2303.16475-spectral-pseudorandomness-paley.pdf`
- Ran the relevant probes:
  - `probe_407_actionorbit_K_growth_law.py`
  - `probe_gausssum_supnorm_formula.py`

## Refutation results

The constant-orbit-count escape is false in the true action-orbit model.  The probe reports:

| rate proxy | n | r | orbit count K |
|---|---:|---:|---:|
| `ρ = 1/4` | 8 | 2 | 4 |
| `ρ = 1/4` | 16 | 4 | 78 |
| `ρ = 1/2` | 8 | 4 | 6 |
| `ρ = 1/2` | 16 | 8 | 206 |

So an `O(1)` orbit-count pin is refuted already at small proper-subgroup scale.  A polynomial
orbit-count statement can still be true, but the existing ledger already identifies it with the
same beyond-Johnson list-size / BGK wall.

The Gauss-period probe continues to support the `sqrt(n log m)` scale: sampled ratios
`M / sqrt(n log m)` were in roughly `[0.84, 1.39]`.  This is evidence for the square-root-log
candidate, not a proof.

## Paper triage

- Kopparty 2026 gives an algorithmic Stepanov/Weil analogue for recovering polynomials from
  noisy character values.  Useful technique; it does not bound the thin-subgroup Gaussian-period
  sup norm in the prize regime.
- Kalmynin 2025 gives strong additive-irreducibility theorems for multiplicative subgroups.
  This rules out some extreme additive decompositions, but it is qualitative and does not give
  the quantitative `O(n)` bad-scalar/coset bound.
- Gorodetsky-Kovaleva 2024 proves high-conductor cancellation in a function-field matrix-trace
  setting.  It is a possible analogy for effective Katz bounds, but not a prime-field dyadic
  subgroup estimate.
- Demirci Akarsu-Marklof 2012 supplies a value-distribution law for incomplete Gauss sums.
  It supports the large-value/statistical lens, not a worst-case uniform bound.
- Kunisky 2023 makes the Paley spectral-pseudorandomness obstruction explicit.  It reinforces
  the generalized-Paley/Gaussian-period framing already in-tree.

## Surviving conjecture package

The only candidate that remains close to the prize regime is the existing entropy pin:

`δ* = 1 - ρ - H(ρ) / log₂(q·ε*)`.

Scores:

| criterion | score | reason |
|---|---:|---|
| novelty | 9 | Combines the entropy ladder ceiling with Gaussian-period extreme-value control and the orbit/list faces. |
| insightfulness | 9 | All surviving routes collapse to the same `max_b |Σ_{x∈μ_n} e_q(bx)|` object. |
| proximity | 10 | It is exactly the prize window with `q·ε* ≈ n`, above Johnson and below capacity. |
| feasibility | 7 | The ceiling is proven, but the floor is the recognized square-root cancellation wall. |

Because feasibility is below 9, this is **not** a solved conjecture.  The newly added Lean file
`Frontier/Prize407EntropyPinSynthesis.lean` names the surviving square-root-log interface:

`SqrtLogGaussPeriodBound ψ G C := WorstCaseIncompleteSumBound ψ G (C * |G| * log |F|)`.

It also proves the deterministic consumers
`addEnergy_le_of_sqrtLogGaussPeriodBound` and
`addEnergy_div_le_of_sqrtLogGaussPeriodBound`: if the square-root-log period bound is supplied,
the existing additive-energy budget follows at the same scale. These are conditional plumbing
lemmas only; they do not prove the period bound.

Refutation hooks are in the same file:
`not_sqrtLogGaussPeriodBound_of_period_sq_gt` fires from a single measured frequency above the
period scale, and `not_sqrtLogGaussPeriodBound_of_energy_gt` fires from additive energy above the
derived budget.

That period bound is the honest next proof target.  This pass found no closed proof that avoids
the open thin-subgroup Gaussian-period bound.
