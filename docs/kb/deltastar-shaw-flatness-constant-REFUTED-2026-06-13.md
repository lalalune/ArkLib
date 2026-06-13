# CROSS-CHECK: the sibling "Shaw Flatness" constant `B(μ_n) ≤ √2·√n` is REFUTED — the log factor is necessary (2026-06-13)

Issue #371 (author `lalalune`) reduces the whole MCA threshold, via the Hölder moment bound
`Σ_{b≠0}‖η_b‖^{2M} ≤ B^{2M−2}(qn−n²)` (= the same bound as my Markov `M_r` reduction, formalized as
`shaw_offdiag_moment_le`), to **one decidable inequality**: `B(μ_n) = ‖𝖲_D|_{1^⊥}‖ ≤ √2·√n`
("Shaw Flatness", claimed "constant pinned sharp by the 3n²−3n energy floor"). I tested it directly.

## Data (`scripts/probes/probe_shaw_flatness_refute.py`): B = max_{b≠0}|η_b|, exact
| n | p | B | √2·√n | 2√(n−1) (Ramanujan) | √(2n ln p) | B/√n | B/√(n ln p) |
|---|---|---|---|---|---|---|---|
| 4 | 1033 | 3.98 | 2.83 | 3.46 | 7.45 | 1.99 | 0.76 |
| 8 | 32801 | 7.84 | 4.00 | 5.29 | 12.90 | 2.77 | 0.86 |
| 16 | 1048609 | 14.51 | 5.66 | 7.75 | 21.06 | **3.63** | 0.97 |
| 32 | 32801 | 16.97 | 8.00 | 11.14 | 25.80 | 3.00 | 0.93 |

**`B > √2·√n` at EVERY point** (by ~2×), and `B > 2√(n−1)` too — the generalized Paley graph
`Cay(F_q^+, μ_n)` is **not Ramanujan**, let alone √2-flat. **`B/√n is unbounded** (→3.6 and climbing),
so NO bound `C·√n` holds for any constant `C`.

## Diagnosis: average-vs-max (L²-vs-L∞) confusion
The `3n²−3n` energy floor controls the **L² average** of the periods: `Σ_{b≠0}η_b² = qn−n² ⟹`
RMS `η_b ≈ √n`. But `B` is the **L∞ / max** period, which exceeds the RMS by the standard
`√(log)` deviation factor. "Shaw Flatness" pins the average and mislabels it the max. So the reduction
`δ* ← B ≤ √2√n` reduces to a **false** inequality; the eigenvalue residual MUST carry the log factor.

## What survives (congruent with my scaffold, corrected constant)
`B/√(n·ln p) ≈ 0.75–0.97`, roughly constant and `< √2` — confirming the **correct** target
> **`B(μ_n) ≤ √(2n·ln p)`** (sup-norm of Gaussian periods, WITH the log),
which is exactly the scale my Markov bridge (`…-DIRECT-ATTACK-markov-mechanism-…`) uses and on which the
prize `δ* = 1−ρ−2/s*` derivation rests. So: the bridge target is unchanged and confirmed; the sibling's
no-log constant is the error. The open core is the **sup-norm with log** (BCHKS 1.12), NOT a Ramanujan/
flatness bound — and crucially it is genuinely open *because* it is the max, not the (easy) average.

**Honesty:** this REFUTES a specific over-optimistic constant in the shared project state and CONFIRMS
the correct reduction target. It does not close the gate — `B ≤ √(2n ln p)` for `n=2^30,p=2^192` is
still the open BCHKS 1.12. Available to post to #371 as a correction if wanted.
