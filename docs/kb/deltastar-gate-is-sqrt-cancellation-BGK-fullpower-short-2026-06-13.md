# DEFINITIVE: the gate = square-root cancellation for subgroup sums; best known (BGK/Shkredov 2024) is a FULL POWER short (2026-06-13)

The open core `B(μ_n) = max_{b≠0}|Σ_{x∈μ_n} e_p(bx)| ≤ √(2n·ln p)` is, in standard analytic-NT terms,
**square-root cancellation for incomplete character sums over a multiplicative subgroup of size
`n = p^γ`** (prize: `γ ≈ 0.156`). Grounded against the most recent authoritative source.

## State of the art (Kowalski, "Exponential sums over small subgroups, revisited", arXiv 2401.04756, Jan 2024)
- **Thm 1.1 (Bourgain–Glibichuk–Konyagin):** `|H| ≥ p^γ ⟹ Σ_{x∈H} e(ax/p) ≪ |H|·p^{−ν}`, `ν=ν(γ)>0`.
  In our terms `B(μ_n) ≤ n·p^{−ν} = n^{1−ν/γ}` — a power saving **off the trivial `n`**, not √.
- **Rmk 1.2(3):** the sharpest explicit `ν` is **Shkredov [Cor. 16]** — still a small power saving.
- **Rmk 1.2(2):** even *nontrivial* bounds for subgroups of size `(log p)^C` are flagged as open.
- Gauss-sum baseline (p.2): `|B| ≤ √p` always, "non-trivial for `|H|` a bit larger than `√p`" — i.e.
  the easy regime is `n>√p`, the OPPOSITE of the prize `n≪√p`.

## The quantitative gap (why this is genuinely hard, exactly)
| quantity | bound | exponent of `n` |
|---|---|---|
| trivial | `B ≤ n` | 1 |
| BGK/Shkredov 2024 (best known) | `B ≤ n^{1−ν}` | `1 − ν` (ν small) |
| **prize needs** | `B ≤ √(2n ln p)` | **1/2 + o(1)** |

The best unconditional bound and the prize requirement differ by **~half a power of `n`** — BGK saves a
*tiny* `ν`; the prize needs to save `1/2`. Square-root cancellation for subgroup character sums in the
`n = p^γ`, `γ<1/2` regime is the **recognized deep open problem** (no method reaches it; even GRH/Burgess
control intervals not subgroups, and need `n>p^{1/4}`). This is exactly BCHKS Conj 1.12 in analytic form.

## Net (honest, definitive)
Across this session the prize was reduced — with PROVEN brackets and bridge — to a single object, and
that object is now identified, against a 2024 authoritative survey, as **square-root cancellation for
incomplete subgroup character sums**, which the state of the art misses by a full half-power of `n`.
The magnitude-method no-go (`…-bootstrap-NOGO-…`) shows the gap cannot be closed by powering up any
sup-norm bound; the equidistribution-defect form (`…-gate-as-equidistribution-defect-…`) is the
counting dual. **The gate is genuinely, quantifiably open. No closure claimed; not fabricated.**

New papers filed (`~/papers/arklib/_new/user6-*`): Kowalski 2401.04756 (BGK revisited), Kowalski/Perret
2112.05441 (equidistribution of subgroup-indexed exp sums), 2509.07765 (Burgess GAP rank-2),
Shparlinski open-problems survey. These confirm — they do not lift — the gate.
