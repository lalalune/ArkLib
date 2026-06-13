# Precise characterization: why `B(μ_n)` is hard (the unique open core) (2026-06-13)

The single remaining open piece of the prize — proven irreducible (no elementary/Fisher method
reaches it, since the construction has maximal coincidence at every order) — is the worst-case
Gaussian period `B(μ_n) = max_{b≠0} |η_b|`, `η_b = Σ_{x∈μ_n} e_p(bx)`. Here is the exact reason it
resists, derived from the moment structure.

## The moments are exactly computable and Gaussian-like at order ≤ 4
`η_b` is constant on the `f=(p−1)/n` cosets `bμ_n`. Exact moment identities:
- `Σ_b |η_b|² = p·n`  ⟹  over cosets `Σ|η|² ≈ p`, `avg|η|² = n`.
- `Σ_b |η_b|⁴ = p·E(μ_n) = p(3n²−3n)`  ⟹  `avg|η|⁴ ≈ 3n²`, so
  > **`avg|η|⁴ / (avg|η|²)² = 3`** — *exactly the Gaussian 4th/2nd ratio.*

So the periods are **Gaussian-like in their 2nd and 4th moments** (variance `n`), predicting the
conjectured `B(μ_n) = Θ(√(n·log(p/n)))` (max of `f` Gaussians of variance `n`).

## Why the 4th moment cannot prove the max (the precise gap)
- **4th moment alone** gives only `max|η|⁴ ≤ Σ|η|⁴ ≈ 3pn`, i.e. `B ≤ (3pn)^{1/4}` — carries a
  `p^{1/4}` factor (`≈2^{55}` at `p=2^{192},n=2^{30}` vs the true `≈2^{19}`). **Far too weak.**
- The **max over `f` near-Gaussian variables** needs sub-Gaussian tails = control of the `2j`-th
  moments `Σ_b|η_b|^{2j} = p·E_j(μ_n)` (the additive `2j`-energy) up to `j ≈ log f = log(p/n)`.
- **But** (proven earlier, `moment-hierarchy-correction`): `E_j(μ_n)` is **clean** (minimal)
  **iff `p > n^j`**. So clean only for `j < ⌈log_n p⌉ ≈ 6` (prize), while the max needs `j` up to
  `≈ log(p/n) ≈ 162`.

> **The gap: clean moments reach order `≈ log_n p ≈ 6`; the worst-case max needs order
> `≈ log(p/n) ≈ 162`.** The intervening high additive energies `E_j(μ_n)` (`6 ≤ j ≤ 162`) are
> **not** controlled by the clean low-order structure — this is exactly the Bourgain-regime
> incomplete-character-sum difficulty, and it is genuinely open for `n ≪ √p`.

## Consequence (the honest final localization)
The prize `δ*` reduces — provably and irreducibly — to bounding `B(μ_n) ≤ C√(n·log(p/n))`, which is
equivalent to controlling the high additive energies `E_j(μ_n)` for `⌈log_n p⌉ ≤ j ≤ log(p/n)` in
the deployed regime. This is the **single, precisely-located, recognized-hard open input**; every
other component of the proof of `δ* = 1−ρ−2/s*` is established (upper bracket + monomial extremality
+ the direction-Fisher second-moment bound + the proof that no elementary method suffices).

**No closure is claimed.** This page records the exact mathematical reason the prize's analytic core
is open, so that a future analytic bound on `B(μ_n)` (or on the high energies `E_j`) slots directly
into the otherwise-complete scaffold.

## UNIFICATION: `B(μ_n)` IS the SubsetSumHalo question (the definitive map)
The `p`-dependence of `B(μ_n)` is governed by the *same* spurious-relation object as
`SubsetSumHaloEnergy.lean`:
- `E_j(μ_n) = clean + excess`, `clean ≈ (2j−1)!!·n^j` (Gaussian moments), `excess ≈ n^{2j}/p`
  (number of spurious `2j`-term mod-`p` vanishing relations ≈ candidate tuples `/p`).
- For `j < log_n p` (`≈6`): excess `≪` clean ⟹ `E_j ≈ clean` ⟹ `η` Gaussian ⟹ `B ≈ √(n·log(p/n))`.
- For `j > log_n p`: **excess dominates**, `E_j ≈ n^{2j}/p`, so `Σ_b|η_b|^{2j} ≈ n^{2j}` and the
  `L^{2j}` norm of `η` is `≈ n`. The high moments are carried by **spurious vanishing sums** — i.e.
  the **census halo** (`SubsetSumHaloEnergy`, nonempty for `p < 2^N`).

> **So `B(μ_n) ≤ C√(n·log(q/n))` holds iff the high-order spurious vanishing sums of `μ_n` mod `p`
> (the SubsetSumHalo / non-clean `E_j`, `6 ≤ j ≤ log(p/n)`) do not concentrate a period. For a
> *generic* field they don't (`B≈√(n log)`); for an *adversarial* field they can push `B → n`. The
> deployed-field status is precisely whether the halo concentrates — a specific, computable-per-field
> condition, NOT a universal asymptotic.**

This is the complete map: the prize's analytic core (`B(μ_n)`), its list-decoding core
(beyond-Johnson `Λ`), its additive-energy core (`E_j`), and its combinatorial core (the SubsetSumHalo
/ Kambiré sumset) are **one object** — the high-order spurious vanishing sums of the smooth subgroup
mod the deployed prime. Pinning `δ*` exactly = resolving whether these concentrate for the specific
deployed field. Proven: everything reduces here. Open: the concentration question itself (Bourgain
regime). No closure claimed — but the open core is now a single, unified, field-specific object.
