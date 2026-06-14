# δ* (#407) — new reading list: subgroup character-sum sup-norm / value distribution (2026-06-13)

Five papers acquired this round, centred on the prize's identified open core —
`B(μ_n) = max_{b≠0}|Σ_{x∈μ_n} e_p(bx)| ≤ √(n·log(p/n))` = **square-root cancellation for the
additive-character transform of a multiplicative subgroup `μ_{2^μ} ⊊ F_p^×`, `n = p^{1/β}`,
`β≈4–5`** (= the BGK regime). Downloaded to `~/papers/arklib/_407/`. The headline: the literature
**independently confirms the wall is real and unclosed** — the world record at `t≈p^{1/4}` is a
power-saving off the trivial bound, a full half-power short of the prize — *and* it supplies a
genuine caution that the limiting **value distribution is non-Gaussian**, which bears directly on
the **exact constant** in δ* (see `deltastar-407-exact-constant-*`).

## Downloaded (valid PDFs, `~/papers/arklib/_407/`)

1. **`2003.06165.pdf` — di Benedetto, Garaev, García, González-Sánchez, Shparlinski, Trujillo,
   *New estimates for exponential sums over multiplicative subgroups and intervals* (J. Number
   Theory 2020).** THE CURRENT RECORD in the exact prize regime: for `|H|=t > p^{1/4}`,
   `max_{(a,p)=1}|Σ_{x∈H} e_p(ax)| ≤ t^{1−31/2880+o(1)}`. The exponent `31/2880 ≈ 0.0108` is a
   *power saving off the trivial `t`*, not square-root cancellation; at `t≈p^{1/4}` it is
   essentially `t^{0.989}`, a **full half-power above** the prize target `t^{1/2+o(1)}`. Size-only
   bound — the `n=2^μ` structure is neither used nor obstructive. https://arxiv.org/pdf/2003.06165

2. **`2401.04756.pdf` — Kowalski, *Exponential sums over small subgroups, revisited* (2024).**
   Cleanest modern exposition of Bourgain–Glibichuk–Konyagin: `|H| ≥ p^γ ⟹ Σ_{x∈H} e_p(ax) ≪
   |H|·p^{−ν(γ)}`, `ν` tiny/non-explicit. Rmk 1.2: even *nontrivial* bounds for subgroups of size
   `(log p)^C` are open; Shkredov gives the sharpest explicit `ν` (still a small power saving).
   This is the authoritative "best-known = power-saving" source. https://arxiv.org/pdf/2401.04756

3. **`1110.0078.pdf` — Bober, Goldmakher, *The distribution of the maximum of character sums*
   (GAFA 2012).** The rigorous Gaussian-maximum / extreme-value model — but proven for **full
   Dirichlet characters mod q**, where `M(χ)=max_t|Σ_{n≤t}χ(n)|` obeys a double-exponential tail
   law. The closest rigorous analogue of the `√(n·log)` heuristic; **never transferred to subgroup
   incomplete Gauss sums.** The template a prize proof of the *form* would imitate.
   https://arxiv.org/pdf/1110.0078

4. **`1207.1607.pdf` — Demirci Akarsu, Marklof, *The value distribution of incomplete Gauss sums*
   (Mathematika 2013).** ⚠️ **Caution paper.** Proves a genuine limit law for incomplete Gauss
   sums normalised by `√(#terms)` — and the limit is **NOT Gaussian**; it is an explicit
   theta/periodic family carrying arithmetic structure. Direct evidence that a clean Gaussian-max
   `√(n log)` law with the *bare* constant need not hold; the **constant** can be inflated by the
   non-Gaussian tail. https://arxiv.org/pdf/1207.1607

5. **`2112.05441.pdf` — Untrau, *Equidistribution of exponential sums indexed by a subgroup of
   fixed cardinality* (2021).** Subgroup-indexed sums equidistribute on explicit **hypocycloids /
   Minkowski sums** (structured, non-circular-Gaussian) — for *fixed* order `d` as `q→∞`, the
   opposite axis to the prize diagonal. A structural counterpoint to the Gaussian heuristic and
   the reason the fixed-`n` limit is *not* the prize regime. https://arxiv.org/pdf/2112.05441

## Not downloaded (access-gated — fetch manually)

- **Arnon, Boneh, Fenzi, *Open Problems in List Decoding and Correlated Agreement* (IACR ePrint
  2026/680).** The prize companion paper; the PDF endpoint returned the HTML landing page (gated).
  Manual: https://eprint.iacr.org/2026/680 (prize: https://proximityprize.org/). Frames the two
  challenges *combinatorially* over smooth `2^μ` domains; does not publicly reduce to a character-sum
  bound — consistent with the in-tree finding that the reduction is ours.

## Net (honest)

These five **confirm, and do not lift, the gate.** Record bound `t^{0.989}` (di Benedetto et al.),
no `√(n·polylog)` for any `t=o(√p)` subgroup family (Kowalski/BGK), Gaussian-max proven only for
*full* characters (Bober–Goldmakher), and two explicit **non-Gaussian** value-distribution results
(Demirci–Marklof, Untrau) warning that even the *constant* in `√(n log)` carries arithmetic
structure. The latter is what motivated this round's exact-constant probes
(`scripts/probes/probe_constant_additive_vs_mult.py`, `probe_betascaling_tail_law.py`).
