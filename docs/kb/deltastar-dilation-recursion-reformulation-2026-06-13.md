# δ\* prize core — the dilation/Hadamard recursion reformulation (2026-06-13)

**Status: honest reformulation + independent re-confirmation of the wall. NOT a closure.**

Context: issue #407 (successor to #389). The δ\* prize floor reduces (governing law
`δ* = sup{δ : I(δ) ≤ q·ε* ≈ n}`) to the **worst-frequency incomplete character sum**
`B = max_{b≠0} |η_b|`, `η_b = Σ_{x∈μ_n} e_p(bx)`, with the floor target
`B ≲ C·√(n·log(q/n))` (conjecture (G), the BGK thin-subgroup sup bound).

## The recursion (exact, probe-verified `probe_dilation_recursion_tower.py`)

Write `f_i(b) = Σ_{x∈μ_{2^i}} e_p(bx)` (so `f_μ = η`, `f_0(b) = e_p(b)`). For the 2-power
tower `μ_{2^{i+1}} = μ_{2^i} ⊔ ζ·μ_{2^i}` (`ζ = ζ_{2^{i+1}}`):

> **`f_{i+1}(b) = f_i(b) + f_i(ζ·b)`**  (exact; verified across primes, `rec_ok=True`).

This is a **non-autonomous Hadamard/dilation recursion** — each level-(i+1) frequency value
is the sum of its level-i value and the value of its **dilate** `ζb`.

## The exact L²-doubling (clean, formalizable, but the LOSSY direction)

`Σ_{b∈F_p*} |f_{i+1}(b)|² = 2·Σ_b |f_i(b)|²` **exactly** (probe: ratios = 2.000 at every
level, every prime). Reason: the cross term vanishes,
`Σ_b f_i(b)·conj f_i(ζb) = Σ_{x,y∈μ_{2^i}} q·[x = ζy] = 0` because `ζ·μ_{2^i} ∩ μ_{2^i} = ∅`.
⟹ `Σ_b|η_b|² = n·(p−1)` (the diagonal/Parseval energy `= n²` after normalization). This is the
*trivial / Johnson-side* direction and gives nothing beyond the known `E = n²` floor.

## Why the recursion does NOT breach the wall (the precise diagnosis)

- **Sup direction:** `M_{i+1} := max_b|f_{i+1}(b)| ≤ 2·M_i` is the only free bound (children can
  align: at the level-(i+1) maximizer the two children `f_i(b), f_i(ζb)` are empirically exactly
  phase-aligned, `cos = 1`). That gives `M_μ ≤ 2^μ = n` — trivial. Beating it needs that
  alignment **cannot persist down a full path** `b → ζb → ζ²b → …` — the cocycle
  large-deviation statement (ratios `r_i ∈ [1/√2, √2]·√2`), already isolated and shown
  **not** capturable by any single-level lemma (`_DyadicPhaseChainingSubmaxRefuted`).
- **Moment direction:** L² cross term vanishes, but the `L^{2r}` (`r ≥ 2`) cross terms are
  exactly the additive energy / cumulant `E_r`, which is the **forced-positive anomaly**
  (`E_r^{Fp} > E_r^{char0}` for all `r > β+1`, `probe_forced_anomaly_crossover.py`). So the
  recursion preserves L² perfectly but its higher-moment cross-correlations grow — a crisp new
  statement of *why* the moment method caps at Johnson and cannot reach the floor.
- **Equivalence to BGK:** persistent alignment along a path `⟺` some dilate `bμ_n` concentrates
  in a short arc of `F_p` `⟺` `μ_n` fails equidistribution = the BGK/MRSS short-character-sum
  cancellation wall. SOTA `n^{0.989}` (di Benedetto), floor needs `n^{0.5}`, prize `β>4` outside
  every explicit theorem.

## Empirical (G) (probe, prize-shaped proper subgroups, `β=4`)

`max|η|/√(n·log(p/n))` = 1.069 (n=8), 1.199 (n=16), 1.260 (n=32) — bounded, slowly increasing,
consistent with the fleet's `C ∈ [1.14, 1.36]`. (G) is **robustly true empirically**; it has no
elementary proof.

## Honest bottom line

The dilation recursion is a clean dynamical reframing that (a) gives an exact, formalizable
**L²-doubling** brick and (b) sharpens the *reason* the wall is a wall (L² conserves, L^{2r}
cross terms = forced anomaly, sup needs the path large-deviation). It does **not** breach the
core. δ\* is pinnable only **conditionally** on (G); making it unconditional = the recognized
open BGK problem. No fabrication.
