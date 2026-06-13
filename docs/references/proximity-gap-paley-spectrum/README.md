# Proximity Gap (#389) — Generalized Paley Graph / Gauss Period literature sweep

**Date:** 2026-06-13. **Driver:** the prize's open per-frequency core is a bound on the
worst-case **Gauss period** over the smooth domain `μ_n` (`n`-th roots of unity, `n | q−1`):

```
η_b := Σ_{y ∈ μ_n} ψ(b·y)   (ψ a nontrivial additive char of F_q, b ≠ 0),   B := max_{b≠0} |η_b|.
```

The Shaw-operator route (see `memory/issue389-shaw-operator-assessment.md`) is **√-loss-free** and
reduces the prize to bounding `B` (and the higher additive energies `E_k(μ_n)`) at the **prize scale
`B ≲ √(n·log(q/n)) = √(n·log(1/ε*))`** in the regime `n = q^{0.19}` (`n=2^30`, `q=2^158`, `n ≪ √q`).

## THE DICTIONARY (confirmed, the one rigorous gain) — Liu–Zhou `arxiv-1809.09829.pdf`

> **Thm 115 (Liu–Zhou, *Eigenvalues of Cayley graphs*):** `B = max_{b≠0}|η_b|` IS exactly the
> **non-principal spectral radius of the generalized Paley graph** `Cay(F_q, μ_n)` (= `Γ((q−1)/n, q)`),
> whose eigenvalues are the cyclotomic Gauss periods. So:
>
> **prize per-frequency bound `B ≤ 2√n`  ⟺  the generalized Paley graph `Cay(F_q, μ_n)` is RAMANUJAN.**

`2√(n−1)` is the **Alon–Boppana-optimal** threshold. Confirmed identical to our in-tree `η_b` /
`I(δ)` objects (`SubgroupGaussSum*`, `FarLineIncidenceEquivariance`).

## THE VERDICT: no paper in this corpus gives the bound at `n = q^{0.19}`

Verified rigorously across 20 papers (Podestá–Videla spectra `2310.15378`/`2604.06513`, Dawsey–McCarthy
cliques, Kim–Yip–Yoo `2405.09319`/`2309.09124`, Yip additive decompositions `2304.13801`, GCD-graphs
`2409.01929`, Kunisky `2303.16475`, Chung quasirandom, LPS/Ramanujan-bigraph, Pillay–Stonestrom
regularity, Green Sárközy, …):

- **Every delivered `η_b` bound is `√q`-scale** = Weil / Gauss-completion = the **vacuous wall**
  (`√q = 2^79` vs our target `2^18` — off by `~2^61`). Weil/RH-for-curves is vacuous for `n ≪ √q`.
- **The only sub-`√q` mechanism (semiprimitive Gauss periods, Liu–Zhou Thm 116 / Podestá–Videla
  Thm 6.1) is ARITHMETICALLY DEAD at the prize point.** Semiprimitive needs `k | p^t+1` with `t | r/2`;
  for `q = 2^158`, `r/2 = 79` is **prime** ⟹ `t=1`, `p^t+1 = 3`, and `k = (q−1)/n ≈ 2^128 ∤ 3`. Also the
  semiprimitive value `|η| ~ n/√q = 2^{-49}` is below the Parseval floor `√n = 2^15` — structurally
  inapplicable to a generic thin subgroup. (Semiprimitive subgroups are *additively structured* ⟹
  `√q`-scale eigenvalues ⟹ the wrong direction; we need *additively random* ⟹ `√n`.)
- **No paper bounds the additive energy `E_k(μ_n)`** at `n=q^{0.19}`. Yip `2304.13801` (the on-topic
  one) bounds additive *decomposition* (`μ_n ≠ A+B`), only for **FAT** subgroups `n ≥ q^{3/4}` — vacuous
  here. The optimal `E_2 = n^{2+o(1)}` (the 7/3 barrier) appears nowhere as proved.

## THE NAMED OPEN LEVER — Kim–Yip–Yoo `arxiv-2309.09124.pdf`, **Conj 2.12 (Paley Graph Conjecture)**

> `|Σ_{a∈A, b∈B} χ(a+b)| ≤ p^{−δ}|A||B|` for `|A|,|B| > p^ε`  (χ multiplicative, A,B ⊆ F_p).

This is the exact incomplete-character-sum cancellation that **would** close our per-frequency core
(it applies at `n = q^{0.19}`, needing only `n > q^ε`) — but it is **OPEN** (the Bourgain / sum-product
content). So: **prize per-frequency bound ⟸ Paley Graph Conjecture / Bourgain–Glibichuk–Konyagin
incomplete-character-sum bound for thin multiplicative subgroups.**

## WHERE THE BOUND ACTUALLY LIVES (next corpus to fetch)

NOT in the generalized-Paley/Cayley-spectrum literature. The thin-`n` `η_b` bound is in the
**incomplete-character-sum / sum-product** literature: **Bourgain–Glibichuk–Konyagin (2006)**,
**Shkredov** (`E_3` energy estimates), **Heath-Brown–Konyagin**. Fetch those next, specifically
BGK-style `|Σ χ(a+b)|` bounds for sets of small multiplicative doubling and Shkredov's third-energy
method.

## CONCRETE NEXT ACTIONS

1. **Formalize the dictionary** (Liu–Zhou Thm 115) as a Lean definition-level bridge: our `η_b`/`I(δ)`
   = spectral radius of `Cay(F_q, μ_n)` = Gauss period. States the open core as a named
   generalized-Paley-eigenvalue conjecture with citation (honest named-residual convention).
2. **Encode the Paley Graph Conjecture (Conj 2.12) as the SINGLE named conditional input** to a
   list-decoding/proximity capstone: `PaleyGraphConj(ε,δ) ⟹ B ≤ q^{−δ}√(n·…) ⟹ δ*-window`, a conditional
   theorem. Converts the open core into one cited hypothesis (parallel to the in-tree GVRepBound /
   additive-energy CRUX residual).
3. **Methodological template** — Kunisky `2303.16475.pdf`: the localization identity
   `α(G) = a + max_I ω(G_I)` → character-sum → packing-bound pipeline is structurally parallel to our
   `δ* = sup{δ : I(δ) ≤ q·ε*}` incidence law; reusable for the capstone.

## HONEST BOTTOM LINE

None of these 20 papers closes any prize piece or supplies a new usable inequality at `n=q^{0.19}`.
Their value is **conceptual confirmation**: our object `B` is exactly the generalized-Paley eigenvalue,
the `2√n` target is the Alon–Boppana/Ramanujan optimum, the semiprimitive shortcut is provably dead at
the prize point, and the open lever is the named **Paley Graph Conjecture** (= Bourgain thin-subgroup
incomplete-character-sum). The prize remains exactly at the additive-energy / sum-product CRUX.

## Files here
- `arxiv-1809.09829.pdf` — Liu–Zhou, *Eigenvalues of Cayley graphs* (**HIGH** — the dictionary, Thm 115/116).
- `arxiv-2309.09124.pdf` — Kim–Yip–Yoo, *Shifted multiplicative subgroups* (names **Conj 2.12**, the open lever).
- `arxiv-2303.16475.pdf` — Kunisky, *Spectral pseudorandomness / Paley clique* (**MEDIUM** — methodological template).
- `chung-randomlike.pdf` — Chung, *random-like graphs / quasirandomness* (**MEDIUM** — quasirandomness baseline).
- `arxiv-2310.15378.pdf` — Podestá–Videla, *Spectral properties of generalized Paley graphs* (canonical GP-spectrum reference; explicit only for `k≤4`/semiprimitive).

Full 20-paper extracts + per-paper bounds/regimes are in the workflow transcript
(`wf_d2b9d9e1-bec`); all 20 PDFs are in `~/papers/arklib/proximity-paley/`.
