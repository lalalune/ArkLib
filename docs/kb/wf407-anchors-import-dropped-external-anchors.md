# wf407 / anchors-import — verdict on the DROPPED external anchors of #407 §8 (J / H4)

**Date:** 2026-06-14 · **Thread id:** `anchors-import` · **Verdict: WALLED** (literature
acquisition complete; no dropped anchor supplies the prize `B`-form).

## Task

Assess each anchor dropped from #407 §8's literature table: does it give something the campaign
lacks, or is it already-walled? Anchors: (1) Ostafe–Shparlinski–Voloch (OSV), (2) Chang–Shparlinski
/ Kerr–Macourt bilinear double sums, (3) Myerson/Lehmer lacunary cyclotomic resultant maxima,
(4) KSV Conjecture 1.3 / Corvaja–Zannier / Makarychev–Vyugin subgroup Möbius-coincidence bounds.

## The prize object (what every anchor is measured against)

`B(μ_n) = max_{b≠0} |Σ_{x∈μ_n} e_p(b·x)|` — the **linear** (degree-1) incomplete Weil sum / Gauss
period over the order-`n` multiplicative subgroup `μ_n`, `n = 2^a` (`a ≤ 40` realizable),
`p ~ n·2^128`, index `m = (p−1)/n = 2^128`, density `n/p = 2^{−128}` (the **thinnest** regime,
`n < p^{1/4}` always — see `RegimePin.lean`).

## Per-anchor table (exact statements + verdict)

| anchor | exact statement (verbatim where possible) | does it help the prize? | wall it hits |
|--------|--------------------------------------------|--------------------------|--------------|
| **OSV** — Ostafe–Shparlinski–Voloch, *Weil Sums over Small Subgroups*, arXiv:2211.07739 (MPCPS 176 (2024) 39–53) | bounds `Σ_{x∈G} ψ(f(x))` nontrivially **in the range the classical Weil bound is already trivial** (small subgroup `\|G\|`), via AG × additive combinatorics. Requires `deg f = d ≥ 2`, `f` **not** of the form `g(x^k)`. Bound is **asymptotic** (`o(\|G\|)` / `p^{o(1)}`), not effective at an instance. | **No (wrong shape).** The prize `B`-form is the **linear** sum `f(x)=b·x` (`d = 1`); OSV's degree gate `d ≥ 2` **excludes** it. OSV is the right object only for the higher *tangent* sum `T_h = Σ_{w∈μ_n} χ^h(1−w)` (autocorrelation identity 407-T28/T18), and there only asymptotically (no `n=2^30` instance). | Right surface, no effective instance ⇒ same as the **fixed-index √-cancellation** wall (407-T07); asymptotic only. |
| **bilinear** — Chang–Shparlinski / Kerr–Macourt, lineage Bourgain–Glibichuk–Konyagin 0705.4573 | sub-`√q` double sums `Σ_a Σ_b α_a β_b e_p(a·b·…)` need **two** variables each of multiplicative density `> p^{3/7}` (BGK threshold). | **No (out of regime).** Already walled in `WF407_T02Shkredov.lean`: any factorization `μ_n = A·B` gives factors of density `≤ θ/2 = a/(2(a+128)) < 1/4 < 3/7` for `a ≤ 40` (`bilinear_factor_below_quarter`). The single thin set `μ_n` has no second density-`p^{3/7}` variable. | **W4 / density gate** (BGK `p^{3/7}`, HBK `q^{1/3}`) — `prize_below_quarter_power`. |
| **Myerson/Lehmer** — *How small can a sum of roots of unity be?* (lacunary cyclotomic resultant maxima) | small-sum law `f(k,n) ∈ [k^{−n}, n^{−k/4+o(1)}]` (upper valid only `k,n` both even). Companion: the house / resultant norm `\|N(Σ_{i∈S} ζ_n^i)\| ≤ (#S)^{φ(n)} ≤ n^{n/2}` (`φ(2^a)=n/2`). | **No (same wall).** The house `(#S)^{φ(n)}` is *exactly* the archimedean bound `HeightGateNormBound` already uses. Myerson refines the **minimum** (how small a defect sum can be) — the **wrong direction** for the gate, which needs an *upper* bound on the *max*. The house `n^{n/2} > p` for **all `a ≥ 8`** (gate dies at `n=64`, `gate_NOT_fires_64`). | **Height-obstruction wall** (`RESEARCH_SYNTHESIS_407` §4): every char-0 algebraic floor-certificate has norm-height `≥ 2^{φ(n)} ≫ p`. |
| **KSV** — Konyagin–Shparlinski–Vyugin, *Polynomial Equations in Subgroups*, arXiv:2005.05315 | **Thm 1.2:** `Σᵢ #{(u,v)∈𝒢²: Pᵢ(u,v)=0} < 12mn(m+n)g·h^{5/3}·t^{2/3}`, valid `12p^{3/4}h^{−1/4} ≥ t ≥ max{h², c₀(m,n)}`. **Conj 1.3 (open):** `∃ ε₀,A` s.t. for `#𝒢 ≤ p^{ε₀}` the Möbius coincidence `(α₁₁u−α₁₂)/(α₂₁u−α₂₂)=v` has `≤ A` solutions in `u,v ∈ 𝒢`. **Thm 1.6 (conditional on 1.3):** Markoff non-component count `#(ℳₚ∖𝒞ₚ) ≤ (log p)^B`, `B = 16 log A + c`. | **No (wrong axis; count not `B`).** The `t^{2/3}` bound is the **count of algebraic coincidences** on `μ_n²` (the orbit/list face, cluster 3), not the analytic character-sum sup-norm. The upper range `t ≤ 12p^{3/4}` **is satisfied** at the prize (`a ≤ 40 ≪ 0.75(a+128)`, `ksv_upper_range_satisfied`), so the theorem **applies in regime** — to the wrong object. Conj 1.3 is the genuine subgroup-Möbius-coincidence statement ("exactly the production regime" `#𝒢 ≤ p^{ε₀}`) but is **OPEN**. | **Count face / wall W1** (per-witness `C(w−1,d+1)`); Conj 1.3 itself open. |
| **Corvaja–Zannier** JEMS 15 (2013) 1927–1942 / **Makarychev–Vyugin** Arnold MJ 5 (2019) | the `t^{2/3}` **ancestors** of KSV Thm 1.2 (CZ: gcd `(u−1,v−1)` for `u,v` in a f.g. subgroup; MV: poly-equation solutions in `F_p` subgroups). KSV strictly **generalises/improves** both. | **No (subsumed by KSV).** Same count face, same `t^{2/3}` exponent, strictly weaker than KSV. | same as KSV (count face). |

## Decisive findings

1. **OSV is the wrong SHAPE.** The single sharpest fact: the prize sup-norm object is the
   **degree-1** (linear) Gauss period, and OSV (the one recent paper targeting `\|G\| < p^{1/4}`
   where Weil is vacuous) requires `deg f ≥ 2`. OSV therefore cannot bound `B` directly; it only
   reaches the higher *tangent* sum `T_h`, and asymptotically. (`osv_degree_excludes_linear_prize_object`.)

2. **KSV is right-regime but wrong-AXIS.** KSV's `t^{2/3}` count theorem **applies in the prize
   regime** (`ksv_upper_range_satisfied`: `n ≤ p^{3/4}` for `a ≤ 40`) — the first dropped anchor that
   is *in regime* — but it bounds the algebraic-coincidence count on `μ_n²`, which is the orbit/list
   face (cluster 3, wall W1), **not** the analytic `B`-form. `t^{2/3} < t` is a genuine count saving
   (`ksv_count_exponent_lt_one`) on the wrong axis. KSV Conj 1.3 ("exactly the production regime"
   `#𝒢 ≤ p^{ε₀}`) is the genuine subgroup-Möbius-coincidence statement, but **open**.

3. **Myerson = the height-obstruction wall already encoded.** The house `(#S)^{φ(n)}` Myerson
   studies IS the archimedean resultant bound in `HeightGateNormBound`; Myerson's improvement is on
   the *minimum* (defect smallness), the wrong direction, and the house `n^{n/2} > p` for all
   `a ≥ 8`. No new lever (`myerson_house_exponent_eq_half`: `φ(2^a) = n/2`).

## Artifacts

- `scripts/probes/wf407_anchors-import_regime.py` — exact regime check, all four anchors
  (OSV degree gate, KSV `t ≤ 12p^{3/4}` + `t^{2/3}` over `a∈[25,40]`, Myerson house `n^{n/2} > p`,
  CZ/MV subsumption).
- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/WF407_AnchorsImport.lean` — 4 axiom-clean
  elementary theorems (`osv_degree_excludes_linear_prize_object`, `ksv_upper_range_satisfied`,
  `ksv_count_exponent_lt_one`, `myerson_house_exponent_eq_half`).
- `PAPERS_NEEDED.md` — added KSV/CZ/MV/OSV rows (precise statements).

## What remains (new avenues for the next wave)

- **KSV Conjecture 1.3 as a list-count input.** Conj 1.3 bounds subgroup Möbius coincidences by
  `O(1)` for `#𝒢 ≤ p^{ε₀}` — the production regime. If proven, it caps the *bilinear* `(1,1)`
  coincidence count on `μ_n` independent of `n`, which is a cluster-3 (orbit/list) input feeding the
  super-code list bridge (407-T11). It does NOT touch the `B`-form, but it is a genuinely in-regime,
  *unconditional-if-resolved* count lever the campaign had not catalogued as such. Status: open NT
  conjecture (Markoff-flavored).
- **OSV → tangent-sum `T_h`.** OSV's `deg ≥ 2` AG×additive-comb method is the correct surface for
  the multiplicative tangent sum `T_h = Σ_{w∈μ_n} χ^h(1−w)` (the autocorrelation identity
  `A_h = m·conj(τ_h)·T_h`, 407-T28). Worth extracting the OSV exponent and checking whether it
  becomes effective on `T_h` at any in-regime `n` — currently asymptotic only.

## Honesty

No closure. The prize `B`-form (thin-subgroup `√`-cancellation, Paley Graph Conjecture) is
unchanged-open. This is a clean **walled** verdict: every dropped §8 anchor is the wrong shape
(OSV), the wrong axis (KSV/CZ/MV count), or the same proven wall (Myerson height-obstruction,
bilinear density gate). The §8 table dropped them for the right reasons.
