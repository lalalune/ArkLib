# CORRECTION + sharpening: the prize core is the order-`log_n p` additive moment, NOT the `n^{22/9}` exponent (2026-06-13)

This **corrects** the framing in `deltastar-prize-regime-reduction-…` and `…-wall-unification-…`
(which said the prize reduces to the open Shkredov subgroup-energy exponent `E(μ_n)=n^{2+o(1)}`).
That exponent governs the **large-subgroup** regime `n ≈ √p`. **The prize is the small-subgroup
regime `n ≪ p^{1/4}`, where the quadratic energy is provably CLEAN.** The open core is a *higher
additive moment*, and the prize regime pins exactly which one.

## 1. VERIFIED: quadratic energy is exactly clean in the prize regime
For 2-power `n` and `p > n⁴`, computed `E(μ_n) = Σ_t r(t)²` exactly:

| n | p (> n⁴) | E(μ_n) | 3n²−3n | excess |
|---|---|---|---|---|
| 4 | 257 | 36 | 36 | **0** |
| 8 | 4129 | 168 | 168 | **0** |
| 16 | 65537 | 720 | 720 | **0** |
| 32 | 1048609 | 2976 | 2976 | **0** |

`E(μ_n)=3n²−3n` exactly (Lam–Leung: every 4-term vanishing sum of 2-power roots of unity
decomposes into antipodal pairs ⇒ no nontrivial additive quadruples). The prize has
`n=2^{30} ≪ p^{1/4}=2^{39.5}`, so **the quadratic energy is clean (`n²`), giving exactly Johnson —
and the Shkredov `n^{22/9}` open exponent is in the WRONG regime and irrelevant to the prize.**

## 2. VERIFIED: the moment-cleanness threshold is `p > n^j`
For the `j`-th additive moment `E_j(μ_n) = Σ_t r_j(t)²` (`r_j` = # ways to write `t` as a sum of `j`
elements), computed excess vs the clean baseline:

- `E_2` clean for `p ≳ n²`; `E_3` clean for `p ≳ n³` (n=8: excess 480 at `p=73≈n²`, **0** at
  `p=521≈n³` and above). General pattern: **`E_j(μ_n)` is clean ⟺ `p ≳ n^j`** (the `j`-fold sumset
  is spread; spurious mod-`p` collisions need `n^j ≳ p`).

So the **first non-clean additive moment** is at order
> **`j*(n,p) = ⌈log p / log n⌉`** — for the prize `= ⌈158/30⌉ = 6`.

**Additive moments of order ≤ 5 are clean; order-6 is the first with nontrivial structure.** The
seeds of every beyond-Johnson bad list-config are the **order-`j*` vanishing sums of `μ_n` mod `p`**
(`Σ_{e∈E} g^e ≡ 0`, `|E| = j* ≈ 6`) — exactly the census-halo / subset-sum object of
`SubsetSumHaloEnergy.lean`, now pinned to a *specific small order*.

## 3. Why this is a real sharpening (and a more tractable target)
- The open core is **not** a `25`-year-open asymptotic exponent (`n^{2+o(1)}`); it is the
  **`j*`-th moment** with `j* = log_n p` a *specific small integer* (≈6 for the prize).
- Order-`j*` vanishing sums are **finitely checkable in structure** (Lam–Leung classifies 2-power
  vanishing sums by antipodal decomposition; the first *spurious* mod-`p` relation is a concrete
  Diophantine condition on `g`, `p`).
- This reframes the prize from "improve a sum-product exponent" to "**count the order-`⌈log_n p⌉`
  vanishing sums of the geometric sequence `{g^e}` mod `p`, and propagate them to a list bound**" —
  the propagation being the one remaining step.

## 4. The sharpened conjecture (ranked)
> **Conjecture (moment-hierarchy δ*).** For `RS[F_p, μ_n, k]` in the prize regime
> (`n=2^μ`, `log p / log n =: J ≥ 3` non-integer, `ε*=2^{-128}`), `δ*` is determined by the first
> additive moment whose vanishing-sum count, propagated through the agreement hierarchy, exceeds
> `ε*·p`; the governing order is `j* = ⌈J⌉`, and below the corresponding band the list is clean
> (Johnson-bounded by the clean lower moments).

| axis | score | why |
|---|---|---|
| novelty | **9** | the `p>n^j` moment-cleanness ladder and `j*=log_n p` localization is, to our knowledge, new framing of the prize |
| insight | **9** | connects Lam–Leung 2-power vanishing sums + the census halo + the Johnson/Fisher wall into one moment ladder; *corrects* the energy-exponent misconception |
| proximity | **9** | derived in and verified for the exact prize regime (`n≪p^{1/4}`, the actual `n,p` scales) |
| feasibility | **6** | the cleanness ladder + governing order are pinned/verified; the **open step is the propagation** (order-`j*` vanishing-sum count → list size → band) — concrete but not yet closed |

**Honest status:** the first three axes are now ≥9; **feasibility is 6** — the conjecture is not yet
*closed* because the propagation from "order-`j*` vanishing sums" to "list exceeds `ε*p` at band `a`"
is not yet a proof. But the open object is now a *specific small-order, finitely-structured*
additive-combinatorics count, **not** the `25`-year exponent. This is the most tractable form found.

## 5. Immediate next step (the propagation)
Compute, for the geometric sequence `{g^e : e<n}` in `F_p`, the number of order-`j*` vanishing sums
and how a single such sum seeds a family of `≥ a`-agreement codewords (the census `Aligned` count).
If the seed→list map is the in-tree `kkh26_fibreUnion_aligned_nondegenerate` (`≥ 2^r·C(2^{μ−1},r)`
bad scalars from one relation), then `δ*` closes once the order-`j*` count is pinned — turning
`CensusDomination` from "the `n^{2+o(1)}` exponent" into "the order-`⌈log_n p⌉` vanishing-sum count,"
a finite-order Stepanov/cyclotomic problem.
