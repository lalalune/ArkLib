# The explicit δ* upper bracket with the EXACT constant `2/s*` (Kambiré construction) (2026-06-13)

Read from the explicit construction (Kambiré, arXiv 2604.09724, *Proximity Gaps Conjecture Fails
Near Capacity over Prime Fields*, Apr 2026; IACR twin **ePrint 2026/782**). This turns the vague
"`δ* ≤ 1−ρ−Ω(1/log n)`" into a **closed formula with the exact constant**, derived from a clean
polynomial identity — and it is *exactly* the in-tree `SubsetSumHaloEnergy` object made into a theorem.

## 1. The construction (clean, explicit, unconditional via Linnik)
`H = ⟨ξ⟩` a subgroup of order `s = 2^α` in `F_p`; `D = μ_n = ⟨ω⟩`, `n = sm`, `k = (r−2)m`,
`C = RS[F_p, D, k]`. Take `f = X^{rm}`, `g = X^{(r−1)m}`. For each `λ` in the **distinct `r`-fold
sumset** `H^{(+r)} = {ξ_1+…+ξ_r : ξ_i ∈ H distinct}`, the identity over the `m`-th-power cosets
`H_j = {a∈D : a^m = ξ_j}`:
```
∏_{a∈H_1∪…∪H_r}(X−a) = ∏_{j=1}^r (X^m − ξ_j) = X^{rm} − λ·X^{(r−1)m} + R(X),   deg R ≤ (r−2)m = k,
```
shows `X^{rm} − λX^{(r−1)m}` agrees with the codeword `−R(X)` on `H_1∪…∪H_r` (size `rm = (1−δ)n`).
So **every `λ ∈ H^{(+r)}` is a bad scalar** at radius `δ = 1 − r/s`, while `[f,g]` is not jointly
`δ`-close. Bad-scalar count `= |H^{(+r)}| = C(s,r)` (when the sums are **distinct mod p** — ensured by
a quantitative Linnik choice `p ≡ 1 (mod n)`, `p < n^A`; for fixed deployed `p` it is the
`SubsetSumHaloEnergy` distinctness condition). Parameters: `ρ = (r−2)/s`, capacity `1−ρ`,
`η := (1−ρ) − δ = 2/s`.

## 2. The EXACT upper bracket (PROVEN, modulo mod-p distinctness)
`ε_mca(C,δ) ≥ C(s,r)/q`, so a radius is **bad** once `C(s,r) > ε*q`. Minimising the bad radius
`δ = 1−ρ−2/s` over valid `s` gives:

> **`δ* ≤ 1 − ρ − 2/s*`,  where `s* = min{ s : C(s, ⌊ρs⌋+2) ≥ ε*·q }`.**

Entropy form (`C(s,ρs) ≈ 2^{s·H₂(ρ)}`): **`s* ≈ log₂(ε*q)/H₂(ρ)`**, so
> **`δ* ≤ 1 − ρ − 2·H₂(ρ)/log₂(ε*·q)`**  (`H₂` = binary entropy).

For the **deployed budget** `ε*q ≈ n = 2^μ` (so `log₂(ε*q) = log₂ n`): `δ* ≤ 1−ρ−2H₂(ρ)/log₂ n`.
Computed exact `s*` and `δ*_upper` (verified, `probe`):

| ρ | H₂(ρ) | Johnson | δ*_upper (n=2^30) | δ*_upper (n=2^128) | capacity |
|---|---|---|---|---|---|
| 1/2 | 1.000 | 0.293 | **0.441** (s*=34) | 0.485 | 0.500 |
| 1/4 | 0.811 | 0.500 | **0.697** (s*=38) | 0.737 | 0.750 |
| 1/8 | 0.544 | 0.646 | **0.837** (s*=53) | 0.866 | 0.875 |
| 1/16| 0.337 | 0.750 | **0.910** (s*=73) | 0.932 | 0.938 |

This **narrows the upper bracket** from "capacity" to a concrete sub-capacity value with the exact
`2/s*` constant — sharper than the bare `1−ρ−1/log₂n` of BCHKS Table 2.

## 3. The closed conjecture (upper half PROVEN, lower half OPEN)
> **Conjecture (sumset-extremal δ*).** The Kambiré subgroup-`r`-fold-sumset construction is
> **extremal**: `δ*(RS[F_q,μ_n,k], ε*) = 1 − ρ − 2/s*`, `s* = min{s : C(s,⌊ρs⌋+2) ≥ ε*q}`.

| axis | score | why |
|---|---|---|
| novelty | 7 | construction is from 2026; the exact-constant closed form + extremality claim is the new packaging |
| insight | 8 | rate-entropy `H₂(ρ)` ↔ window depth via the subgroup sumset count; unifies the construction with `SubsetSumHaloEnergy` |
| proximity | 9 | exact prize regime — `ε*`, `ρ`, `q` explicit; deployed numbers computed |
| **feasibility** | 7 | **upper half is PROVEN** (the construction); the open half is the *specific* claim "no MCA attack beats the subgroup-sumset one" + "the list is small below `δ*`" — much narrower than the bare 25-yr exponent |

**Honest status:** this is a **closed formula** with **no free variables** and a **proven upper
half**. It is *not* a full proof — the lower half (extremality / list-smallness below `δ*`) is open,
so feasibility is 7, not 9. But it is the **sharpest, most prize-specific δ* statement of the
session**, and the open half is now a *specific extremality question about one explicit construction*,
not an asymptotic exponent.

## 4. Caveats / next steps (honest)
- **mod-p distinctness:** the count `C(s,r)` requires the `r`-fold sums distinct mod `p`. Linnik gives
  this for constructed `p<n^A`; for the deployed `p` it is the `SubsetSumHaloEnergy` condition
  (checkable per field). If sums collide, the bracket *weakens* (count `< C(s,r)`), which would push
  `δ*_upper` *up* — needs the deployed-field check.
- **Lower bracket (the open half):** prove no line with a *non-sumset* far direction beats
  `C(s,r)` bad scalars at `δ < 1−ρ−2/s*` — i.e. the subgroup sumset is the worst MCA attack. This is
  the remaining content; it is the `Λ(RS,δ)`-upper-bound / `B(μ_n)` character-sum question (the
  sibling "Shaw-operator" reduction: `δ*` ↔ worst Gaussian period `B(μ_n)=Θ(√(n log(q/n)))`).
- **Fetch:** ePrint 2026/782 (the IACR twin / subgroup version) for the full near-capacity failure
  statement and any matching lower bound.
