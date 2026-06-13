# δ* attack via value-concentration / curve-sparsity (2026-06-13)

Worked out while the IACR-blocked papers are being fetched manually. Synthesises the newly
acquired **Mérai–Shparlinski sparsity** (arXiv 1803.02165 — *Sparsity of curves and additive &
multiplicative expansion of rational maps over finite fields*) and **Lam–Leung** vanishing-sum
structure into a precise dissection of face (iv) (line–ball incidence) and where exactly it does
/ does not beat Johnson in the prize regime.

## 1. The exact reduction (face (iv), made fully explicit)

Code `C = RS[F_q, H, k]`, `H = ⟨g⟩` a multiplicative subgroup of order `n = 2^μ`, rate
`ρ = k/n`. Stack `(u₀, u₁)`, scalar line `w_γ = u₀ + γ u₁`. Per the in-tree far-coset law
(`epsMCA_ge_far_incidence`) and the ratio-multiplicity identity:

> `γ` is **bad at radius `δ`** ⟺ `w_γ` agrees with a single degree-`<k` codeword on
> `≥ (1−δ)n` coordinates ⟺ there is a value-pattern that a fixed rational map `R = −u₀/u₁`
> (entrywise on the eval points) realises on `≥(1−δ)n` points of `H` **AND** those points lie on
> a degree-`<k` polynomial.

`ε_mca(C,δ) ≈ (#bad γ)/q`, and `δ*(ρ) = sup{ δ : max-over-stacks #bad γ ≤ ε*·q }`,
`ε* = 2^{-128}`.

**Two nested constraints** — and separating them is the whole game:
- **(Concentration)** the map `R` takes one value on many points of `H` — bounded by
  `max_c deg gcd(P − cQ, X^n − 1)` where `R = P/Q`. *Pure subgroup question.*
- **(Code)** those agreement points additionally lie on a degree-`<k` curve. *The Reed–Solomon /
  list-decoding constraint.*

## 2. Why concentration ALONE only gives capacity (and is not enough)

The worst *pure-concentration* direction is the power map `R(x) = x^d` with `d ∣ n`: on
`H = ⟨g⟩` it takes each value of `⟨g^d⟩` exactly `d` times. Take `d = n/2 = 2^{μ−1}` (the largest
proper divisor of a 2-power): one value is hit `n/2` times. So a structured direction can force
agreement `n/2`, i.e. a bad scalar at every `δ ≥ 1/2`. At `ρ = 1/2` that is exactly **capacity**
`1−ρ = 1/2` — *not* an improvement, and it is the well-known capacity-side construction
(CS25-style covering). **Concentration alone reproduces the capacity heuristic, which is FALSE for
the true `δ*`** (the wall is strictly below capacity). So the L∞-concentration bound is necessary
but the binding constraint is the *code*.

## 3. The genuinely new lever: MS sparsity bounds the JOINT object

The point of Mérai–Shparlinski is that they bound `N_F(A,B)` for the *curve itself*, with the
**sparsity** `δ(F)` of the defining polynomial entering the exponent — not an L² average. Their
Theorem 1.3: for `F(X,Y)` with `F(X,Y^n)` absolutely irreducible ∀n, an interval `A=[1,H]` and a
subgroup `G` of order `e`,
```
N_F(A,G) ≪ d_X^{1/2} · H^{1/2} · max{ d·e^{−1/2}, d^{2/3} e^{1/3}, d_X^{1/2} d_Y^2 }.
```
Corollary 1.2: a degree-`d` rational map takes any fixed value `≤ H^{1/d+o(1)}` times on an
interval of length `H`. The `1/d` exponent is the sparsity payoff — **sub-`d` concentration**.

**The connection to the code constraint.** The "(Code)" constraint says the `(1−δ)n` agreement
points `(x, w_γ(x))` lie on the graph `Y = f(X)`, `deg f < k` — i.e. on a *low-degree, hence
sparse, curve*. Intersect with the smooth-domain relation `X^n = 1`. The joint incidence is
`N_{F}(H, ·)` for `F` = (the resultant coupling `Y=f(X)`, the ratio map, and `X^n−1`). **This is
exactly the `A,B`-both-structured (subgroup × low-degree-graph) incidence MS/Corvaja–Zannier
estimate — an L∞ bound that energy (L²) cannot produce.** The novel target:

> **Target conjecture (sparse-joint-incidence).** For the smooth RS far-coset curve, the joint
> incidence of `{agreement with a degree-<k codeword}` ∩ `{H-concentration of the far map}` is
> `≤ poly(n)` for all `δ < f(ρ)` with `f(ρ) > 1−√ρ` (beyond Johnson), with `f` an explicit
> closed function of `ρ` driven by `δ(F)` (curve sparsity). The crux is whether the far-coset
> curve is **sparse enough** (`δ(F) = o(d²)`) for the MS exponent to clear Johnson.

If `poly(n) ≤ ε*·q` in the deployed field (`q ≳ 2^{160}` makes `poly(n) ≪ 2^{−128}q`), this pins
`δ* ≥ f(ρ) > Johnson` — the prize lower bracket. **Kill-criterion:** if the far-coset curve is
*dense* (`δ(F) ≈ C(d+1,2)`), MS gives only the Johnson-equivalent bound and this lever dies,
collapsing to the open energy problem.

## 4. What is computable NOW (the falsifiable fork)

The whole lever turns on **one measurable quantity**: the sparsity `δ(F)` of the explicit
far-coset curve, and whether the structured-direction agreement actually exceeds Johnson while
staying `≤ poly(n)` below capacity. Probe `probe_value_concentration.py`:
- builds small smooth RS codes `RS[F_p, H, k]`, `H` of 2-power order;
- for structured far directions (power maps `x^d`, `d∣n`, and the inverse map) computes the exact
  max agreement of `u₀+γu₁` with a degree-`<k` codeword over all `γ∈F_p`;
- reports `δ*_emp = 1 − maxagree/n` vs Johnson `1−√ρ` vs capacity `1−ρ`, and the per-direction
  value-multiplicity (concentration) so we can see concentration-vs-code separation directly.

**Decision rule (the user's filter applied):** if structured directions cluster at *capacity*
(concentration unconstrained by the code) → the code constraint is doing nothing special and this
is the known capacity construction (discard). If they cluster *strictly between Johnson and
capacity* at a value matching an explicit sparsity exponent → the sparse-joint-incidence target is
live and we formalise the MS bound for that curve. If they collapse to *Johnson* → lever reduces
to Johnson (discard).

## 5. Lam–Leung note (face (iii), parked but recorded)
2-power vanishing sums decompose into antipodal pairs `ζ+(−ζ)=0` (Lam–Leung, single prime p=2);
robust to weight 21 (Christie–Dykema–Klep). This compresses the *vanishing-relation census* but —
per the sweep — does **not** bound the ℓ-fold *sumset* (the superpoly side, Yip 2304.13801:
`G ≠ A+A`). Keep for the census-supply face; it is not the δ* lever.
