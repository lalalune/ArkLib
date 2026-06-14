# Direct attack on the core inequality `B(μ_n) ≤ C√(n log(p/n))` (2026-06-13)

Full-effort direct proof attempt on the single open core, with every rigorous tool. Documents what
holds, what breaks, and the precise mathematical obstruction. **Honest: not proven; the attack
localizes the obstruction to one statement (Gauss-sum non-conspiracy).**

## Target
`n=2^k`, `n | p−1`, `n ≪ √p`. `η_b = Σ_{x∈μ_n} e_p(bx)`. Prove `B := max_{b≠0}|η_b| ≤ C√(n·log(p/n))`.
(Equiv: `E_r(μ_n) ≤ (Crn)^r`, `r≤log(p/n)`; closes `δ*=1−ρ−2/s*` via the proven scaffold.)

## Step 1 — exact Gauss-sum formula (rigorous)
`1_{μ_n}(x) = (1/f)Σ_{ψ: ord(ψ)|f} ψ(x)`, `f=(p−1)/n`. Fourier transform:
> `η_b = (1/f)[ −1 + Σ_{ψ≠χ₀, ord(ψ)|f} \barψ(b)·g(ψ) ]`, `g(ψ)=Σ_x ψ(x)e_p(x)`, `|g(ψ)|=√p`.
So `B = (1/f)·max_b |Σ_{ψ≠χ₀} \barψ(b) g(ψ)| + O(1/f)`. The core is the **sup over `b` of an
`(f−1)`-term sum of Gauss sums with character-value phases**.

## Step 2 — L² is exactly right (rigorous, gives the average)
`Σ_b |Σ_ψ \barψ(b)g(ψ)|² = (p−1)Σ_{ψ≠χ₀}|g(ψ)|² = (p−1)(f−1)p`. So `avg_b|·|² = (f−1)p`, giving
`η_b ≈ (1/f)√(fp) = √(p/f) = √(n·p/(p−1)) ≈ √n` on average (Parseval `Σ_b|η_b|²=pn`). ✓ matches data.
**The whole difficulty is average (`√n`) → max (`√(n·log(p/n))`): a sub-Gaussian / no-large-deviation
gap.**

## Step 3 — every standard tool gives only the trivial bound (rigorous failures)
- **Weil / Pólya–Vinogradov:** `|g(ψ)|=√p` ⟹ `B ≤ (1/f)(f−1)√p ≈ √p`. (The trivial `√p`; `≫ √(n log)`.)
- **Young's inequality on `E_r`:** `||1_μ^{*r}||_2 ≤ ||1_μ||_1||1_μ^{*(r−1)}||_2` ⟹ `E_r ≤ n^{2r−1}`
  (no cancellation; trivial).
- **Weil on the moment `E_3`:** `Σ_b η_b^6 ≤ (max η_b^4)Σ_b η_b² ≤ p²·pn` ⟹ `E_3 ≤ p²n ≫ n³`. Useless.
  (So even the FIRST nontrivial energy `E_3 ≤ Cn³` is not reachable from Weil + Sidon `E_2`.)
- **Stepanov / sum–product (BGK):** gives nontrivial cancellation only for `n > p^ε` with
  triple-exponentially small savings — the prize regime `n ≪ √p` (often `≪ p^{1/4}`) is out of reach.
- **2-power norm bound (cyclotomic):** a spurious `2r`-relation `D∈Z[ζ_{2^k}]`, `|σ(D)|≤2r ∀σ`,
  `p|D` needs `p ≤ (2r)^{2^{k−1}}` — astronomically satisfied at large `k`, so **no obstruction to
  spurious relations**; the count is uncontrolled.

## Step 4 — the precise obstruction (where the proof genuinely stops)
`B ≤ √(n log(p/n))` ⟺ `max_b |Σ_{ψ≠χ₀} \barψ(b) g(ψ)| ≤ √(f·log f)·√p` ⟺ **the `f−1` Gauss sums
`{g(ψ) : ord(ψ)|f}` do not conspire**: for every `b`, the phases `\barψ(b)·arg(g(ψ))` exhibit
square-root cancellation (`√(f log f)`), never coherent alignment (`f`). This is a **quantitative
no-large-deviation statement for Gauss-sum arguments** — beyond mere equidistribution (Katz), which
controls the *distribution* of `{g(ψ)/√p}` but not the *sup over `b`* of the weighted sum. It is the
recognized open problem (Szabó: high-moment upper bound "hopeless with current knowledge"; equivalently
the additive-energy / almost-Ramanujan / Λ(2r)-set statement).

## Step 5 — what the attack DID establish (honest positives)
- The target is *exactly* the Gauss-sum sup-norm; the average `√n` and the Parseval/L² structure are
  rigorous and match data.
- A single bad `b` ⟺ one coset `bμ_n` additively concentrated ⟺ a coherent Gauss-sum alignment —
  three faces of the same obstruction, now unified.
- Confirmed the obstruction is NOT removable by Weil/Young/Stepanov/2-power-norm — these all give
  trivial or BGK bounds — so a genuinely new equidistribution-with-no-large-deviation input is
  required. This rules out the "easy" routes definitively.

## Verdict
**Not proven.** The direct attack reduces the prize, rigorously, to: *the Gauss sums `g(ψ)`,
`ord(ψ) | (p−1)/2^k`, satisfy a uniform (sup-over-`b`) square-root-cancellation bound* — a frontier
open problem in analytic number theory. Every standard tool was applied and gives only the trivial
`√p`. No fabrication; the obstruction is real and precisely located.
