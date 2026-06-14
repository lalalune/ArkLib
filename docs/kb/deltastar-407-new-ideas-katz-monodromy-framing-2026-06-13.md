# New ideas tried on the BGK wall — Gauss-sum-family joint independence (Katz monodromy) is the fresh framing (2026-06-13)

Tried several genuinely new angles beyond the moment/phase-alignment routes. Most reduce to BGK; one gives
a new, geometric framing.

## Tried and reduces to BGK / inapplicable
- **Bilinear / Cauchy–Schwarz** (`η_b(μ_n)=Σ_{t∈T}η_{bt}(μ_{2^j})`): CS gives only the TRIVIAL
  `M(n)≤2M(n/2)` (factor 2, not √2); the √2 = the decorrelation = BGK. Lossy everywhere.
- **Katz / Sato–Tate compact support:** the periods have UNBOUNDED (growing ~√log) support (`M/√n` = 2.3,
  2.8, 3.5, 4.7 for n=8…64), so they are NOT semicircle/Sato-Tate (no hard edge); the max is a Gaussian
  large-deviation (Kluyver/random-walk), not an edge. Katz-compact does not apply.
- **GRH:** controls interval/short character sums, NOT multiplicative-subgroup sums (additive-combinatorial
  structure). No help — it is BGK not L-function.
- **Tail rigidity (Idea B):** period tail `~exp(−c·r²/n)`, measured `c≈0.8` (`>1/2`). So the conjecture
  `M≤√(2n ln p)` ⟺ **periods are √2-sub-Gaussian** (`c≥1/2`); `c≈0.8` confirms generically. But proving
  sub-Gaussianity of the dependent sum = the cumulant condition = BGK.

## The fresh framing (Idea A → Katz monodromy)
Measured: the Gauss-sum phase increments `arg g(χ_{s+1})−arg g(χ_s)` have variance ≈ uniform (3.23–3.31 vs
3.29) ⟹ **the Gauss-sum phases `arg g(χ_s)` are pseudorandom** — no Stickelberger/Hasse–Davenport low-degree
structure to exploit (rules out the "structured phases" escape). Since `η_b = (1/f)Σ_s \bar{χ_s}(b)g(χ_s)`
(f phased vectors of length √p), the random-phase model gives `max_b|η_b| ≈ √(f ln p)·√p/f = √(n ln p)` = the
floor. So:
> **CONJECTURE ⟺ joint independence/equidistribution of the coset Gauss-sum family `{g(χ_s) : χ_s trivial on μ_n}`.**
This is a **Katz monodromy / Deligne equidistribution** question (geometric), NOT raw additive-combinatorial
BGK. Individual equidistribution of `arg g(χ)` is PROVEN (Patterson; Heath-Brown–Patterson cubic); the JOINT
distribution of the family is the open part — but it is a different, possibly more tractable machine (large
monodromy ⟹ asymptotic independence ⟹ the bound). Known obstructions: Hasse–Davenport/Stickelberger create
SOME dependencies; the question is whether they are weak enough (the measured pseudorandomness says yes).

## Status (honest)
No new idea CROSSES the wall. But the exploration (a) rules out the structured-phase and Katz-compact escapes,
(b) sharpens the conjecture to "periods are √2-sub-Gaussian" (measured c≈0.8), and (c) reframes the core as
**joint independence of the coset Gauss-sum family = a Katz-monodromy problem** — a geometric target distinct
from BGK, connecting to Deligne/Katz equidistribution machinery. That reframing is the genuine new lead worth
handing to someone with the monodromy toolkit. Not a closure; no fabrication.
