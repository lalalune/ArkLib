# The Ubiquitous Quantity: 50 Theories for *Why* It Appears Everywhere (#407)

**The object.** One quantity recurs across the whole #407 campaign, wearing a different name in
each domain but provably equal each time:

| Domain | Name of the quantity |
|---|---|
| Analytic number theory | `M(n) = max_{b≠0}|η_b|`, `η_b = Σ_{x∈μ_n} e_p(bx)` — max incomplete Gauss sum / Gaussian period over a multiplicative subgroup |
| Spectral graph theory | `λ₂` = non-principal eigenvalue of the generalized Paley graph `Cay(F_q, μ_n)` (Ramanujan ⟺ `λ₂ ≤ 2√n`) |
| Algebraic number theory | the **house** (largest absolute conjugate) of a degree-`m` algebraic integer with known power sums |
| Fourier analysis | sup-norm of the inverse-DFT of a **fixed-modulus** (`√q`) vector of Gauss sums |
| Additive combinatorics | Fourier-dual of the additive energy `E(μ_n)`; the BCHKS r-fold subset-sum count |
| Coding theory / the prize | the worst-case far-line incidence pinning `δ*` |
| Sum-product / BGK | the `√`-cancellation in incomplete character sums over thin subgroups |

The prize needs `M ≤ √(2n log m)` (worst case); SOTA is `n^{0.989}` (di Benedetto), need `n^{0.5}`.
**The recurring failure mode:** every algebraic identity *renames* the quantity (5-identity rigidity);
every second-order method *caps at Johnson* (meta-theorem); the one exact Gauss-sum reduction
(Hasse–Davenport) strips `3n/4` of the DOF and stops at the irreducible `n/4` Katz monodromy phases.

**The meta-question (this doc).** *Why* is this one quantity the answer in so many unrelated places?
What structure forces it? Why is it open everywhere at once? 50 theories, ranked, then ground out.

Scoring: **N**ovelty / **L**ikelihood-true / **R**elevance-to-prize / **F**easibility (1–10 each).

---

## TIER S — the unifying meta-theory: it is the maximum of a log-correlated field

> **The thesis.** `√(2·Var·log N)` is the *universal* leading-order maximum of **any** log-correlated
> field of `N` points. The reason this quantity appears identically in ζ-on-the-critical-line, CUE
> characteristic polynomials, Paley eigenvalues, and Gauss periods is that **all four are
> log-correlated fields** (their log-modulus has covariance `≍ −log(distance)`). The prize floor
> `√(2n log m)` is exactly the log-correlated max with `Var = n`, `N = m`. This is the answer to
> "why everywhere": **log-correlation is the universal structure of barely-dependent exponential
> sums, and its maximum is a fixed law.**

| # | Theory | N | L | R | F |
|---|---|---|---|---|---|
| 1 | **Gauss periods are a log-correlated field**; `max = √(2n log m) − (3/4)√(2n/log m)·loglog m + O(1)` (the Fyodorov–Hiary–Keating / branching-random-walk law). Proven machinery: Bramson, Aïdékon, Madaule, Arguin–Bourgade–Radziwiłł. | 10 | 7 | 10 | 6 |
| 2 | **Covariance-log hypothesis** (the testable core of #1): `Cov(η_a, η_b) ≍ −c·log dist_m(a,b)` for a natural metric on `ℤ_m` (2-adic / multiplicative). If true, #1 follows from BRW universality. | 9 | 6 | 10 | 7 |
| 3 | **Freezing transition.** `T_r / Wick → 1` exactly at `r ≍ log m` IS the `β_c = 1` freezing of the field's partition function `Σ_b e^{β|η_b|}`. Explains *why the depth is `log m`* (not a coincidence). | 9 | 7 | 9 | 7 |
| 4 | **Universality of `√(2 Var log N)`** across ζ-max, CUE-max, Paley-λ₂, Kloosterman — all log-correlated Frobenius fields. This IS the cross-domain ubiquity, as a theorem (Fyodorov–Keating conjecture circle). | 10 | 6 | 8 | 5 |
| 5 | **Subleading correction = exact δ\*.** The `−(3/4)loglog` term is the precise worst-case refinement the prize needs (pins δ* including worst case, not just leading order). | 9 | 6 | 10 | 5 |
| 47 | **Large-deviation / Coulomb-gas.** Periods = a 1D log-gas; `max` = rightmost charge (Fyodorov–Bouchaud freezing); the rate function `I(λ)` at threshold gives the tail `#{|η_b|>λ√n}`. | 8 | 6 | 9 | 6 |
| 49 | **Spectral form factor at Heisenberg time.** `T_r` = SFF of the arithmetic system; the dip-ramp-plateau pins the max via RMT spectral statistics. | 9 | 5 | 7 | 4 |

## TIER A — genuinely novel cross-domain transfers (under-explored)

| # | Theory | N | L | R | F |
|---|---|---|---|---|---|
| 19 | **Iwaniec–Sarnak amplification.** `M` = L^∞-norm of an arithmetic eigenfunction; build a *Hecke-style amplifier* from the multiplicative structure to boost the `√n` average into a worst-case bound. Real technique, never applied here. | 9 | 5 | 9 | 5 |
| 48 | **Fourth-moment phenomenon (Nualart–Peccati).** If a fourth-moment criterion holds, `T_2` controls all `T_r` → would collapse `r≍log m` to `r=2` (which is char-free!). High-value even if it turns out FALSE — testable now. | 9 | 3 | 10 | 8 |
| 50 | **Fourier-uncertainty fixed point.** The quantity is the unique self-dual extremal of the DFT restricted to subgroup-supported functions (Bourgain–Clozel–Kahane / `+1`-eigenfunction); ubiquity = it's a Fourier-uncertainty extremal. | 9 | 4 | 7 | 5 |
| 29 | **Compressed sensing / coherence.** `M` = mutual coherence of the DFT-submatrix indexed by `μ_n`; RIP/Welch-bound theory bounds coherence. Novel transfer; Welch bound gives only the `√` average (likely caps at floor). | 8 | 4 | 7 | 6 |
| 24 | **Gaussian multiplicative chaos.** The period field `e^{|η_b|}` is a GMC; total mass / max = GMC theory (Berestycki, Rhodes–Vargas). Connects to #1 via the same loglog. | 9 | 5 | 8 | 4 |
| 31 | **Peak-to-average power ratio (PAPR).** `M`/avg = PAPR of the Gauss-period sequence; OFDM/Rudin–Shapiro theory bounds PAPR for *structured* sequences. Novel transfer. | 8 | 4 | 6 | 5 |
| 21 | **Amplifier from multiplicativity.** A concrete amplifier: `Σ_l c_l χ^l(b)` chosen to peak at the worst `b`; the dual bound is a moment in disguise — test if it beats Cauchy–Schwarz. | 8 | 4 | 8 | 6 |
| 37 | **Free probability.** Empirical period distribution = free additive convolution of Bernoullis; `max` = edge of the free convolution. Edge ≠ support-edge in general (atoms), test. | 8 | 4 | 6 | 5 |
| 35 | **Pila–Wilkie point counting.** The large periods are rational points on a definable set; o-minimal counting bounds `#{b : |η_b| > λ}`. Novel; likely the wrong category (arithmetic, not transcendental). | 8 | 2 | 5 | 4 |
| 45 | **Partial L-function special value.** `M` = residue/special-value of a Dirichlet series built from the periods; the explicit formula transfers the max to zero-density. | 8 | 3 | 6 | 3 |

## TIER B — spectral / arithmetic-geometry (the established faces, sharpen them)

| # | Theory | N | L | R | F |
|---|---|---|---|---|---|
| 6 | Paley-graph `λ₂` = Ramanujan; ubiquity via association schemes (every mult. subgroup ⟹ a scheme). | 5 | 9 | 7 | 6 |
| 7 | Frobenius house: Deligne `√q` per conjugate; the SUP needs effective equidistribution rate (the gap). | 6 | 8 | 8 | 5 |
| 8 | Katz monodromy `n/4` DOF = effective-equidistribution dimension; max-concentration = Katz rate. | 7 | 7 | 8 | 4 |
| 9 | Sato–Tate edge: `η_b/√n` equidistributes; `M` = right-edge finite-`m` fluctuation. | 6 | 6 | 7 | 5 |
| 44 | Self-dual circulant operator norm — universal wherever a cyclic convolution lives. | 6 | 6 | 5 | 5 |

## TIER B — additive combinatorics / number theory faces

| # | Theory | N | L | R | F |
|---|---|---|---|---|---|
| 11 | Fourier-dual of additive energy; `M² ≥ E/|G|`, gap = non-flatness. Caps at Johnson (known). | 4 | 9 | 6 | 7 |
| 12 | BCHKS r-fold subset-sum (the framework authors' Conj 1.12). The recognized open form. | 5 | 8 | 9 | 4 |
| 15 | Lehmer / Schinzel–Zassenhaus: house *lower* bounds; ubiquity via Galois on roots of unity. | 7 | 5 | 5 | 4 |
| 17 | Bilu Galois equidistribution governs the house (average, not max — known √-loss). | 5 | 7 | 5 | 5 |
| 39 | Paley clique number (`√q`, itself open!) controlled by the same `λ₂` — a *sibling* open problem. | 7 | 6 | 6 | 4 |

## TIER C — "why never solved" (structural obstruction theories, mostly to confirm-refute)

| # | Theory | N | L | R | F |
|---|---|---|---|---|---|
| 25 | Hardness web: any proof simultaneously settles Paley + Lehmer + BCHKS (so it's "as hard as several"). | 6 | 7 | 5 | 5 |
| 26 | Cohomological char-`p` obstruction (Fermat–Betti / GLT no-go at `r=2`) is genuine, not removable. | 6 | 7 | 6 | 4 |
| 27 | Meta-theorem: no second-order method beats Johnson (Cauchy–Schwarz). PROVEN in-tree. | 4 | 10 | 6 | 9 |
| 28 | Algebraic rigidity: every exact identity is volume-preserving (5-identity result). PROVEN-adjacent. | 4 | 9 | 5 | 8 |

## TIER C — further domains (breadth; mostly expected to refute, a few wildcards)

| # | Theory | N | L | R | F |
|---|---|---|---|---|---|
| 10 | Eigenvalue linear-statistics / RMT edge (Tracy–Widom vs Gumbel — which?). | 7 | 5 | 6 | 4 |
| 14 | Universal "is this set Fourier-flat" object (the L^∞ of an indicator's transform). | 5 | 7 | 5 | 6 |
| 20 | QUE / Berry random-wave sup-norm bounds transfer. | 7 | 4 | 6 | 4 |
| 22 | Edge-fluctuation of an eigenvalue ensemble. | 6 | 4 | 5 | 4 |
| 23 | Borell–TIS concentration (gives concentration, not the constant — known gap). | 4 | 8 | 4 | 6 |
| 30 | Dual-distance / covering-radius extremal in coding theory. | 5 | 6 | 6 | 5 |
| 32 | Discrepancy of the orbit of mult-by-`g` (equidistribution rate). | 6 | 5 | 5 | 5 |
| 33 | Small-denominator / Diophantine approx of the period. | 6 | 3 | 4 | 4 |
| 34 | p-adic / Berkovich non-archimedean house. | 7 | 3 | 4 | 3 |
| 36 | TCS pseudorandomness: bias of the `ε`-biased set from `μ_n`. | 5 | 6 | 5 | 6 |
| 38 | Largest character value of a Gelfand pair / class function. | 6 | 5 | 5 | 4 |
| 40 | Partial-difference-set / design existence governed by `λ₂`. | 6 | 5 | 5 | 4 |
| 41 | Obstruction to a deterministic CLT (failure of exact Gaussianity). | 7 | 5 | 6 | 5 |
| 42 | Second-order Frobenius / variance of equidistribution. | 6 | 5 | 5 | 5 |
| 43 | The canonical hard instance of the universal "L^∞ vs L^p gap". | 6 | 6 | 5 | 5 |
| 46 | Arithmetic Gaussian free field restricted to a subgroup (GFF connection → #1). | 8 | 5 | 7 | 4 |
| 13 | Sum-product spectral gap (Plünnecke–Ruzsa sees it; vacuous at index `m`). | 4 | 7 | 4 | 5 |
| 16 | Mahler-measure bound on the house. | 5 | 5 | 4 | 4 |
| 18 | Discriminant/resultant (lower-bound-only — known). | 3 | 8 | 3 | 6 |

---

## Initial verdict (pre-grind)

**The cross-domain ubiquity has a single best explanation: TIER S — the quantity is the maximum of a
log-correlated field, and `√(2 Var log N)` is the universal law of such maxima.** This reframes the
prize from "prove a `√`-cancellation bound" (BGK, stuck 25 years) to "prove the Gauss-period field is
log-correlated" (#2) — a *different* statement with *different* (probabilistic) machinery that the entire
BGK-centric literature has never applied. It also predicts the **exact** answer including worst case
(the FHK loglog correction, #5), which is precisely the prize's "pin δ* exactly including worst case."

**The single highest-value testable wildcard: #48 (fourth-moment phenomenon)** — if a Nualart–Peccati
fourth-moment criterion holds, the depth collapses `r≍log m → r=2`, which is char-free. Almost certainly
too good to be true, but cheap to test and decisive either way.

The workflow `prize-407-ubiquity-grind` triages all 50, deep-grinds the survivors with numerics in the
prize-adjacent regime (proper subgroup, `p=n^{4..5}`, multiple large primes, never the full group),
and adversarially verifies every TRUE/PROMISING verdict.

---

## GRIND RESULT (50 agents, ~2.3M tokens, numerics in prize regime) — **0 survivors; the crown theory REFUTED**

**The TIER-S meta-theory (log-correlated field) is numerically FALSE — and that is the most valuable
output.** Direct measurement of the period field's autocovariance (confirmed independently by 4 agents and
re-verified inline, `scripts/probes/probe_period_autocovariance.py`):

> `Cov(η_a, η_b)` for `dist ≥ 1` is **EXACTLY `−Var/(m−1)`, distance-independent** (`stdCov = 0.0000`
> across all tested `p ~ n⁴`). The marginal is `N(0,1)`-like (std 1.000, tail counts match i.i.d.-Gaussian
> `K/p ≈ 0.044 ≈ Pr|Z|>2`). This is the signature of an **exchangeable family with a single linear
> constraint** (`Σ_{b≠0} η_b = −n`): "white noise on the constraint surface."

Consequences:
- The periods are **MORE independent than log-correlated** — no log-covariance decay, no branching
  structure, no GFF. The max follows the **i.i.d.-Gumbel law (subleading coefficient `−1/2`)**, NOT the FHK
  branching-random-walk law (`−3/4`, which would *suppress* the max below i.i.d.). So theories #1, #2, #5,
  #24, #46, #47 (the whole log-correlated/GMC/Coulomb-gas/FHK cluster) are FALSE in the prize regime.
- The leading order `√(2n log m)` IS correct — but only as the **i.i.d. extreme-value floor**, which merely
  re-derives the already-in-tree sub-Gaussian conjecture and supplies **no new leverage** on the open char-`p`
  depth-`r≍log m` transfer.

**All 47 others reduce to the wall (40), to Johnson (5), or are false (2).** Decisive recurring kills:
- **Amplification (#19, #21)** — machine-confirmed: the Iwaniec–Sarnak amplifier *is* the shifted moment
  `D_r(h) = p·Σ_t N_r(t)² e_q(−ht)`, positive-definite, `argmax_h = 0` = flat energy. **No amplifier beats
  flat energy** → second-order → meta-theorem.
- **Fourth-moment phenomenon (#48)** — Nualart–Peccati is a char-0 Wiener-chaos theorem with *no char-`p`
  content; "collapse to `r=2`" only re-derives Lam–Leung sub-Gaussian and leaves the char-`p` break untouched;
  its LD guise is the already-proven `JohnsonFourthMomentNoGo`.
- **RIP/coherence (#29), PAPR (#31), free-convolution edge (#37), Fourier-uncertainty (#50)** — all
  second-order / `L²`-energy / bulk-spectral objects; Welch bound = `√n` average = the floor; the
  worst-case spike at 2-power-structured primes (Fermat `n=64` → `5.45√n`) is exactly what they are blind to.

### The real answer to "why is it everywhere, and why is it never solved"

Not log-correlation. The honest synthesis the grind forces:

1. **Why everywhere:** the quantity is the **`L^∞` (sup-norm / spectral edge) of a deterministic
   *equidistributing* exponential sum.** Every domain with a multiplicative-subgroup / character-sum /
   Frobenius-trace structure manufactures the *same* sup-norm object (Paley `λ₂`, the house, the coherence,
   the PAPR, the edge eigenvalue, …). They are not analogies — they are literally equal.
2. **Why never solved:** every domain's *native tool is second-order* (energy, `L²`, moments, spectral bulk,
   free cumulants, Welch, RIP), and the in-tree **meta-theorem proves no second-order method reaches `L^∞`
   below the `√p`/Johnson floor.** Reaching `L^∞` needs `log`-many moments — and those moments **break in
   char-`p` exactly at 2-power-structured primes** (the cumulant explosion). The obstruction is a discrete
   *arithmetic* fact about specific bad primes, not a soft analytic one — which is why no probabilistic
   shortcut (BRW/GMC/FHK) exists: **the field is too independent to have exploitable structure, yet the
   worst-case prime still spikes.**

That sharpening — *generically i.i.d.-Gumbel (floor holds), worst-case governed by structured-prime
independence-breakdown* — is the genuine, honest residue of this round. The prize core is unchanged and open,
but it is now correctly *de-mystified*: stop looking for a hidden universal field; the universality is the
`L^∞`-of-equidistribution + second-order-no-go, and the open part is purely the char-`p` structured-prime tail.
