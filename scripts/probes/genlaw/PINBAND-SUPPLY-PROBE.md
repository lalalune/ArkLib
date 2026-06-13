# Does the EsymmFiber coset supply reach the census pin band? — a verified probe (FFT: no; thick smooth: yes)

2026-06-13. Independent exact-arithmetic check (this probe), done because the workflow that
raised the question had its adversarial-verify leg die on a session limit AND its two
research legs disagreed (one claimed "uniformly poly, no dichotomy", the other "sharp
dichotomy, production on the poly side by an off-by-one"). Neither was verified; this probe
adjudicates. **It does NOT pin δ* or prove CensusDomination — it decides one named
obstruction.**

## Setup (exact, from the proven theorems)

- `CensusDominationWeld.lean`: pin needs `CensusDomination dom ((r−2)m+1) (rm+1) K`, i.e.
  RS dimension `k_c = (r−2)m+1`, pin floor `a₀ = rm+1`, domain `n = 2^μ·m`, all bands `a ≥ a₀`.
- `EsymmFiber.lean smooth_dyadic_supply_lower_bound`: at band `a`, a union of `μ_d`-cosets
  (needs `d | a`, `d | n`) with `d ≥ a − k_c + 1` (= `m_E+2`) gives `C(n/d, a/d)` explainable
  cores. So the construction's reach at the pin band = `max over {a ≥ a₀, d | gcd(a,n),
  d ≥ a−k_c+1} of C(n/d, a/d)`.

## Verdict (exact scan, production rates ρ ∈ {1/2,1/4,1/8,1/16}, μ = 10..16)

**The reach is governed by `m`, NOT by a "dyadic rate r=2^t" (the workflow's framing was a
mis-parametrization; with `k_c = (r−2)m+1`, r ≈ ρ·2^μ is large, not a small 2-power):**

- **m = 1 (the FFT / FRI production domains, n = 2^μ): POLYNOMIAL.** No `(a,d)` fires. The
  divisor floor `a − k_c + 1` always lands exactly one above the largest power-of-2 dividing
  `a` — the off-by-one the workflow's second leg correctly identified. Verified at every
  (ρ, μ) row: max log₂(supply) ∈ {0, 1, 2, 3} (= a single coset tip, ≤ 1/ρ). The
  multiplicative-coset construction does **not** reach the pin band on pure-2-power domains.
- **m ≥ 2 (thicker smooth domains, n = 2^μ·m): EXPONENTIAL.** E.g. ρ=½, n=2048 (μ=10,m=2):
  band a=1032 = 8·129 has d=8 ≥ floor 8, giving `C(256,129) ≈ 2^251`. Every m≥2 row fires
  at rate 0.02–0.13. The construction **does** refute CensusDomination here.

So: **the first leg's "uniformly poly" is WRONG (m≥2 is exp); the second leg's
"production on the poly side" is RIGHT but only because the FFT production case is m=1** —
and the operative variable is m, not the rate's 2-adic structure.

## What this means for δ* (honest scope)

- **Positive, narrow:** on the prize's actual FFT domains (m=1), the EsymmFiber
  multiplicative-coset construction is removed as a pin-band obstruction. One of the ways
  CensusDomination could have been false at production is now closed.
- **NOT proven:** CensusDomination itself (the supply could still be super-polynomial via a
  **non-coset** construction — the open "H-MAX" obligation), and therefore δ* is **not**
  pinned. This probe clears a single construction, nothing more.
- **A constraint on any pin claim:** any δ* pin via this census route must restrict to
  m=1 (pure 2-power domains); for n = 2^μ·m with m ≥ 2 the coset construction already
  refutes CensusDomination, so the route is dead there.

Reproduce: the scan is `pinband_probe.py` in this directory (exact integer `comb`, no
sampling). Coordination: the live pin-band lane is claimed by another NubsCarson seat on
#389 (comment 2026-06-13T02:49); this probe is recorded here, in the genlaw census lane,
not posted over that claim.
