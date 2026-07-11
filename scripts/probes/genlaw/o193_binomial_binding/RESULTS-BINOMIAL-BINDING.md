# The binomial-binding question, resolved at the computable frontier: MONOMIAL governs the binding rung (n=8,16)

2026-06-16. Answers lalalune's explicit open question from the #444 fresh-angle round
(comment 4716... 08:09Z): "is the *binding* (budget-crossing) rung's worst direction monomial
or binomial? If binomial, the m* analysis (and {3,3,5}) is on a proxy." Engine: the in-tree
`scripts/rust-pg/src/bin/monobino.rs` (lalalune's own monomial-vs-binomial incidence engine,
the one that produced binoMax=448). Exact arithmetic, faithful primes, `budget = n`.

## Verdict: MONOMIAL GOVERNS the binding rung; the binomial advantage is confined to
## above-budget explosion rungs and does NOT change m* (n=8 and n=16, 3 primes).

**n=16, k=4 (ρ=1/4), budget=16** — identical across p ∈ {65537, 1048609, 16777441}:

| s (=k+m) | m | monoMax | binoMax | both ≤ budget? |
|---|---|---|---|---|
| 6 | 2 | **89**  | **448** | NO  (explosion edge — both ≫ 16) |
| 7 | 3 | **9**   | **8**   | YES (binding rung — mono ≥ bino) |
| 8 | 4 | 9 | 8 | yes |
| 9 | 5 | 9 | 9 | yes |
| 10| 6 | 8 | 6 | yes |
| 11| 7 | 0 | 2 | yes |

- m=2 (s=6): BOTH mono (89) and bino (448) exceed budget ⟹ m=2 fails for EITHER direction class.
- m=3 (s=7): BOTH drop ≤ budget, and mono (9) ≥ bino (8) ⟹ m=3 passes; the worst direction is monomial.
- ⟹ **m*(16) = 3 whether or not binomials are included.** The binomial's 5× advantage (448 vs 89)
  lives only at the over-determined explosion rung s=6, which is above budget regardless.

**n=8, k=2 (ρ=1/4), budget=8** (regime control — lalalune: "at n=8 the monomial IS worst"):

| s (=k+m) | m | monoMax | binoMax |
|---|---|---|---|
| 3 | 1 | 40 | 56 (explosion edge, both ≫ 8) |
| 4 | 2 | **9** | **8** (mono > budget, bino = budget) |
| 5 | 3 | 5 | 3 (both ≤ 8) |
| 6 | 4 | 0 | 2 |

- At the binding-determining rung s=4, the **monomial** (9 > 8) is the constraint that keeps m=2
  from passing (the binomial alone, 8, would pass). m*(8) = 3, monomial-governed. Confirms
  lalalune's "monomial is worst at n=8."

## What this means (honest scope)

- **Resolves the binomial-binding question favorably:** the monomial cascade is NOT a proxy at the
  binding rung. {m*(8)=3, m*(16)=3} are correctly computed on the monomial locus; binomials do not
  push m* up because their advantage is confined to rungs already above budget. This validates the
  demand-side r=3/4/5 monomial bricks (DeepBandR{3,4,5}Bound) as the genuine binding object at n≤16.
- **Does NOT contradict lalalune's binoMax=448** — it contextualizes it: the binomial explosion is
  real but lives one rung below binding (above budget regardless), exactly per their own caveat.
- **Does NOT resolve the prize.** m* is the over-determined Johnson/Plotkin PROXY face (per O192);
  the real prize is the p-dependent BGK sup-norm wall (BCHKS 1.12), untouched. This removes one
  specific doubt (is m* itself on a monomial proxy — no, at the binding rung), nothing more.
- **n ≥ 32 is uncomputed** (the over-det edge `C(32,s)·#dirs·#bases` is the CPU-cap lalalune hit);
  the "monomial governs the binding rung" conjecture is verified at the computable frontier n ≤ 16.

Reproduce: `cd scripts/rust-pg && cargo build --release --bin monobino && \
  for s in 6 7 8 9 10 11; do ./target/release/monobino 16 4 $s; done` (3 primes via mult=4,5,6).
