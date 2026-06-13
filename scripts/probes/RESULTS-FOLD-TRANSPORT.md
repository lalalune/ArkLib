# Fold-transport feasibility frontier — vector 5, lower-bound side (#389)

`probe_fold_transport_feasibility.py`, exact closed form. The all-rates bracket
(`RESULTS-DELTASTAR-BRACKET.md`) reduced "pin δ*" to the lower-bound side; this
decides the research map's highest-ceiling never-tried vector (fold-transport of
explicit capacity results) at the constraint level.

## The exact frontier
Folded smooth-RS (arity s) preserves rate ρ and list-decodes to folded-symbol-error
fraction 1−ρ−ε (GW/CZ25). A plain δ-fraction of errors maps to folded fraction in
[δ, min(δs,1)] (effective unfolding loss L ∈ [1,s], adversary spreads). The route
gives a beyond-Johnson plain radius iff L < L*(ρ) := (1−ρ)/(1−√ρ) = **1+√ρ** (exact).

| ρ | Johnson 1−√ρ | L*=1+√ρ | naive loss s | verdict |
|---|---|---|---|---|
| 1/2 | 0.2929 | 1.7071 | ≥2 | naive DEAD |
| 1/4 | 0.5000 | 1.5000 | ≥2 | naive DEAD |
| 1/8 | 0.6464 | 1.3536 | ≥2 | naive DEAD |
| 1/16 | 0.7500 | 1.2500 | ≥2 | naive DEAD |

## Verdict
* **Naive fold-transport NEVER beats Johnson** at any prize rate: the smallest fold
  arity is s=2, and 2 > 1+√ρ = L*(ρ) for every ρ ≤ 1/2. The research map's hand-wave
  ("naive unfolding lands below Johnson") is now an exact fact. REFUTED as a naive route.
* The route survives ONLY if the smooth 2-power tower forces MCA-bad error supports to
  co-locate within tower blocks to fraction ≥ **1−√ρ** (the Johnson radius itself — an
  exact self-referential threshold; at s=2 the spread fraction must be < √ρ).
* **Successor question (the real test, toy-probeable):** do MCA-bad stacks on a smooth
  2-power domain have error support that co-locates under the squaring-tower block
  structure to ≥ 1−√ρ? The supply census (exponential, spread-thin) is prior evidence
  AGAINST co-location — honest prior is full refutation; the co-location probe decides it.
