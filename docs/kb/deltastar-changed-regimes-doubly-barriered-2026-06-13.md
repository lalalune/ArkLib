# The prize is DOUBLY-barriered: every "changed regime" relaxation is provably load-bearing (#407)

**Status: decisive regime map.** A 6-agent survey of each "change the problem" regime where δ* is
PROVEN, looking for an open path back toward the plain-RS prize that avoids BCHKS Conjecture 1.12.
Result: the prize is blocked by TWO INDEPENDENT proven barriers, and every relaxation that makes the
changed regime provable is itself provably NECESSARY. 2026-06-13.

## The two independent walls
The plain-RS-over-μ_n prize sits at the intersection of two unrelated proven obstructions:
1. **Character-sum / worst-case-list route → BCHKS Conjecture 1.12** (= GK07/BGK sum-product wall).
   [`deltastar-floor-IS-BCHKS-conjecture-1-12`]
2. **Subspace-design / higher-order-MDS route → BCDZ25 Thm 1.11 Schubert-calculus barrier**: the
   subspace-design quality is `d(k−d)/(s−d+1)`, VACUOUS at `s=1` (plain RS). GGH26: "this property
   necessarily requires the code to be FOLDED." Plus the in-tree machine-checked negation-symmetry
   refutation (`MuTwoPowDerandRefutation.lean`: even μ_n SATURATES generalized-Singleton since `−1∈μ_n`).

These are INDEPENDENT (one is additive-NT subset-sum spreading, the other is Grassmannian codimension).

## The regime map (which relaxation is load-bearing, and why)
| Regime | δ* proven? | un-relax → prize | blocker |
|---|---|---|---|
| **Folded RS** (GG25/BCDZ25) | YES, BGK-free | drive folding `s→1` | re-hits BCHKS-1.12 AND Schubert; folding load-bearing |
| **Multiplicity codes** (GG25) | YES, BGK-free | drive mult `s→1` | dies EARLIER at design-dim collapse `τ(r)=1 ∀r≥2` (before BCHKS) |
| **Random RS** (BGM/GZ, large field) | YES, BGK-free | derandomize → explicit μ_n | negation symmetry refutes μ_n genericity (higher-order-MDS) |
| **Large-field RS** | counting only | reduce `q→n·2¹²⁸` | doesn't fix explicit-μ_n genericity; re-hits BCHKS |
| **Subspace-design** (JLR26/BCDZ25) | YES, BGK-free | transfer to RS | needs folding (Schubert barrier) |
| **CLOSEST: explicit folded RS** (BCDZ25 Thm 1.4) | YES, BGK-free, `q=Θ(sn)` | un-fold | **un-foldability is a THEOREM** (BCDZ25 Thm 1.11) |

**The closest proven, BGK-free, prize-adjacent result:** BCDZ25 (Brakensiek–Chen–Dhar–Zhang,
arXiv:2510.13777, Oct 2025) Thm 1.4 — explicit `s`-folded RS / multiplicity codes over `q=Θ(sn)`
(field size EASIER than the prize 2¹²⁸) inherit EVERY local property of random linear codes
(list-decoding / curve-decodability / OPTIMAL proximity gap to capacity `1−R−ε`), routing through
subspace-designs + GK16 explicit expanders + LMS25/GM-MDS — **never touching BCHKS-1.12/BGK**. The
ONLY relaxation vs the prize is the folding `s≥b(R/ε+1)`, and BCDZ25 Thm 1.11 proves that folding is
NECESSARY for the subspace-design property.

## The one un-refuted (but unresolved) opening: ODD-ORDER smooth domains
The even-order floor refutation is SPECIFICALLY the negation symmetry (`−1=ω^{n/2}∈μ_n`, forced for
`n=2^a`). ODD-order multiplicative subgroups (`n=3^a`, radix-3 NTT, `−1∉μ_n`) REMOVE it. Numerics
(`probe_oddorder_*.py`): even μ_n sits at the WORSE end of the random worst-case-list range; odd μ_n is
random-like — but at the small radii tested the random spread is too tight (lists 2–3) to cleanly show
odd-order is MORE generic (`< random`). So odd-order is the one route that escapes BOTH the negation
refutation and (via the GM-MDS/higher-order-MDS route, which Route 4 showed is BGK-free) the
character-sum wall — reducing the prize to "is odd-order μ_n higher-order MDS?", a DIFFERENT open
problem than BGK. CAVEAT: odd-order is a changed smoothness (radix-3, not the prize's 2-power NTT), and
the genericity is unproven. Worth a dedicated GM-MDS-minor (not list-size) test.

## Net (honest)
NO open path from any proven regime to the PLAIN-RS prize: every relaxation (folding, multiplicity,
randomness) is PROVABLY load-bearing (Schubert / design-dim-collapse / negation), independent of
BCHKS-1.12. The prize is doubly-walled. The closest proven result is explicit FOLDED RS (BCDZ25), gap =
the provably-necessary folding. If the internal team "solved MCA," they either (a) resolved
BCHKS-1.12/BGK, (b) used folding/multiplicity (changed the problem, where it IS proven, BCDZ25/GG25),
or (c) found a construction outside this map. The single un-refuted lead is odd-order smooth RS via
higher-order MDS.

New paper: **BCDZ25, arXiv:2510.13777** (Oct 2025) — "From Random to Explicit via Subspace Designs",
Thm 1.4 (explicit folded-RS inherits random-LC local properties) + Thm 1.11 (folding necessary).
