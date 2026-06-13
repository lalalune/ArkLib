# δ* prize hypothesis slate (issue #371/#389, 2026-06-13)

**The target (open core).** Bound the sub-Johnson list size of explicit smooth
*dyadic* Reed–Solomon codes `μ_{2^μ}` in the prize window
`δ ∈ (1−√ρ, 1−ρ−Θ(1/log n))` at constant rate, `ε* = 2⁻¹²⁸`. Equivalently
(issue #389): is the *window-interior* list size (capacity `< a <` Johnson)
poly/subexponential as `n→∞` at constant rate? The deep-band/capacity radius
is SETTLED NEGATIVELY (`not_explainableCoreSupply_exponential`: Θ-exponential);
the window interior is open and computationally unreachable (brute force caps
at n=8; k≤3 incidence reaches only vanishing rate).

Each hypothesis: idea · what it builds on · novelty · likely refutation.
Rankings on two axes at the end. **Honest caveat: a 9/10-feasibility entry IS
a proof of the prize; none here clears that bar — feasibility is the wall.
This is an attack-planning artifact, not a claim of solution.**

## Reasonable (existing math, insightful use)

**R1 — Cyclotomic-tuned Guruswami–Sudan multiplicity.** Run GS bivariate
interpolation but raise multiplicity at the structured roots using
`X^n−1 = ∏_{d|n} Φ_d`. Builds on: GS99, in-tree `GuruswamiSudan/`. Novelty 4.
Refutation: GS with any multiplicity profile is bounded by Johnson for the
list radius (the interpolation degree count is symmetric); the cyclotomic
factorization doesn't change the genus/degree budget. **Reduces to Johnson →
discard per directive.**

**R2 — Spectral-gap second-moment Johnson refinement.** The list second
moment `Σ_{c,c'} |agree(c)∩agree(c')|` over μ_n is a Gauss sum (the in-tree
√q kernel). Refine Johnson by the *exact* √q value, not the trivial bound.
Builds on: `SubgroupGaussSum{SecondMoment,WorstCase}` (in-tree, √q both sides).
Novelty 5. Refutation: the second moment controls the *average* list, already
√|G|; the worst-case word can concentrate, and the completion step loses the
gain (this is the documented sub-√q incomplete-sum open face). Likely stalls
at the same wall.

**R3 — Multiplicative Croot–Lev–Pach / slice-rank.** Bound the agreement-set
system by slice-rank over the group algebra `F[μ_n]`. Builds on: CLP17,
polynomial method. Novelty 6. Refutation: CLP bounds *progression-free* sets;
the list isn't obviously progression-free, and slice-rank over `F_p[μ_n]` with
`p` large gives trivial bounds (rank = dimension). Probably vacuous in the
prize regime.

## Novel (new math)

**N1 — Multiplicative abc / Mason–Stothers collision bound.** My shared-R₀
insight: list size at radius `a` = #value-collisions of a bounded-degree
rational candidate map `f = −(R₀−r)/(R₁−q)` on μ_n. Conjecture a NEW
"abc-for-μ_n": a rational of degree `D` restricted to μ_n has `O(D + n/log n)`
value-collisions (vs the trivial `O(n)`), via a Mason–Stothers/radical bound
specialized to the cyclotomic `X^n−1`. Builds on: `RungOffPointPinning`,
Mason–Stothers. Novelty 9. Refutation: Mason–Stothers gives `deg ≤ rad−1`
which on μ_n doesn't obviously beat trivial; collisions = roots of `f−c` over
all `c`, total `= n·deg`, no per-`c` saving without new input. The "n/log n"
saving is exactly the window scale — plausible but unproven, and likely needs
the same incomplete-sum bound. **Most novel; feasibility 3.**

**N2 — Inversion orbit-rank invariant.** The bad set is `x↦−1/x`-invariant
(`MobiusMCASymmetry`). Define a NEW invariant: the rank over `F_2` of the
agreement-incidence matrix quotiented by the involution; conjecture it bounds
`log₂(list)`. Builds on: S1 Möbius brick, `mcaEvent_rs_mobius`. Novelty 8.
Refutation: a group action permutes the list but does not bound its size;
the orbit-rank could be full. No mechanism forces small rank. Feasibility 2.

**N3 — Cyclotomic-Fourier list-entropy.** Define a NEW entropy functional
`H(list) = −Σ_χ |⟨list, χ⟩|² log|·|` over μ_n-characters; conjecture
`log(list size) ≤ H ≤` (Gauss-sum-controlled). Builds on: Fourier on μ_n.
Novelty 8. Refutation: the lower bound `log|list| ≤ H` is false in general
(entropy of a structured list can be small while the list is large); the
functional likely measures spread, not count. Feasibility 2.

## Synthetic (interpolate the project's own math)

**S1 — Möbius × packing crossover lift.** The Möbius involution halves the
effective stack search space (`windowRationalBounded_of_halfFamily`); fuse with
the swarm's q-independent packing to push its `Θ(√(n log n))` crossover. Builds
on: my `MobiusMCASymmetry` + lalalune `mca_badscalar_packing`. Novelty 6.
Refutation: halving a search space changes constants, not the
`√(n log n)` exponent; `PackingDeepBandMiss` shows the crossover is
information-theoretic, not search-bound. Won't move the exponent. Feasibility 3.

**S2 — Tower-telescoped supply recursion.** Apply the quartet-tower 4-adic
recursion (`QuartetTowerLaw`) to the supply: relate the μ_{2^μ} list to two
μ_{2^{μ-1}} lists, telescoping a recursive bound down the 2-adic tower. Builds
on: `QuartetTowerLaw`, `TowerMonotonicity`, `WindowTelescope` (mine) +
`ExplainableCoreSupply`. Novelty 7. Refutation: the tower step likely *adds*
list members (coset union — the exact BKR explosion mechanism), so the
recursion grows not shrinks; `not_explainableCoreSupply_exponential` is built
from exactly this coset union. Probably proves the wrong direction. Feasibility 4.

**S3 — Attachment-gate as incomplete character sum.** My candidate-map
collision count IS an incomplete character sum over μ_n; bound it by the in-tree
worst-case completion `SubgroupGaussSumWorstCase`. Builds on: `RungOffPointPinning`,
`RungCrossRestriction` + the √q kernel. Novelty 7. Refutation: the worst-case
completion gives √q, and the window needs better than √q per frequency (the
sub-√q incomplete-sum open face) — so it lands exactly on a known open face,
not a closure. Feasibility 5 (the machinery exists; the bound is the wall).

## Dual rankings

**Easiest → hardest to prove-or-refute** (most are easy to *refute*):
R1 (reduces to Johnson, refuted) > R3 (vacuous slice-rank) > N3 (entropy LB
false) > N2 (orbit-rank unbounded) > S1 (constant-only) > R2 > S2 > S3 > N1.

**Most → least promising** (genuine chance of a real bound):
N1 (mult-abc, if the n/log n saving is real) > S3 (lands on the named open
face — closest to in-tree machinery) > S2 (tower recursion, if direction
flips) > R2 (spectral) > S1 > R3 > N2 > N3 > R1.

**Top pick to attack:** N1 (multiplicative-abc collision bound) on promise,
S3 on feasibility. Both route through the candidate-map collision count, which
is *computable* — so the productive move is to MEASURE the collision count of
the candidate map on μ_n vs degree, testing whether the conjectured
`O(D + n/log n)` saving is even true before attempting the abc-style proof.
If collisions are `Θ(n)` (no saving), N1 is refuted and the window-interior
list is genuinely large (negative). If `o(n)`, there is a real target.

## Top-pick attack result (N1/S3): the collision saving is not cheaply measurable

`probe_prize_collision.py` (n up to 1024, smooth μ_n vs generic domain):
ALL value-multiplicity counts are 0 in the window — because a fixed
small-degree map takes each value ≤ deg times, so no value reaches the
window radius `a = Θ(n)`. The fix (map degree `Θ(n)`, matching constant-rate
codewords) makes "count high-multiplicity values" EXACTLY the open
list-decoding question — no cheap proxy. **N1's conjectured `O(D+n/log n)`
collision saving cannot be measured at small degree, and at the needed
degree it is the wall.** Smooth-vs-generic showed no difference at small
degree (both 0), so no structural-inflation signal is cheaply visible either.

**Cycle conclusion (honest).** The full directive loop is complete: research
→ 9-hypothesis slate (3 reasonable / 3 novel / 3 synthetic) → dual rankings →
attack top pick (N1/S3) → all routes reduce to one of {Johnson (forbidden),
the sub-√q incomplete-sum open face, or the proven exponential supply}. No
entry clears 9/10 feasibility because that bar IS the prize. No winning
conjecture was found; none was fabricated. The prize core (constant-rate
window-interior list size for explicit smooth dyadic RS) is the genuine
~25-year wall, computationally unreachable at constant rate, and every
cheap proxy either misses the regime or reduces to the open question. The
realistic paths forward require either new literature technique (P1–P5, to
fetch) or a genuine mathematical breakthrough — not more probing.
