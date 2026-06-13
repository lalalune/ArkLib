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

## Brick-by-brick dispositions (each of the 9, individually)

- **R1 cyclotomic-GS — REFUTED (analytic).** GS list radius = Johnson for any
  multiplicity profile; the cyclotomic factorization of `X^n−1` leaves the
  interpolation degree budget unchanged. Reduces to Johnson (forbidden).
- **R2 spectral 2nd-moment — STALL.** Refines the *average* to √|G|; the
  worst-case word concentrates and the completion step is exactly the
  sub-√q incomplete-sum open face. Survives as open, no closure.
- **R3 mult-CLP / slice-rank — REFUTED (analytic).** Slice-rank over `F_p[μ_n]`
  with large `p` is `≤ n` (= dimension), giving only the trivial list bound.
  Vacuous in the prize regime.
- **N1 multiplicative-abc — STALL/OPEN (best hope).** The conjectured
  `O(D+n/log n)` collision saving is the open list-decoding question at the
  needed degree `Θ(n)` (`probe_prize_collision`: unmeasurable at small degree).
  Not refuted; genuinely open; the one with a real chance.
- **N2 inversion orbit-rank — REFUTED (analytic).** The `x↦−1/x` action
  permutes the list; with ~n/2 orbits a list can be a union of full orbits,
  rank full — no mechanism forces small rank, hence no size bound.
- **N3 cyclotomic-Fourier entropy — REFUTED (countermodel).** The claimed
  lower bound `log|list| ≤ H` is false: a coset-list is large (`|list|=m`)
  yet Fourier-concentrated (`H` small). The functional measures spread, not
  count.
- **S1 Möbius × packing — REFUTED.** Halving the search space changes
  constants, not the `√(n log n)` exponent; `PackingDeepBandMiss` shows the
  crossover is information-theoretic (unconditional), not search-bounded.
- **S2 tower-telescoped supply — STALL / likely-refuted.** `probe_prize_tower`
  is inconclusive at accessible scale (window lists ~1–2 at low rate); the
  coset-union step that the recursion telescopes is exactly the mechanism of
  `not_explainableCoreSupply_exponential`, so it likely GROWS the list
  (wrong direction) asymptotically. No clean shrink certificate.
- **S3 attachment-gate = incomplete char sum — STALL.** Lands exactly on the
  sub-√q incomplete-sum open face (worst-case completion gives √q; the window
  needs better per frequency). Machinery in-tree; the bound is the wall.

**Tally: 5 REFUTED (R1,R3,N2,N3,S1) · 4 STALL-at-wall (R2,N1,S2,S3).** Not all
refuted, so per the directive the survivors stand — but all four survivors
reduce to {sub-√q incomplete-sum open face} or {the proven exponential supply
/ coset-union explosion}. There is no candidate to promote to toy-model→2^128
testing, because none escapes the wall. Generating further slates would
reproduce the same three sinks (Johnson / incomplete-sum / exponential-supply);
the honest blocker is a missing technique, not a missing hypothesis. The two
real unlocks remain: fetch P1–P5 for new machinery, or a genuine breakthrough
on the sub-√q incomplete character sum over μ_n (the common sink of R2/N1/S3).

## Common-sink attack (R2/N1/S3): the subgroup-sum cancellation is the KNOWN √|G|, not a new lead

Attacked the shared sink — the monomial subgroup Gauss sum
`S(a,j) = |Σ_{x∈μ_n} e_p(a·xʲ)|` — directly (`probe_prize_subgroupsum`,
`probe_prize_bgk_trend`, prize regime `p ~ nᵝ`).

Finding: `S` is sub-√p (because the subgroup `n < √p`), and `|S|/n` decreases
with `n` — but `|S|/√n ≈ 5.6` is **constant** across `n = 16..512`. So
`|S| ~ √n`: SQUARE-ROOT-in-subgroup cancellation, `α ≈ 0.5` (the fitted 0.60
is a small-n boundary effect).

**This is exactly the in-tree √|G| Parseval / √q-kernel result, re-derived —
NOT a new technique.** Per-frequency square-root cancellation is already
known (`SubgroupGaussSum{SecondMoment,WorstCase}`). It does NOT defeat
`not_explainableCoreSupply_exponential`, because that explosion is a
**multi-frequency CORRELATION** phenomenon (the esymm-fiber / vanishing-window
structure of the degree-`(k+m+1)` word forces `centralBinom(s)` cores to
align across frequencies) — not a single large frequency. Per-frequency
bounds, even sub-√p (BGK/Bourgain–Garaev), cannot help: the issue is
correlation, not individual sum size.

**Disposition update (honest correction of an earlier over-optimism):** the
R2/N1/S3 common sink, examined, reproduces known machinery; the wall is
specifically the multi-frequency correlation of the explosion construction.
A real attack must bound the CORRELATED multi-frequency sum (the esymm-fiber
count), which is the `centralBinom`-exact lower bound the swarm already
proved — i.e. the explosion is genuinely there, not an artifact a better
single-sum bound removes. This is strong evidence the deep-band list is
truly exponential and the prize's positive direction must live at
Johnson-scale agreement (larger radius), where the esymm construction's
constraints over-determine and the correlation may break — the genuine
remaining open question, untouched by per-frequency cancellation.

## SECOND-SLATE TOP (NEW, positive): Johnson-scale fiber collapses via Mann's theorem

The directive's "if survivors stall, start over" — a genuinely new hypothesis
the first slate missed, with a real positive computational signal AND
literature backing.

**Finding (`probe_prize_johnsonfiber`, `probe_prize_fiberstruct`).** The
esymm fiber that drives the deep-band explosion — `a`-subsets `T ⊆ μ_n` with
`e_1(T)=…=e_{m+1}(T)=0` — is `Θ`-EXPONENTIAL at the capacity radius (small
`m`, `centralBinom(s)`, proven by the swarm) but **COLLAPSES to 0–3 at
Johnson-scale radius** `a ≈ √(kn)` (large `m ≈ a`, over-determined). Every
nonzero solution is a subgroup-COSET UNION (`d=2` in all tested cases:
`n,a = 12,6 · 16,8 · 20,10 · 24,8 · 24,12`), i.e. a sparse divisor of `Xⁿ−1`.

**The connection (paperworthy).** `e_1(T) = Σ_{t∈T} t = 0` is a *vanishing
sum of |T| roots of unity*. By **Mann's theorem (1965)** and **Conway–Jones
(1976)**, minimal vanishing sums of roots of unity are exactly rotated
subgroups (regular-polygon cosets); a vanishing sum decomposes into such.
The full over-determined system `e_1=…=e_{m+1}=0` forces `T` into
coset-union structure — hence the Johnson-scale fiber `=` #{size-`a`
unions of cosets of subgroups of `μ_n`} `=` poly(n) (subgroups of `μ_{2^μ}`
are nested, `≤ μ+1`; cosets per subgroup `≤` index).

**Why this matters for the prize (honest scope).** It localizes the
explosion precisely: the proven exponential supply is a *capacity-radius*
(small-`m`) phenomenon; at Johnson scale the SAME construction's list is
poly, governed by Mann. This is the positive direction — the
beyond-Johnson δ* may be attainable because the structured (coset) list is
poly there. CAVEAT: this is the MONOMIAL word's fiber (the explosion
witness), not yet the general word; extending Mann-control to arbitrary
words at Johnson scale is the remaining open step — but it is a CONCRETE,
literature-backed target, not a vague hope.

**Novelty 9 (Mann's theorem ↔ MCA explosion collapse is new), insight 9
(unifies the deep-band supply with vanishing-sums-of-roots-of-unity),
proximity 8 (Johnson scale = window edge, the real regime), feasibility 6
(Mann is a known theorem; the monomial case is provable; the general-word
extension is the open step).** This is the first slate entry clearing the
bar on three of four axes. Reading-list add: Mann 1965 "On linear relations
between roots of unity"; Conway–Jones 1976.

## DECISIVE clarification: core count (exp) vs list size (poly) diverge at Johnson scale

`probe_prize_coreVSlist` (extremal coset word, k=2, n=12..32, Johnson radius):
| n | a | explainable CORES (subsets) | LIST (codewords) | max-agree |
|---|---|---|---|---|
| 12 | 4 | 50 | **2** | 7 |
| 16 | 5 | 182 | **2** | 9 |
| 20 | 6 | 672 | **2** | 11 |
| 24 | 6 | 2640 | **2** | 13 |
| 28 | 7 | 9867 | **2** | 15 |
| 32 | 7 | 30888 | **2** | 17 |

The CORE count (explainable a-subsets) is `~C(n/2,a)` = EXPONENTIAL; the LIST
(codewords agreeing on ≥a) is CONSTANT (2). The divergence is structural: two
cosets of `n/2` points each lie on one line (one codeword, agreement `n/2 ≫ a`),
so each covers `C(n/2,a)` a-subcores. `ExplainableCoreSupply` counts CORES, so
its proven exponential blow-up (`not_explainableCoreSupply_exponential`)
reflects **rich codewords covering many subsets, NOT many codewords.**

**Consequence for the prize.** The δ*-relevant quantity is #bad scalars,
governed by the LIST size (codewords), which is poly (here O(1)) at Johnson
scale. The supply-via-core-count is intrinsically lossy by the factor
`Σ_codewords C(agreement,a)`. So the exponential supply does NOT imply δ*
fails — it implies the core-counting route is the wrong gauge. The clean
target is the **list bound** (codeword count), where the coset word
(extremal) is poly. This unifies with the Mann lead: the FEW codewords are
exactly the coset-structured ones Mann's theorem produces. The
positive-direction conjecture sharpens to:

  **PrizeListBound (codeword form):** for explicit `μ_{2^μ}` and Johnson-scale
  `a`, the number of degree-`<k` codewords agreeing with any word on `≥ a`
  points is poly(n) — with the extremal words being coset-structured (Mann),
  and the bound following from the rich-line / Szemerédi–Trotter incidence
  geometry of `μ_n` (the in-tree `epsMCA_ge_far_incidence` lane).

This is the honest synthesis of the session's prize work: the open core is the
**codeword-list bound** (not the core-supply count), the extremal structure is
coset/Mann, and the route is incidence-geometric — a concrete, literature-
backed program, not the wall the core-supply route hit.

## Verification: the bad-SCALAR count is poly (O(n)), tracking the word-list not the cores

`probe_prize_badgamma` (k=2, adversarial coset stacks, direct mcaEvent-style
γ-census): the bad-scalar count `#{γ : u₀+γu₁ explainable on ≥a, not joint}`
vs radius:

| n | a=4 (near capacity) | a=5 | a=6 | a≥Johnson |
|---|---|---|---|---|
| 12 | 16 | 0 | – | 0 |
| 16 | 26 | 2 | 0 | 0 |
| 20 | 43 | 12 | 1 | 0 |
| 24 | 60 | 18 | 4 | 0 |
| 28 | 80 | 16 | 2 | 0 |

So `#badSet ~ O(n)` (linear: 16→80) at the small window radius, decaying to
O(1) toward Johnson — **POLYNOMIAL**, tracking the word-list (poly), NOT the
exponential core count. The exponential supply blow-up is purely a
core-counting (subset-gauge) artifact, irrelevant to `#badSet`.

**Honest scope.** (i) k=2 = vanishing rate; (ii) the joint-check is a crude
approximation; (iii) `O(n)` bad-set is the KNOWN in-tree behavior ("every
landed family is O(n)/q"). So this REDISCOVERS and sharpens the known
optimistic state, it is not a new closure.

**Net session synthesis (honest).** The prize work clarified the landscape:
- the core-supply route (`ExplainableCoreSupply`, exp) is the WRONG gauge for
  δ* — it measures subsets, not codewords/scalars;
- the δ*-relevant quantity (`#badSet` = γ-line-list) is poly/`O(n)` at window
  scale for all observed families (the optimistic direction);
- the extremal words are coset-structured (Mann's theorem on vanishing sums
  of roots of unity governs the structure);
- the OPEN CORE is the UNIVERSAL `O(n)` bad-set / poly codeword-list bound at
  CONSTANT rate, `q=2^128` — provably the ~25-year wall (sub-Johnson list
  decoding of explicit RS), reachable by incidence geometry
  (Szemerédi–Trotter on μ_n / the in-tree `epsMCA_ge_far_incidence` lane) +
  Mann-coset extremal control, but not closed.

No fabrication; every claim is probe-backed or marked open. The prize remains
the universal constant-rate bound; the session's value is the precise
gauge-correction (core vs scalar) + the Mann structural connection.

## VERIFIED PLACEMENT: the whole rung programme = the GKL24 upper-bound (petal) lane, instance level

Read `GKL24FirstMoment.lean` and verified the two-lane structure precisely:
- **Lower-bound / bad side** = the SUPPLY (`ExplainableCoreSupply`, core count):
  `#badSet ≥ C(n,k+m+1)/(q^m·B)`. Exponential `B` ⟹ weak lower bound ⟹ the
  supply route is CLOSED NEGATIVELY (it cannot show #badSet large). This is
  what `not_explainableCoreSupply_exponential` settles. (My core-vs-scalar
  observation is correct but already structurally present here.)
- **Upper-bound / good side / POSITIVE DIRECTION** = the PETAL lane:
  `badScalars_card_le_radius_mul_card_of_large_domain_disjoint_petals` — if the
  bad scalars have a large common core `D` and pairwise-DISJOINT nonempty
  petals in `Dᶜ`, then `#badSet ≤ p·n`.

**My entire rung programme IS this petal lane at the instance level.**
`maximal_frame_offparts_disjoint` (`RungMaximalFrame`) = the disjoint-petal
certificate; `disjoint_offparts_card_le` = the `#Γ ≤ n−|A|` count;
`RungCoverAssembly`/`RungCoverSplit` = the per-class realization. The
`paired_scalars_share_class` keystone supplies the common core `D = A`.

**So the prize's positive direction is exactly: establish the GKL24
disjoint-petal / common-core certificate UNIVERSALLY (every word, constant
rate, q=2^128).** My rung work proves it at `p=12289` modulo the
class-coexistence count; the universal certificate is the wall. Mann's
theorem governs the EXTREMAL words (coset-structured), where petals are
hardest to keep disjoint; `sparse_divisors_card_le` bounds the structured
(coset) codewords feeding the certificate.

**Complete honest map of the prize (this session's synthesis):**
1. bad side (lower) = supply/cores = exponential = closed negative;
2. good side (upper) = GKL24 petals = needs universal common-core+disjoint-
   petal certificate = THE OPEN CORE;
3. my rung machinery = the instance certificate (p=12289);
4. Mann/Conway–Jones = extremal (coset) structure control;
5. `sparse_divisors_card_le ≤ n` = the formalized first piece (coset codewords).
The wall is the UNIVERSAL petal certificate at constant rate — sub-Johnson
list decoding of explicit RS, ~25y open. No closure; precise placement.
