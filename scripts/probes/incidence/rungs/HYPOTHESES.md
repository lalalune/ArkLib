# The incidence laboratory at all rungs — pre-registered hypothesis batch 1

Lane: nubs incidence seat (claim: #334 comment 4675343864, 2026-06-10). Extends O129.
Method per the program discipline: each hypothesis is preceded by its constraints, the
new direction, why nobody has done it, the no-larping check, and what exactly is novel
— written BEFORE the computations run. Verdicts appended as lanes return.

## Grounded (known mathematics)

**G1 — the menu law.**
Constraints: the cross-pair dead locus is S∩B (O129 dichotomy); S ranges over a
pair-selection structure (O130 witness recipe); B over the marginal census.
Direction: derive the locus-multiplicity menu as pure counting over B's antipodal-pair
profile. Why not done: the pair-locus question only existed after O129; O130's menus
are element-level (B-census), not pair-level. No-larping check: searched DISPROOF_LOG
for incidence menus — none; O130 explicitly flags census closed-forms beyond m=16 as
fits, not derivations. Novel: first closed-form incidence statistic; if exact at s=16
it generalizes to all rungs by the same counting.
Falsifier: any of the 40 menu entries differing from the analytic count.

**G2 — exactness at rung 3 (n=64).**
Constraints: the exactness law is proven s=8/16 only, via a finite char-0 computation;
the certificate is configuration-specific. Direction: blind test at n=64 on
engine-constructed data. Why not done: the n=64 census is hours old. No-larping: O130's
constructive codewords were verified for agreement, never for pairwise incidence.
Novel: a third rung either extends the law (suggesting a uniform char-0 rigidity, cf.
A3) or breaks it (locating the law's finite range).
Falsifier: a witness–marginal pair at n=64 with |Z₀| > |T∩T′|.

**G3 — dichotomy generality.**
Constraints: the dead-fiber dichotomy proof (P/Q factorization, parity lock) uses only
deg bounds and e₃ ≠ 0 — looks rung-generic. Why not done: stated at s=16 only.
No-larping: the O129 lemmas are explicitly one-configuration. Novel: locus = S∩B at
every rung makes the incidence lattice rung-uniform — the input G1's general form needs.
Falsifier: an n=64 pair whose L1 locus ≠ S∩B.

**G4 — rank/Fisher cap (queued, needs G1–G3).**
Constraints: locus indicators live in F₂^(s/2); rank ≤ s/2 trivially. Direction: a
Plotkin/Fisher-style argument capping clique size by lattice rank — the first
incidence-driven LIST bound. No-larping: no list bound in the program uses pairwise
locus structure; classical Johnson/Elias bounds use distances only. Novel: distances
here are REFINED by where the agreements sit (the locus), not just how many.
Falsifier: configurations with equal-size lists but unboundedly different lattice ranks.

**G5 — beating the union bound.**
Constraints: V_{Z₁} ∩ V_{Z₂} = V_{Z₁∪Z₂} with exact dimensions (O96) — the
inclusion–exclusion is computable on the measured lattice. Why not done: O99 stopped at
the union bound by design ("the slack IS the open incidence content"). No-larping:
checked O99/O115/O118 — no I-E computation exists. Novel: the first sub-union-bound
count past Johnson on a smooth domain, even if only at one word.
Falsifier: the Bonferroni sandwich failing to separate from the union-bound sum.

## Advanced (new directions)

**A1 — incidence–moments duality.** The locus-multiplicity distribution should BE the
combinatorial core of the third agreement-spectrum moment (pair collisions ↔ triple
correlations of (u, c, c′)). Constraint: moments are word-averaged, my data is per-word.
Why not done: the two channels were opened by different seats this week. Novel: a
bridge identity would let moment bounds consume incidence data directly. Larp-check:
probe_coset_agreement_moments.py computes M2 only; no M3-incidence link anywhere.

**A2 — certificate class-field structure.** The 13,219 norms' prime divisors (the bad
primes) should be characterized Galois-theoretically (the differences live in ℤ[ζ₃₂];
their norms' splitting is governed by which auxiliary moduli divide). Why not done: the
certificate is one day old. Novel: would turn the 1/p empirical rate into a density
theorem (Chebotarev). Falsifier: bad-prime set failing any congruence/density pattern.

**A3 — rigidity at all words.** Char-0 exactness (zero accidental agreement between
distinct close codewords) holds for EVERY word and every pair of list elements, not
just the canonical configuration — "agreement rigidity is generic in char 0". If true,
char-0 list counting is EXACTLY lattice combinatorics, and char-p deviations are
finitely certified per configuration. Why not done: nobody asked; the classical
literature works in fixed char p. Larp-check: this is NOT the Schwartz–Zippel triviality
(that bounds zeros; this asserts zero EXCESS at honest configurations). Falsifier: a
char-0 word with an accidental collision (the q-root identities show dense-dense pairs
CAN collide — the refined claim is these are classified, not absent; sharpening needed
after G2).

**A4 — the lattice flag tower.** Depth-ℓ dead loci refine S∩B through the slice
anatomy (level-2 loci should be readable from the σ-typing). Novel: would make the
tower iteration of incidence combinatorial too. Queued behind G3.

**A5 — turn-on predictor.** The r-strata turn-on (r=5 at s=32, O130's finding) is
governed by an incidence-lattice threshold (atoms of the level lattice exceeding the
balance constraints). Blind-testable against O130's level-4 anchors (predict whether
r=7 activates at s=64). Queued behind G1's general form.

## Status
Batch-1 lanes (G1, G2+G3, G5) launched 2026-06-10 via workflow; verdicts to be
appended verbatim with artifacts.

## A2 — first observation (inline, 2026-06-10)
From `exactness/norms_result.json` summary data: all systematically swept bad primes are
≡ 1 mod 32 (split, as the theory requires). Over the sweep range (p = 97..1409), the
bad-orbit rate follows c/p with **c ≈ 11 ± 3 — significantly below the generic c = 16**
(a random degree-16 norm would be divisible by a split p at rate ≈ 16/p). The deficit
is the first quantitative evidence that the difference set carries Galois structure
(stabilizers/congruence obstructions) — A2's target is now: explain c ≈ 11. Caveat: the
dict's large-p tail is existence-conditioned (prime factors found), not a rate
measurement — excluded. Full A2 needs the per-delta factorizations (norms.py rerun).

## A1 — VERDICT (2026-06-10): bridge PROVEN + verified; hypothesis corrected in transit
Artifacts: `lane_a1_moments_bridge.py` / `.out` (all exact checks pass, n=16 C19).

**The pre-registered location of the pair content was wrong, and the correction is the
theorem.** Every factorial/power moment of the agreement spectrum a_j is a
single-codeword sum (Σ a_j j³ = Σ a_j [j + 3j(j−1) + j(j−1)(j−2)] — no pair term, ever).
The pair-overlap distribution enters the moments channel through the TRANSPOSED
spectrum: for t-subsets σ ⊆ D let M_t(σ) = #{p ∈ L : σ ⊆ T_p}. One double count gives,
for all r ≥ 1, t ≥ 0:

    Σ_σ C(M_t(σ), r) = Σ_{R ∈ C(L,r)} C(|∩_{p∈R} T_p|, t)        (BRIDGE)

r=1 recovers the a_j factorial moments (Σ_σ M_t = Σ_j a_j C(j,t)); **r=2 is the bridge:
the t-th binomial moment of the O129 pair-overlap distribution equals the second
binomial moment of the dual spectrum.** Power form (t=1, N(x) = point multiplicity):
Σ N² = F1 + 2·P2, Σ N³ = F1 + 6·P2 + 6·P3 (P2/P3 = pair/triple overlap mass) — the
"third moment with pair-overlap core" lives in the dual variable, and its genuinely new
content at order 3 is the TRIPLE-overlap mass. Centered form: n·Σ(N−F1/n)² =
Σ_{p,p'}(n|T∩T'| − |T||T'|) — centered dual-M2 = overlap excess over uniform baseline.

Verified exactly at the C19 configuration (a_9=16, a_10=3): all nine (t,r) ∈ {1,2,3}²
instances; F1=174, P2=922, P3=3240, ΣN²=2018, ΣN³=25146; dual census b⁽¹⁾ =
{9:8, 10:4, 14:2, 17:2} (two domain points carry 17 of the 19 list elements).
Exactness re-measured on ALL 171 pairs incl. the 3 witness–witness pairs (out of scope
of the n=32 theorem — NEW data): zero excess everywhere; W-W overlaps all 6; overlap
menus W-D {5:28, 6:20}, D-D {3:4, 4:16, 5:40, 6:52, 7:8}.

**What the moments channel now consumes (honest).** T_p ∩ T_p' ⊆ Z0(p−p') always; the
exactness law upgrades it to equality, so |T∩T'| = n − d_H(p,p') — the full pair-overlap
distribution, hence by (BRIDGE, r=2) every binomial moment of the dual spectrum's pair
content, is computable from the list's distance geometry alone, with zero per-word
slack, wherever exactness holds (proven: canonical s=8/16 configurations, char 0 +
certificate; G2 tests n=64). Concretely, Johnson-style double counts can replace the
worst-case cap c_max·C(L,2) (here 7·171 = 1197) by the measured/derived pair mass
(922, ratio 0.770) — a 23% tightening at C19. Limits: this feeds per-word,
per-configuration moment arguments; it does NOT touch the word-averaged closed forms
(probe_coset_agreement_moments.py M1/M2 — those decompose over the code-level distance
distribution and are already exact), and order-3 dual moments need triple overlaps,
which incidence has not yet measured beyond n=16.

## A2 — VERDICT: CONFIRMED (2026-06-11, lane complete)
**c ≈ 11 explained exactly: c = Σ_orbits 16/|Stab| / #orbits = 146622/13219 = 11.0918.**
The dominant mechanism: 7,796/13,219 orbits are σ₁₇-fixed — witness values always lie in
the index-2 subfield ℤ[ζ₁₆] (all their exponents are even), and differences inherit it.
Corrected rate law E[bad(q)] = Σ_d hist[d]·(1−(1−1/q)^d), hist = {16:5414, 8:7227,
4:516, 2:56, 1:6}: 30-prime sweep aggregate measured 5,940 vs expected 5,935.9
(z = +0.05); generic c=16 rejected (z = −28.7). Per-prime overdispersion ×10.2
(clustering — law is aggregate-exact). Beyond the sweep the law is an UPPER bound: the
deficit is forced (1−ζ)-adic content (v₂(norm) ≥ 20 always, mean 31.7) + extreme
smoothness (median norm fully 10⁴-smooth). Residue-degree law: v_p(norm) ≡ 0 mod
ord₃₂(p), 0 violations/1,142 — exponent-1 bad primes MUST be split, proving the sweep's
empirical pattern. Perfect-power structure matches stabilizers 7,743/7,748. Artifacts:
rungs/laneA2/ (orbit data, rate-law tables, factorizations, all cross-checked against
the committed certificate exactly).

## A3 / G1 / G2+G3 / G5 — PENDING (session limit 2026-06-11 ~03:40 UTC; re-queue after reset)

## G1 — VERDICT: CONFIRMED, all 40 entries exact (2026-06-11, inline)
**The menu law is a theorem.** Per dense element with block B: cross-pair loci over the
35 witnesses are Z_J = (B∩{z*}) ∪ ⋃_{i∈J} b_i for traces J ⊆ N(B), with multiplicity
exactly **C(m₀, 4−|J|)** (m₀ = B-empty pairs; proof: disjoint blocks make the locus
determine I∩N, completions free among empty pairs). Aggregate evenness: negation fixes
squares, so t and ν(t) carry the SAME B — every aggregate multiplicity inherits the
B-census {2,4} factors. Verification (lane_g1_menu_law.py, on kernel-regenerated data):
analytic aggregate == measured menu in ALL 40 entries; total 47,040; distinct 4,072.
General-s form: multiplicity C(m₀, s/4−|J|) over the s/2−1 pair-blocks — the incidence
menu at every rung is B-census convolution with this kernel.

## G5 — VERDICT: REFUTED, informatively (2026-06-11, inline; exact computation, no truncation)
The pre-registered falsifier fired: the exact union (Möbius over all 2¹⁶ loci,
partition-checked Σ exact(D) = q¹⁶) and the union-bound sum agree to 9 significant
digits — slack factor 1 + O(1/q). Mechanism: V-space overlaps are q^(16−2|Z∪Z′|) ≤
(1/q)·min terms — over a 2×10⁹-element field, inclusion–exclusion corrections are
measure-negligible BY CONSTRUCTION, regardless of how much the loci overlap
combinatorially (the 11.55 multiplicity is real but lives in counting, not measure).
Findings: (i) a 31-locus antichain (7 singletons + 24 pairs) carries the whole union;
(ii) the union exceeds the 47,040 actual differences by 2.7×10¹²⁶ — **the entire open
content of level-1 counting is the weight filter, not locus incidence**. REDIRECT: the
lane's counting target shifts from "overlap corrections" to "how the weight filter cuts
a per-locus space" — the measure of {f ∈ V_Z : wt(f) ≤ w} vs q^(16−2|Z|)·(ball fraction),
where smooth-domain structure must enter. lane_g5_union_exact.py = the computation.

## W1 (post-G5 redirect, pre-registered 2026-06-11): the weight-filter cut
Constraints: O135 proved the union bound measure-tight — level-1 counting's open content
is #{f ∈ V_Z : wt ≤ w} vs the generic volume fraction. Why not done: the redirect is
hours old; all prior counting treated the weight filter via union bounds. No-larping:
the dossier's "syndrome-space lens" is untried per §5; the census-conditional pin
consumes census counts, not weight-conditional measures. Novel: first direct measurement
of how a locus space meets the weight ball, smooth vs random domain.
HYPOTHESIS W1: at toy scale (q=97, n=32), conditioned on f ∈ V_Z (slices vanishing on a
size-z locus), the probability of list-band weight (wt ≤ 27, i.e. ≥ 5 domain zeros) on
the SMOOTH domain μ₃₂ exceeds the same probability on random 32-point domains by a
factor consistent with the census excess — i.e. the smooth-domain structure concentrates
low-weight mass inside locus spaces. Falsifier: smooth/random ratio ≈ 1 within sampling
error (then the census excess lives elsewhere — e.g. only at the exact-anatomy weights).

## W1 — VERDICT: falsifier FIRED, sharply (2026-06-11, inline)
On the smooth domain, the excess-zero distribution of V_Z samples beyond the forced
2|Z| dichotomy zeros is **Poisson-generic to 4 decimals** (|Z|=3: P₀ 0.7644 vs
Poisson(26/97) 0.7649; |Z|=5: 0.7967 vs 0.7971; 10⁵ samples each, q=97, n=32).
**The weight-filter cut on smooth domains = forced (census) × generic (Poisson)** —
no smooth concentration beyond the dichotomy. The random-domain comparison columns are
contaminated by unmodeled coincidental partners/square-collisions (per-domain forced
accounting needed; noted, not pursued — the smooth-vs-Poisson match is the verdict and
needs no comparison). IMPLICATION: direct empirical support for the census-conditional
pin — at level 1, the census/anatomy counts are the ONLY non-generic input; the weight
filter contributes generic volume only. Together with O135 (union bound measure-tight):
level-1 counting is COMPLETE given the census — exactly the reduction the
CensusConditionalPin program assumes. lane_w1_weight_filter.py + this entry.

## G2 — VERDICT: REFUTED at n=64, by exact char-0 identities (2026-06-11)
34 violations / 2,329,470 pairs (6,435 witnesses × 340 census + 22 O134-spurious
elements). The mech classification: ALL 34 are CHAR0-IDENTITY — the extra collisions
reproduce at p₂ identically (prime-independent), the same cyclotomic-identity class as
the n=32 dense-dense excess (O129), now appearing in the witness–dense cross channel.
**The exactness law is rung-bounded**: exact at s = 8/16 cross pairs (proven, certified),
fails at s = 32 with a finite family of exact identities (O(10) per the run). The
certificate framing survives — in char 0 the collisions are explicit identities, not
noise. Verified by independent rerun of the in-tree script (deterministic, 6 s).

## G3 — VERDICT: CONFIRMED at n=64 (2026-06-11)
0 violations / 2,329,470: the dead-fiber dichotomy (locus = S∩B) is RUNG-GENERAL —
including on the 22 prime-spurious O134 elements (char-p-only objects obey the same
incidence anatomy). The S∩B lattice is the incidence geometry at every scale tested.

## G1-general — blind-CONFIRMED at s=32 (same run)
The general menu law C(m₀, 8−|A|−|J|) passes on all 362/362 elements (census AND
spurious) — first blind test at a new rung, as pre-registered.

## A3 — PARTIAL: s=8 leg CONFIRMED (2026-06-11; s=16 leg pending capacity)
Across the λ-family at s=8 (multiple fiber sizes, 563 pairwise checks): zero excess
everywhere — exactness is not max-fiber-specific at the base rung. s=16 script staged
(laneA3/lane_a3_s16_pairs.py), unrun.

## Record note (the discipline): the G2G3/A3 artifacts were written by lanes that died
on the weekly cap mid-report; they entered the tree in the O145 (W1) commit's sweep
before being described. This entry + the independent rerun close the gap: every number
above was reproduced from this seat before being recorded.
