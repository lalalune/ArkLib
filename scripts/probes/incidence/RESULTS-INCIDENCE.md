# The incidence laboratory: difference-loci on the proven-complete list configurations

Lane: nubs, claimed #232 (2026-06-10, comment 4667894636) as the complement of
lalalune's 07:11Z lane 2 — dense layers, slice spread of differences, cross-level
persistence, union-bound loss on dense mass. After O109/O115/O118 closed the counting
side, this lane's object — the locus-overlap/incidence channel — is the program's named
sole survivor (with δ*); these are its first measurements, plus the first theorem.

## Inputs and gates (all hard, all passed before any number below was believed)
- n=16 independent Python sweep: list 19 = 3 + 16, witnesses agree-10 all-even-support.
- n=32: the production kernel (patched this commit with an `#ifndef A` guard) at
  `-DA=17` emits BOTH layers; 1,974 raw rows (= the census's functional-pass count)
  distill to exactly the 35 constructed `u_S(X²)` witnesses (bit-exact) + 1,344 dense,
  each verified individually (agree exactly 17, deg < 16, distinct).
- Independent second generator (`exactness/lane_a.py`): the 1,344 reconstructed from
  the consistency-equation dictionary, no kernel involved — same set.

## THE EXACTNESS THEOREM (the headline; computational proof, second-seat audited)
**Statement.** Over `ℤ[ζ₃₂]`, every witness–dense difference `c_w − c_t` of the
canonical max-fiber configuration vanishes on `μ₃₂` exactly on `T_w ∩ T_t` — no
accidental zeros. Consequently the law holds at a split prime `p ≡ 1 (mod 32)` **iff
`p` divides none of an explicit set of 13,219 algebraic norms** (Galois/sign-orbit
representatives, all < 2.2·10²⁴). BabyBear `15·2²⁷+1` and `3·2³⁰+1` divide none —
the law at both production primes is proven twice (directly + by certificate).
**The law is NOT anatomy-forced in char p:** it fails at all 20 split primes
97..2113 tested, at the generic rate ≈ 6.7/p, with explicit counterexamples
(e.g. p = 97: S = {22,1,96,8,89,33,64,27,70}, B = {1,8,64,27,22,79,96},
x = (27,50,85): extra zero at H[28]). The bad-prime list predicted by the norm
certificate matches the observed sweep failures exactly.
**Structural lemmas** (paper-level, the `e_w`-even lever; `d(x) = P(x²) + x·Q(x²)`,
`P = F·q_e − E`, `Q = −e₃·F`): (a) every dense word has `e₃ ≠ 0` (else its agreement
count would be even); (b) dead-fiber dichotomy: a full fiber over `z` dies iff
`z ∈ S ∩ B` — so accidental collisions are ALWAYS single zeros with live partner
(`d(−x₀) = 2x₀e₃F(z) ≠ 0`), confirmed 0 dead-fiber accidents among ~10,800 observed
extra zeros across 20 primes; (c) zeros are governed by `N(Y) = P² − Y·Q²` (deg 15):
forced doubles at `S ∩ B`, forced singles at `xᵢ² ∈ S`, accidents = free roots of `N`
landing on `μ₁₆ ∖ (S ∪ B)` — codim-1 in char p (the 1/p law), absent in char 0.
**Honest uncertainties:** the char-0 nonvanishing is a finite exact computation, not a
conceptual argument (the open "why": free roots of `N` avoid `μ₁₆` over `ℚ(ζ₃₂)`);
the iff-direction of the bad-prime criterion rests on Galois/mirror stability of the
family (sketched, empirically exact, not formalized); witness–witness pairs not in scope.

## Pre-registered hypotheses → verdicts
**H-INC1 (extra agreements) — REFUTED on cross pairs (now a theorem); literally TRUE
on dense-dense, where the exceptions are exact cyclotomic identities.** Cross:
`|Z₀| = |T ∩ T′|` in 47,040/47,040 (both generators, both primes — index-identical
configurations; run-2 reproduces run-1 exactly, every histogram). Dense-dense
(12,000-pair sample, seed 20260610 — note the index→element map depends on distillation
order, so different pipelines draw different samples; three independent samples agree):
run-2 published numbers {exact: 11,973, +1: 26, +2: 1}; the excess pairs collide at the
SAME points over `ℤ[ζ₃₂]` and at both primes — mechanism observed: pairs sharing two
q-roots `{x_a, x_b}` collide exactly at the antipodes `{−x_a, −x_b}`. Every excess pair
is identified per-pair in the probe output (all are non-negation pairs).
**H-INC2 (spread blindness) — CONFIRMED with a structured exception class.** Cross:
branch-maximal (2,4,8) in all 47,040. Dense-dense: 11,986/12,000 maximal; the
exceptions, identified per-pair: 8 × (1,2,4) — ALL negation pairs (population check:
all 672 negation pairs have spread (1,2,4); the sample's 8 matches the expected ≈ 8.9)
— plus a non-negation tail 3 × (2,4,6), 2 × (2,3,6), 1 × (2,4,7) (observed, mechanism
open). Negation differences `c − c∘(−X)` are odd-supported: the difference drops a full
tower level. Incidence information lives in the point loci, not the coefficient spread.
**H-INC3 (locus sharing = union-bound loss) — CONFIRMED.** 4,072 distinct level-1 dead
loci over 47,040 cross pairs (mean multiplicity 11.55; max 144; full multiplicity menu
in the probe output — low-multiplicity mass concentrated at 2 and 4, echoing the
B-census {2,4} pattern; the menu also has higher even entries). Dense-dense sample:
2,666 distinct / 12,000 (mean 4.50; 32 pairs have EMPTY level-1 locus — the L1 floor is
not universal off the witness layer). L1 dead-fiber sizes 1–7 on cross pairs (never 0; the
≤ 7 cap is the trivial deg ≤ 15 bound — attainment is the empirical content); L2 dead
fibers exist for ≈ 63% of cross pairs (derived from the L2 size histogram).
**H-INC4 (persistence) — CONFIRMED in shape.** n=16 reference: cross (48 pairs) → 15
distinct loci, dense-dense (120) → 13, L1 sizes 1–3: massive sharing at both levels
with refined (not rigid) values.

## The union-bound loss, measured
Each level-1 locus is shared by ~11.55 cross pairs on average (max 144) — the
O97/O99-template union bound over-counts by at least an order of magnitude at level 1
on the real configuration (locus-count-weighted; the probability-weighted slack is a
finer open question). By the dead-fiber dichotomy the cross-pair loci are EXACTLY
`S ∩ B` — the incidence geometry of witness–dense pairs is the intersection lattice of
the 35 fiber-subsets with the 580 B-blocks, fully combinatorial.

## Honest scope
One word (canonical max-fiber λ), one radius pair (18/17); the exactness theorem covers
exactly this configuration at all split primes; dense-dense is a 12,000-pair
deterministic sample. Incidence numbers beyond the theorem are BabyBear measurements.

## Reproduction
gcc -O3 -march=native -DA=17 ../n32census/census_kernel.c -o census17
for i in $(seq 0 15); do ./census17 $i c17_$i.txt & done; wait   # ~4 min, both layers
python3 probe_incidence.py 'c17_*.txt'                            # gates + measurements
python3 exactness/lane_a.py && python3 exactness/char0.py && python3 exactness/norms.py
python3 exactness/sweep.py                                        # the 20-prime falsification
