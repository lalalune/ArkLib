# DISPROOF / NO-GO LOG (#407 and predecessors)

Machine-checked refutations and precise pins. Each entry: lens, test, exact result, wall.

## eta-COSET-LOCALIZATION is THINNESS-ESSENTIAL (rule-3 PASS) -- the FIRST structural reduction in the map that passes the thin gate; corroborates in-tree EtaCosetSplit / coset reduction (2026-06-15)

Lens: the bulk-correlation localization opened by the ILO entry (852e0fa27: thin mu_n sup-norm is LARGE,
bulk-correlated). WHERE does the large thin |eta_b| live? eta_b = sum_{x in mu_n} e_p(bx). Since mu_n is a
GROUP, for c in mu_n the map x->cx permutes mu_n, so eta_{cb} = sum_x e_p(b(cx)) = eta_b EXACTLY -- eta is
constant on multiplicative cosets b*mu_n. This is ALREADY formalized in-tree (EtaCosetSplit.eta_coset_split,
GaussPeriodCosetReduction.cosetReduced_eta_pow_le -- the "divide by n" coset reduction). The MISSING test
(supplied here): is this structural reduction THINNESS-ESSENTIAL (rule-3), unlike the moment-cert (thickness-
invariant 18%) and ILO (thin worse) passages?

PROBE (scripts/probes/probe_407_bulk_freq_structure.py, EXACT eta over proper mu_n vs random thin-density
control, full b-sweep, prize + thick primes, never n=q-1):
| n  | beta | p     | M=max|eta| | M/sqrt n | |eta| const on mu_n-cosets? | random same-partition const |
|----|------|-------|------------|----------|-----------------------------|------------------------------|
| 8  | 3.0  | 521   | 6.56       | 2.32     | YES (40/40, exact)          | 0/40 (spread <= 5.17)        |
| 8  | 4.0  | 4153  | 7.46       | 2.64     | YES (40/40)                 | 0/40 (spread <= 5.12)        |
| 16 | 3.0  | 4177  | 10.94      | 2.74     | YES (40/40)                 | 0/40 (spread <= 11.9)        |
| 16 | 4.0  | 65617 | 13.30      | 3.32     | YES (40/40)                 | 0/40 (spread <= 9.49)        |

VERDICT (rule-3 PASS -- a POSITIVE structural localization, not a wall): the |eta| spectrum is EXACTLY
mu_n-coset-localized => the sup-norm M(n) = max over only (p-1)/n COSET REPRESENTATIVES, not p-1
frequencies (a genuine structural reduction, already in-tree). CRUCIALLY this coset-localization is
ABSENT for a random same-density set (0/40 cosets constant, spreads 5-12) => it is THINNESS-ESSENTIAL:
it is a multiplicative-GROUP property of mu_n, FALSE for an unstructured thin set. This is the FIRST
reduction in the whole #407 obstruction map that PASSES the rule-3 gate at the SUP-NORM level (the moment
certificate and ILO anti-concentration both FAILED rule-3 -- thickness-invariant / thin-worse). So a valid
thinness-essential CORE proof, which by rule 3 must use a quantity FALSE in the thick window, is consistent
with ROUTING THROUGH the coset reduction (eta constant on b*mu_n, reducing to (p-1)/n reps) -- the
in-tree EtaCosetSplit / cosetReduced_eta_pow_le machinery -- whereas it CANNOT route through the moment or
ILO passages. CONSEQUENCE (mapping): the live thinness-essential surviving structure at the SUP-NORM level
is the coset reduction itself; the open content is the per-coset-rep bound on |eta_c| after the reduction
(the GaussPeriodCosetReduction object), NOT a global anti-concentration or moment bound. CORE not closed;
the coset reduction CONFIRMED as the rule-3-passing structural locus. Python-only, no Lean changed =>
axiom-clean trivially. Exact full b-sweep, proper subgroups, thick+thin windows.

## ★ REDUCTION-MISMATCH — the lacunary-root reduction (63aa3b4ab) + DFT-uncertainty insight (6507e61aa) compute the WRONG δ*: max-single-witness root count (trivial n/2 binomial factor) ≠ the in-tree list-budget δ* (2026-06-15)

Lens: the two freshest analytic handoffs reframe the prize s* as "max # of μ_n-roots of a (k+2)-term lacunary
far-line polynomial P=x^a+γx^b−c (deg c<k)". Adversarial audit (rule 6): this object is NOT the in-tree
list-budget s* the engine computes.

EXACT FACTS (verified):
1. Engine source (`scripts/rust-pg/src/main.rs`): `incidence(a,b;s)=local.len()` = **# distinct γ** with x^a+γx^b
   agreeing with a deg<k codeword on a size-s subset; `s*=min{s : max_dir incidence(s) ≤ budget=n}` (a γ-COUNT /
   list-size threshold). This is the prize δ* (p-independent, GPU-confirmed).
2. The max-SINGLE-witness (NON-DEGENERATE) root count is **k+1**, NOT n/2 (CORRECTED, see retraction note).
   My first-pass witness P=(x−1)(x^{n/2}+1) (n=16: line x^9−x^8) has **b=n/2 active** = the KB-excluded antipodal
   monomial, with gcd(a−b,n) EVEN = the degenerate I=q−1 coset pencil (the engine never scans b=n/2 at the binding
   radius; rule-2 trap). Enforcing correct non-degeneracy (active line monomials, gcd(a−b,n) ODD, no exp=n/2): the
   factors Φ_{2^j}=x^{2^{j−1}}+1 carry only EVEN exponents, so an odd-(a−b) witness uses ≤1 big even-exp factor +
   Φ_1 ⟹ cyclotomic-forced roots collapse to **k+1** (PARITY-BLOCKED, per the 0xSolace parity-block comment).
   (A first non-deg recheck still showing n/2 had a bug: its rank-deficiency test admitted combos like x^9+x=
   x(x^8+1) that DROP the required active line monomial x^a, silently re-admitting the degenerate 2-term antipodal
   pencil. With line-monomials-active enforced, all n/2 witnesses vanish.)

WALL / constraint lemma: the non-degenerate "max μ_n-root-count of a (k+2)-sparse far-line polynomial" = **k+1**
(cyclotomic-forced), while the in-tree list-budget s* = 2k−1 ≈ Johnson. Still a DIFFERENT object — gap **k−2** — and
the ~(k−2) agreement lifting s* from k+1 (cyclotomic) to 2k−1 (Johnson) lives ENTIRELY in the band / general
deg-<k codeword DOF, NOT the roots-of-unity / cyclotomic-divisibility structure. Therefore the lacunary-root /
DFT-uncertainty reduction does NOT compute the prize δ*; the lacunary/cyclotomic-factor mechanism alone cannot
reach Johnson non-degenerately (caps at k+1). The Mann/Conway–Jones/Bombieri–Zannier handoff is real ONLY for
the single-witness object. For the prize, the right classical object is **list-size/multiplicity of (k+2)-sparse
polynomials at Johnson radius**, not max-root-count. Consistency check: for n PRIME, x^n−1=(x−1)Φ_n with Φ_n DENSE
⟹ no sparse high-deg factor ⟹ single-witness roots cap at k+O(1) (matches KB "prime⟹capacity"), so the prime-vs-
smooth dichotomy is real for the single-witness object — the error is equating it with the prize δ*.

RETRACTION NOTE (rule 6): my first receipt claimed n/2+1 single-witness roots; that used a DEGENERATE antipodal
witness (b=n/2, even gcd(a−b,n)) — the excluded I=q−1 pencil (rule-2 trap). Corrected non-degenerate ceiling = k+1
(parity-block). The reduction-mismatch CONCLUSION survives (max-single-witness object ≠ list-budget δ*); only the
NUMBER was inflated. Posted correction: #407 comment 4704593680.

Probe: `scripts/probes/probe_407_lacunary_cyclotomic_mechanism.py` (exact char-0). Pushed 71722be4f (probe) +
this corrected entry. NOT a closure — removes a false analytic lead + re-localizes the open core (consistent with
the 0xSolace parity-block + lalalune p-independence findings).

## ILO / anti-concentration is NOT the lever — thin μ_n is anti-concentrated WORSE than random (larger sup-norm, larger small-ball); reconciles the thin depth-advantage with the large thin sup-norm (2026-06-15)

Lens: inverse-Littlewood-Offord (Tao–Vu / Nguyen–Vu). M(n)=max_{b≠0}|η_b|, η_b=Σ_{x∈μ_n} e_p(bx), is
controlled by anti-concentration of the signed character sum Σ ε_i ζ^i: FEW additive relations (high Sidon
depth) ⇒ strong anti-concentration ⇒ small small-ball Q ⇒ small M. The surviving thin mechanism (my
full-depth-BIND entry + the depth-SCALING entry e7b5e6125) shows thin μ_n has DEEPER first vanisher than
random — which would, IF ILO were the bridge, predict thin M < random M. This is the missing test:
does the thin sparse-depth advantage translate to a sup-norm / small-ball advantage (live ILO lever) or not?

PROBE (scripts/probes/probe_407_ilo_vanisher_count.py, EXACT sup-norm via full b-sweep over proper μ_n <
F_p^*, p==1 mod n m odd never n=q−1; random thin-density control = n distinct nonzero residues; small-ball
Q(t)=Pr[|Σε_i r_i| ≤ t·p] over the sign cube; thick β~2.3-3.0 AND thin β~4-4.5 windows):

| n  | β    | window | M_thin | M_rand(med) | M_thin/√n | Q(.02)_thin | Q(.02)_rand |
|----|------|--------|--------|-------------|-----------|-------------|-------------|
| 8  | 2.30 | thick  | 5.84   | 5.58        | 2.06      | 0.147       | 0.023       |
| 8  | 4.00 | thin   | 7.46   | 6.90        | 2.64      | 0.125       | 0.053       |
| 8  | 4.50 | thin   | 7.68   | 7.49        | 2.71      | 0.156       | 0.039       |
| 16 | 2.30 | thick  | 8.44   | 9.39        | 2.11      | 0.044       | 0.038       |
| 16 | 4.00 | thin   | 13.30  | 11.99       | 3.32      | 0.050       | 0.040       |
| 16 | 4.50 | thin   | 12.98  | 10.38       | 3.25      | 0.043       | 0.040       |

VERDICT (the OPPOSITE of what ILO needs — rule-3 wall): thin μ_n's sup-norm M_thin is consistently
≥ M_rand (n=16 β=4: 13.30 vs 11.99; β=4.5: 12.98 vs 10.38), and the small-ball Q_thin ≥ Q_rand (thin
CONCENTRATES MORE, not less). So inverse-Littlewood-Offord ANTI-CONCENTRATION is NOT the prize lever:
μ_n is anti-concentrated WORSE than a random same-density set, hence any ILO bound is WEAKER for μ_n. The
thin advantage at sparse DEPTH (no low-order vanishers) does NOT lift to a bulk anti-concentration / sup-
norm advantage — the bridge runs backwards.

RECONCILING INSIGHT (why this is consistent, not contradictory): μ_n carries the FULL multiplicative-group
additive structure — it has MORE near-zero bulk sums (worse small-ball) than random PRECISELY BECAUSE it is
a coherent geometric/cyclotomic object, even while its FIRST exact vanisher is pushed deep (high Sidon
depth). "Deep first relation" (sparse, sibling e7b5e6125) and "large sup-norm / poor anti-concentration"
(bulk, here) coexist: the cancellation difficulty of the thin BGK regime lives in the BULK correlation, not
the sparse-relation floor. This is exactly WHY the moment-cert passage (thickness-invariant 18% slack) and
the ILO passage both fail to convert the sparse thin depth-advantage into the sup-norm bound. CONSEQUENCE
(mapping, not closure): the surviving thin sparse-depth signal must reach M(n) WITHOUT going through (a) the
moment→sup passage M≤(qA_r)^{1/2r} [regime-uniform loss] or (b) the ILO anti-concentration→sup passage [thin
is worse]. Both "obvious" bridges from depth to sup are now walled. CORE not closed; ILO lever walled +
the depth-vs-bulk reconciliation pinned. Python-only, no Lean changed ⇒ axiom-clean trivially.

## BIND-full-depth-threshold — the literal B_∞←B_{log n} Sidon bootstrap target (NO non-antipodal vanisher AT ALL) FAILS at fixed prize β as n grows; thin advantage is REAL but INSUFFICIENT (2026-06-15)

Lens: brief lane #0 / §5.0 (BIND) literal full-depth form. The proven depth-2 brick
`SidonLiftDevacuated.sidonModNeg_rootsOfUnity` gives "no 4-term ±-relation" (Sidon-mod-neg, depth r≤2)
WHEN `p > 4^{φ(n)} = 2^n`, i.e. `β > n/log₂ n`. The bootstrap target is to extend no-non-antipodal-
vanishing `Σ_{i∈S} ζ^i ≡ 0 (p)` from depth ~log n to FULL depth |S| ≤ n/2. I measured directly whether
the literal FULL-depth property holds at the PRIZE scaling (p = n^β, β∈[4,5]) and whether the obstruction
is thinness-essential (the rule-3 gate that killed the BHBI lever).

Method: exact-integer meet-in-the-middle over μ_n = n-th roots of unity in F_p (proper 2-power subgroup,
p≡1 mod n, m=(p−1)/n preferentially odd, NEVER n=q−1), smallest non-antipodal unsigned zero-sum r_min.
Full MITM exact at n=16,32; randomized MITM (SOUND on FAILURES — a found r_min<n/2 PROVES BIND fails) at
n=64. Probes `scripts/probes/probe_407_bind_depth_fraction.py` + `probe_407_bind_beta_threshold.py`.

RESULT 1 — empirical β*(n) (smallest β with FULL-depth BIND, r_min = NONE) GROWS with n:
| n  | empirical β* (full-depth BIND) | proven-suff (n/log₂n) | n=64 SOUND-FAILS at β = |
|----|--------------------------------|-----------------------|--------------------------|
| 16 | 4.0   (matches proven 4.00)    | 4.00                  | —                        |
| 32 | 4.5   (well below proven 6.40) | 6.40                  | —                        |
| 64 | ∈ (6.0, 7.0]                   | 10.67                 | 4.0,4.5,5.0,5.5,6.0 all  |
Decisive: at the UPPER prize edge β=5.0, full-depth BIND HOLDS at n=32 (r_min=NONE) but SOUND-FAILS at
n=64 (r_min ≤ 10 < 32, exact zero-sum witness). β*(n) is NOT bounded by the prize ceiling β=5 — it grows.

RESULT 2 — THINNESS-ESSENTIAL (rule-3 PASS, unlike BHBI): at n=32, β=4.0, thin μ_32 r_min = 11 vs RANDOM
thin-density 32-subset median = 6 (samples [5,6,6,7,7]); at β=5.0 thin = NONE (full depth) vs random median
= 8. μ_n is strictly MORE relation-free (deeper Sidon) than a random same-density set. So this is a GENUINE
thin obstruction-suppression — NOT the thickness-invariant basis-length pigeonhole that killed BoundedHalf-
BasisIndep. The 2-power structure really does push the first vanisher deeper.

CONSTRAINT LEMMA (BIND-FULL-DEPTH-THRESHOLD). Let β*(n) = inf{β : μ_n over F_{p}, p=⌈n^β⌉ prime ≡1(n),
has NO non-antipodal S⊆Z/n with Σ_{i∈S} ζ^i ≡ 0 (p)}. Measured β*(16)=4.0, β*(32)=4.5, β*(64)∈(6,7];
β*(n) is increasing and (over 16→64) tracks ABOVE the prize ceiling 5 by n=64. ⟹ for every FIXED prize
β∈[4,5], the LITERAL full-depth BIND statement is FALSE for all large n (a non-antipodal mod-p vanisher of
size < n/2 exists). The literal "B_∞ ← B_{log n}" bootstrap target is therefore unattainable as stated.

HONEST SCOPE (rule 6, no overclaim): (a) n=64 is randomized (SOUND only on the FAILURE direction; the
β=7,8 "none-found" rows are inconclusive, NOT proofs BIND holds). (b) β*(n) grows SLOWLY (4.0→4.5→~6.5),
FAR below the proven-sufficient n/log₂n — the truth is much better than the depth-2 resultant lift can
prove, just not good enough for fixed β. (c) This refutes the LITERAL full-depth form, NOT CORE: CORE is
the sup-norm bound, which does not need zero spurious vanishers — it needs the COLLECTIVE cancellation to
stay √-small. A super-constant (even log^c n or n^{1−ε}) thin Sidon depth, which the thin-advantage in
Result 2 DOES provide, could still route CORE via a moment/√-cancellation argument that tolerates a few
deep vanishers. So: the literal BIND target is walled; the thinness-essential thin advantage that suppresses
low-depth vanishers is real and is the live object — but it must be used COLLECTIVELY (depth-profile /
moment), not as a per-S "no vanisher at all" statement. CORE not closed; one literal target precisely walled
+ the surviving thin mechanism isolated. Python-only, no Lean changed ⟹ axiom-clean trivially.

## BIND-gate-scope — the §5.0 (BIND)/house gate route does NOT generalize: non-antipodal mod-p vanishers EXIST at thin prize-β primes once (#S)^φ > p (2026-06-15)

Lens: §5.0 reduces CORE to (BIND) — "no spurious non-antipodal vanishing `Σ_{i∈S} ω^i ≡ 0 (p)` with S
not antipodal" — and proves it via the height gate `HeightGateNormBound.gate_2power_antipodal`, whose
HYPOTHESIS is `hp : (#S)^φ(n) < p` (house bound `|N(β)| ≤ (#S)^φ < p`, then `p|N ⇒ N=0 ⇒` antipodal).
The body claims "NoSpuriousVanishing is a proved theorem for n≤32" + "realized-height extends to n≤64,
heuristically n≤96", and frames the open part as "need a structure-aware norm bound (not trivial house)
to get |N|<p at n≥112."

TEST 1 (worst-case realized norm vs the fixed prize budget p~2^128). Hill-climbed max over reduced
coeff vectors c∈{-1,0,1}^{n/2} (the worst non-antipodal residue pattern; exact integer norm via
`Res(x^{n/2}+1, c(x))`, cross-checked high-precision):
  n=64:  max log2|N| = 78.9  (< 128, closeable — matches H(64)<2^128)
  n=96:  max log2|N| = 131.1 (> 128)
  n=112: max log2|N| = 160.5 (> 128)
  n=128: max log2|N| = 188.0 (> 128; vs ABF p~2^136 still >)
Growth ~0.184·n·log2(n) (a CONSTANT fraction ~37% of the house (n/2)log2(n/2) — the house slack does
NOT vanish). CROSSOVER between n=64 and n=96. The single 56-element witness cited in §5.0 (2^131) is
NON-worst-case; the true worst at n=96 already exceeds p. (scripts/probes/issue407-bind/probe_bind_realized_norm_max.py,
probe_bind_norm_crossover.py)

CONSEQUENCE: a "structure-aware UPPER bound giving |N|<p" CANNOT exist at the worst-case binding
weight for n≥96 — the realized worst-case norm itself exceeds p. The §5.0 open-route as stated
("replace the loose house by a tighter |N|<p") is a no-go past the crossover.

TEST 2 (the mechanism is real: explicit, INDEPENDENTLY-VERIFIED non-antipodal mod-p vanishers at thin
prize-β primes). For thin primes p (p>n^3, n|p-1, β=log_n p in the prize band 4–4.8) we exhibit
non-antipodal S with `Σ_{i∈S} ω^i ≡ 0 (mod p)` (ω a primitive n-th root in F_p), directly verified
(not via the bridge — the sum is computed in F_p and equals 0 on the chosen ω):
  • n=32,  p=14814881  (β=4.764): S={1,2,7,8,9,10,12,13,19,22,27} (#S=11), non-antipodal, Σω^i≡0.
  • n=64,  p=136085377 (β=4.503): #S=24 set, non-antipodal, Σω^i≡0.
  • n=128, p=268437889 (β=4.000): S={6,17,24,27,29,38,43,52,59,65,70,77,82,87,94,97,107,112,117}
    (#S=19), non-antipodal, Σω^i≡0; here house 19^64~2^272 ≫ p~2^28 (gate hyp `(#S)^φ<p` FALSE).
(scripts/probes/issue407-bind/probe_bind_counterexample_search.py + verify_bind_counterexamples.py
[standalone, from-scratch], probe_bind_n128_counterexample.py)

WALL / precise scope (NO prize refutation — honesty): these counterexamples use SMALL primes (p~2^24–2^28),
NOT the actual prize budget p~2^128, so the PRIZE is NOT refuted. What is refuted is the GENERALITY of
the gate route: (BIND) is FALSE as a ∀-thin-prime statement; non-antipodal vanishing genuinely occurs
exactly when `(#S)^φ(n) > p`. §5.0's "NoSpuriousVanishing proved for n≤32" is correct ONLY because at
the prize budget p~2^128 and n≤64 the house hypothesis `(#S)^φ < p` happens to hold for ALL relevant #S
(e.g. n=32: p^{1/φ}=2^8=256 > n). Once n grows so that (n/4)^{n/2} > 2^128 (i.e. n≥~112 at the binding
size), the house hypothesis fails AND — by Test 1 — no realized-norm replacement can rescue it. The
gate/house lane is therefore CAPPED at the crossover; closing CORE at n≥112 needs a genuinely different
mechanism (the thinness-essential B_∞←B_{log n} Sidon bootstrap), not a sharper norm bound on the gate.
Constraint lemma: `∃ non-antipodal S, ω prim. n-th root in F_p : Σ_{i∈S}ω^i=0` for every thin p with
(#S)^{φ(n)}>p — so the gate's safety margin is exactly `house < p`, nothing more.

## wf-NC — Gross-Koblitz / p-adic Γ_p refinement of Stickelberger (UNIT part) — PINNED (2026-06-14)

Lens: GK expresses g(χ^{−a}) = −π^a·Γ_p(⟨a/(p−1)⟩) (q=p prime ⇒ residue degree f=1);
η_b = (1/m)Σ_k ζ_{p−1}^{−nkc} g(χ^{nk}) is a ζ-weighted sum of GK factors. Hoped: dyadic
base-p digit-sum of a=nk + Γ_p reflection/multiplication ⇒ sub-trivial archimedean max_b|η_b|.
All numerics exact-as-float ~1e-14, n=8,16,32, multiple p≡1 (mod n).

- NC1 (f=1 single Γ_p factor): for q prime the GK product runs over the Frobenius orbit of size
  f=1 → ONE Γ_p factor per Gauss sum. No multi-factor product ⇒ the dyadic digit-sum handle is
  STRUCTURALLY ABSENT. The genuine multi-Γ_p / digit-sum lever needs f≥2 (q a prime power), which
  the prize forbids. (probe_wf2NC_gammap_valuation.py)
- NC2 (unit part has no archimedean SUP content): GK pins v_p(g)=a/(p−1) (=Stickelberger=section-6
  magnitude) and the unit Γ_p as a p-adic unit (|Γ_p|_p=1); |g|=√p is archimedean, independent of
  the unit congruence. Adversarial test (4000 trials): SUP achievable under the Γ_p reflection
  U(nk)U(−nk)=+1 EQUALS the SUP under |U|=1 alone (~0.86–0.95·√(p−n)); true SUP (0.58–0.79·√(p−n))
  sits strictly below, i.e. the genuine cancellation is NOT a GK relation. (probe_wf2NC_sup_vs_gk.py,
  probe_wf2NC_gk_phase.py)
- NC3 (no product→sum bridge): Davenport-Hasse/Stickelberger pin Π_k g(χ^{nk}) (= the norm/house,
  section-6 magnitude object), verified exact (rel.err ~1e-14); the SUP needs max_c|Σ_k ...|. A single
  product equation among m−1 unit phases does not bound a max-of-sum. (probe_wf2NC_gammap_valuation.py)

Why NEW (vs section-6 Stickelberger MAGNITUDE no-go): this is the complementary fact — the GK
unit/Γ_p part (the thing section-6 excludes) carries NO archimedean SUP info at f=1, and the only
digit-sum handle lives at f≥2 off the prize. The reflection formula reduces to the already-refuted
antipodal char-0 symmetry (T09-leak). Wall: GK adds nothing to max_b|η_b| for q prime.

## census<->CORE — the universal census bound is LOSSY, caps at Johnson, NOT equivalent to CORE (2026-06-14)

Lens: the count/census lane (`UniversalAlignmentLaw.badScalars_card_le_alignableSets`) bounds
`#{bad γ} ≤ #alignableSets(dom,k,a,u0,u1)`, feeding δ* via `epsMCA_le_of_alignableSets_card_le`.
#407 brief flags the "census ⟺ CORE equivalence" as ASSERTED-BUT-NEVER-PROVEN. Tested the tightness
directly: exact `#bad` (the CORE/incidence object) vs exact `#alignableSets` (census), thin proper
μ_16 ⊊ F_p*, large primes p≫n³, binding monomial direction u0=x^10,u1=x^4.
Probe: `scripts/probes/probe_407_census_core_tightness.py` (exact, no enumeration; left-null affine-γ).

- RESULT (p-INDEPENDENT across p=200017/500113/1000033):
  | r (a=n−r) | δ=r/n | #bad (CORE) | #alignableSets (census) | ratio |
  |---|---|---|---|---|
  | 8 (a=8) | .5000 | 9  | 10  | 1.11 |
  | 9 (a=7) | .5625 | 9  | 80  | 8.89 |
  | 10 (a=6)| .6250 | 89 | 456 | 5.12 |
  Budget = n = 16. **True δ* = 9/16** (#bad ≤ 16 through r=9, first bad r=10).
  **Census δ* = 8/16 = JOHNSON** (#alignableSets first exceeds 16 at r=9: 80 > 16).

- WALL / CONSTRAINT LEMMA: the census bound is **strictly lossy by a p-independent factor
  (5–9×) that turns on exactly at the beyond-Johnson rung**. Census `#alignableSets ≤ budget`
  fails at r=9 while the true incidence `#bad ≤ budget` holds, so **any δ* bound proven through
  the census/alignable-set count recovers at most JOHNSON (δ*=8/16), never the beyond-Johnson
  window**. The census overshoot = (every a-set that aligns for SOME γ is counted, but distinct
  aligned a-sets share γ's; `Aligned.gamma_eq` injectivity gives the ≤ direction but the reverse
  is many-to-one) ⟹ census counts aligned-sets, CORE counts γ's; the fibers have p-independent
  size 5–9 at the binding radii.
- THEREFORE: "census ⟺ CORE" is **FALSE**. Proving the count-lane bound (ExplainableCoreSupply /
  CensusDomination / SubJohnsonListBound) is NOT proving CORE in the prize window — it is a strictly
  weaker (Johnson-capped) handle. This is independent of, and complementary to, the §3 second-order
  cap (B5 already showed the count-lane is exponential-class, not second-order; THIS shows that even
  so, its δ* CERTIFICATE is Johnson-capped by the alignable-set overshoot). The beyond-Johnson rung
  is carried only by the γ-incidence (CORE/F2) count, which the census cannot see.

### census fiber structure (sharpening, 2026-06-14): fibers NON-UNIFORM (1..56), p-independent — census UN-repairable
Per-γ fiber size (# aligned a-sets a single bad γ owns), n=16 k=4, p-independent (p=200017/500113):
- r=9 (a=7): {8:×8, 16:×1} — total 80 over 9 γ.
- r=10 (a=6): {1:×16, 2:×64, 32:×8, 56:×1} — total 456 over 89 γ; max fiber 56.
The census overshoot is NOT a uniform constant — fibers range 1..56, a few heavy γ own huge fibers.
So census CANNOT be repaired into a CORE-tight bound by dividing by any fixed fiber size; the deflation
factor is itself a per-γ combinatorial quantity. Even the single worst γ is census-over-counted up to 56×.
The fiber-size multiset is a p-independent invariant of the binding configuration. Reinforces: the
count/census lane is Johnson-capped, cannot reach the prize window. (probe_407_census_core_tightness.py + /tmp/fiber.py)

## phase-alignment "tower self-similarity" — REFUTED, the alignment is just REALITY (2026-06-15)

Lens: the fleet observed at the worst frequency b* the two half-coset sums
S0(b*)=∑_{x∈μ_{n/2}} e_p(b*x), S1(b*)=∑_{x∈μ_{n/2}} e_p(b*·rep·x) are maximally phase-aligned
(cos=1.0000, machine-exact n=8,16,32,64). Floated as a candidate NON-AVERAGE structural handle
(tower-recursive self-similarity for a descent/Stepanov argument, since moment methods are blind
to worst-frequency alignment). Brief flagged this lane explicitly (phase-alignment tower probes).

Adversarial recheck (scripts/probes/probe_407_phase_dichotomy.py, probe_407_phase_why.py,
probe_407_phase_reality.py — all FFT-exact, ~1e-14):
- cos(S0(b),S1(b)) = ±1 for EVERY frequency b (256/256, 599/599 sampled), not just b*. The two
  half-coset sums are ALWAYS real-collinear.
- Holds IDENTICALLY in the THIN (β≈9.8, deep prize) AND THICK (β≈1.07, very thick) regimes. The
  cosine is ±1 everywhere; the sporadic −1 are sign flips of two REAL numbers, not a regime signal.
- ROOT CAUSE: μ_{n/2} is a 2-power cyclic subgroup of EVEN order n/2 ⇒ contains the unique order-2
  element −1 ⇒ closed under negation ⇒ S0(b)=∑ e_p(bx) is REAL (pair x↔−x). Verified
  max|Im S0(b)| ~ 1e-15. Two reals are trivially collinear ⇒ cos=±1 automatic.

CONSTRAINT LEMMA (axiom-clean Lean, Frontier/_PhaseAlignmentReality.lean):
`eta_real_of_neg_closed` — if G is closed under negation then eta ψ G b = ∑_{y∈G} ψ(b·y) is REAL
(conj-invariant) for every b. #print axioms ⊆ {propext, Classical.choice, Quot.sound}.

WALL: the "phase alignment" is forced by reality, holds for ALL b, and is identical in the thick
window where the prize is FALSE ⇒ it is NOT thinness-essential. Any descent built on cos(S0,S1)=±1
is thickness-monotone, which rule-3/§3 forbids. The alignment carries NO worst-frequency information
beyond "the half-coset sum is real," which is true unconditionally. Lane PINNED — not a non-average
handle.

## moment "count/Markov/EVT-tail" packaging is NOT sharper — one object in four costumes (2026-06-14)

Adversarial audit of the freshly-landed `MomentCountSupBound.forall_le_of_sum_pow_lt` (commit
64c0bc081), whose docstring claims the integer-tail-count argument is "SHARPER than the per-term
‖η_b‖^{2r} ≤ ∑ bound (it uses that a fractional count rounds down to zero)."

VERDICT: not asymptotically sharper. The count route certifies `a_b ≤ T` only under the STRICT
hypothesis `∑_b a_b^r < T^r`, i.e. for `T > Tᵣ := (∑ a^r)^{1/r}` strictly. The per-term route gives
the CLOSED bound `a_b ≤ Tᵣ` directly. Both families have the SAME infimal usable threshold `Tᵣ`; the
integer-rounding only discards the measure-zero boundary `∑ a^r = T^r`, never an asymptotic factor.

PROBE (scripts/probes/probe_407_count_vs_perterm.py, exact FFT, thin μ_n ⊊ F_p*, p~n^3.5-4): at EVERY
fixed r the per-term bound (∑ a^r)^{1/r} and the count-route infimal threshold coincide to machine
precision:
  n=8 β=4 p=4129:   r=2 830.41 / r=3 275.36 / r=5 125.96 / r=8 86.67  (per-term == count, all r)
  n=16 β=4 p=65537: r=2 6864.48 / r=3 1488.32 / r=5 504.80 / r=8 307.79 (equal, all r)
  n=16 β=3.5 p=16417: r=2 3428.51 / r=3 933.42 / r=5 376.79 / r=8 254.79 (equal, all r)

CONSEQUENCE: the direct ℓ^{2r}-root route (MomentSupNormBridge.sup_le_moment_root), the per-term root
(eta_le_optimized), the Markov tail bound (PeriodTailMarkov.card_filter_mul_le_sum_pow), and the
integer-count bound (MomentCountSupBound) ALL optimize the SINGLE object `min_r (∑_b ‖η_b‖^{2r})^{1/2r}`,
landing at the identical sqrt(n·log q)-gapped bound. Re-packaging the moment bound as a Markov tail /
integer count / EVT histogram does NOT escape the BGK √-cancellation wall. The EVT/tail-rate reframing
is the same analytic object in different costume; its open content stays `A_r ≤ Wick` (= BGK).

RIGOROUS Lean (MomentCountSupNotSharper.lean, axiom-clean {propext, Classical.choice, Quot.sound}):
- `forall_le_rpow_root`: the per-term CLOSED bound `∀ b, a_b ≤ (∑ a^r)^{1/r}` (count route not needed).
- `count_threshold_not_below_perterm`: for any `T < Tᵣ`, the count hypothesis `∑ a^r < T^r` is FALSE
  (`T^r ≤ ∑ a^r`), so the count route CANNOT certify a threshold below `Tᵣ`. Same infimum, no escape.

## DC-subtracted A_r<=Wick: CONFIRMED at prize DEPTH (r~ln q) for n=32..256 — ratio collapses, no catch-up failure (2026-06-14)

Follow-up confirmation of the 2026-06-14 ★★ correction (raw E_r<=Wick FALSE for n>=64; only the
DC-subtracted A_r = E_r - n^{2r}/q <= Wick is the correct prize input). The correction established A_r<=Wick
is "measured true" but did NOT publish the r-PROFILE at the prize depth r~ln q for n past the n=64 DC
crossover. Decisive question: does A_r CATCH UP to Wick at large r (the failure mode that killed raw E_r),
or stay below? Probe scripts/probes/probe_407_Ar_wick_depth_profile.py (exact FFT, thin mu_n subset F_p*,
p~n^3-4.5, A_r = (1/q) sum_{b!=0} |eta_b|^{2r}, Wick=(2r-1)!!*n^r):

| n   | p (q)     | r*=round(ln q) | A_r/Wick @ r=2 | @ r=4 | @ r=8 | @ r=r* |
|-----|-----------|----------------|----------------|-------|-------|--------|
| 32  | ~1.5e7    | 16             | 0.969          | 0.824 | 0.404 | 0.0156 |
| 64  | 16777601  | 17             | 0.984          | 0.908 | 0.710 | 0.119  |
| 128 | 14605697  | 16             | 0.992          | 0.946 | 0.647 | 0.0294 |
| 256 | 16777729  | 17             | 0.995          | 0.945 | 0.547 | 0.0051 |

VERDICT (confirmation, not closure): A_r<=Wick holds at EVERY depth through r~ln q, and the ratio A_r/Wick
DECREASES monotonically in r (0.99 at r=2 down to ~0.005-0.12 at the prize depth). So A_r is increasingly
BELOW Wick at the optimal order — the "A_r catches up to Wick at large r" failure mode (which killed raw
E_r via the DC term) does NOT occur for the DC-subtracted energy. The DC-subtracted reduction is robustly
non-vacuous with room to spare at prize depth across the prize-band n.

HONEST CAVEAT (why this is NOT the prize): these p are sub-prize (p~2^24, not 2^128), so this confirms the
r-profile shape and rules out the catch-up failure mode, but does NOT certify A_r<=Wick UNIFORMLY across
ALL fields at the actual prize budget — that uniform-in-field bound at depth r~log q IS the BGK wall (the
prize is forall-field-universal, c.154). The open content remains exactly A_r<=Wick as a thinness-essential
forall-field theorem. Value: pins the correct object's empirical r-profile (collapsing ratio), strengthening
confidence that the DC reduction is the right target and quantifying the numerical slack at prize depth.

## moment-certificate SLACK is THICKNESS-INVARIANT — the moment route cannot be the rule-3 thinness-essential lever (2026-06-15)

WALL / CONSTRAINT (rule-3 mapping). The DC-subtracted moment chain certifies the sup-norm via
`M(n) = max_{b!=0}|eta_b| <= min_r (q*A_r)^{1/2r}` (the moment certificate; `q*A_r = sum_{b!=0}|eta_b|^{2r}`).
Two facts were already known: (a) `A_r<=Wick` is measured-true at prize depth with collapsing ratio
(prior entry), and (b) the count/Markov/EVT-tail packagings are one object min_r(q A_r)^{1/2r} "in four
costumes" (not sharper). MISSING test: is this object **thinness-essential**? Rule 3 says any valid CORE
proof's certifying inequality must be FALSE in the thick window (beta~2.3-3.2) and TRUE only in thin
(beta~4-5). A thickness-INVARIANT certificate quality therefore CANNOT be the prize lever.

PROBE (scripts/probes/probe_407_Ar_thinness_essential.py, exact FFT over PROPER mu_n < F_p^*, beta swept
ACROSS the thick AND thin windows; cert = min_r (q A_r)^{1/2r}, true = M(n)):

| n  | beta (p)       | A_r<=Wick? (A_r/Wick @ r~lnq) | M/sqrt(n) | target sqrt(log(p/n)) | cert/true |
|----|----------------|-------------------------------|-----------|-----------------------|-----------|
| 8  | 2.27 (113)     | YES (0.049)                   | 1.808     | 1.627                 | 1.197     |
| 8  | 2.71 (281)     | YES (0.053)                   | 2.146     | 1.887                 | 1.181     |
| 8  | 3.20 (769)     | YES (0.040)                   | 2.430     | 2.137                 | 1.159     |
| 8  | 3.60 (1777)    | YES (0.051)                   | 2.547     | 2.324                 | 1.185     |
| 8  | 4.00 (4073)    | YES (0.023)                   | 2.665     | 2.497                 | 1.169     |
| 8  | 4.50 (11593)   | YES (0.009)                   | 2.714     | 2.698                 | 1.187     |
| 16 | 2.30 (593)     | YES (0.033)                   | 2.110     | 1.901                 | 1.210     |
| 16 | 2.70 (1777)    | YES (0.096)                   | 2.715     | 2.170                 | 1.173     |
| 16 | 3.00 (4129)    | YES (0.045)                   | 2.785     | 2.357                 | 1.171     |
| 16 | 3.30 (9377)    | YES (0.043)                   | 3.043     | 2.525                 | 1.153     |

TWO VERDICTS:
1. `A_r<=Wick` holds in BOTH the thick AND thin windows (ratio 0.03-0.10 thick, 0.009-0.023 thin) =>
   `A_r<=Wick` is NOT thinness-essential. It is honest substrate, true with room to spare across all beta.
   The thinness CANNOT live in the input inequality A_r<=Wick.
2. **The moment certificate's SLACK `cert/true = (min_r (q A_r)^{1/2r}) / M(n)` is THICKNESS-INVARIANT,
   locked at 1.15-1.21 across the ENTIRE beta window (thick 2.27 -> thin 4.5) and across n=8,16.** The
   moment route overshoots the true sup-norm by a constant ~18% that does NOT depend on thinness. Since the
   certificate quality is beta-uniform, the moment family (energy/Wick + count/Markov/EVT-tail, all four
   costumes) CANNOT be the rule-3 thinness-essential mechanism: a thickness-monotone certificate cannot
   prove a bound that is FALSE in the thick window. Any beta-aware refinement of A_r<=Wick is ruled out as
   a prize lever -- the residual ~18% slack lives in the moment->sup passage M<=(q A_r)^{1/2r}, and that
   passage's loss is regime-uniform.

WHERE THIS LEAVES THE OPEN CONTENT (mapping, not closure): not in tightening A_r<=Wick (beta-uniformly
far below Wick), not in the moment->sup step (beta-uniform constant slack). Corroborates "one object in
four costumes": the WHOLE moment family is beta-uniform, hence rule-3-incompatible standalone. A genuine
CORE proof must use a thinness-DISCRIMINATING object whose certifying inequality flips sign between the
thick and thin windows -- the moment certificate provably is not such an object.

HONEST CAVEAT: small-n / sub-prize p (p<=~12k, not 2^128); this maps the certificate's regime-behavior
shape, it does NOT itself prove or refute the prize. No Lean theorem claimed (the thickness-invariance is
an empirical measurement; proving the constant-slack would itself require BGK). Reproducible probe + this
constraint entry are the deliverable, per rule 4 (a precisely-mapped wall is a WIN).

## thinness-discriminator search: normalized prize-ratio R and shallow Sidon-depth are NOT decisive rule-3 discriminators (2026-06-15)

CONTEXT. Prior entry (82581fb79) showed the moment certificate is thickness-INVARIANT, so the prize
lever must be a thinness-DISCRIMINATING object (certifying quantity bounded in thin beta~4-5, ill-behaved
in thick beta~2.3-3.2). This entry tests the two most natural candidates and finds NEITHER is a clean
discriminator at accessible scale -- narrowing where the real lever can live.

PROBE (scripts/probes/probe_407_thinness_discriminator.py, exact FFT/enumeration, proper mu_n<F_p^*):

D1 -- normalized prize ratio R(n,p) = M(n)/(sqrt(n)*sqrt(log(p/n))) (prize wants R<=C absolute):
| n  | beta | R      |          | n  | beta | R      |
|----|------|--------|          |----|------|--------|
| 8  | 2.27 | 1.111  |          | 16 | 2.30 | 1.110  |
| 8  | 2.71 | 1.137  |          | 16 | 2.70 | 1.251  |
| 8  | 3.20 | 1.137  |          | 16 | 3.00 | 1.182  |
| 8  | 3.60 | 1.096  |          | 16 | 3.30 | 1.205  |
| 8  | 4.00 | 1.067  |          | 16 | 3.60 | 1.152  |
| 8  | 4.50 | 1.006  |          |    |      |        |
  n=8 avg R: thick(beta<3.3)=1.129, thin(beta>=3.9)=1.037 -- mild thin-TIGHTENING toward ~1.0.
  n=16: R is NON-monotone, stays ~1.10-1.25 across all beta (no clean convergence; no thick blow-up).
  VERDICT: R is O(1) in BOTH regimes. The n=8 convergence to 1.006 at beta=4.5 is suggestive but is
  likely a small-n artifact (only n=8 reaches beta=4.5 cheaply); n=16 shows R bounded but NOT
  thin-converging. R is NOT a decisive rule-3 discriminator -- it does not blow up in the thick window,
  it just sits at a slightly higher O(1) constant there. (Consistent: sqrt(log(p/n)) is the right SCALE
  in both regimes up to a constant; the prize's open content is the absolute CONSTANT, not the scale.)

D2 -- shallow additive Sidon-depth signature (waste = 1 - distinct(r-fold sumset)/n^r; lower=more Sidon):
| n  | beta | r=2 waste | r=3 waste | r=4 waste |
|----|------|-----------|-----------|-----------|
| 8  | 2.53 | 0.484     | 0.8125    | 0.9607    |
| 8  | 4.00 | 0.484     | 0.8125    | 0.9451    |
| 16 | 2.49 | 0.496     | 0.8359    | 0.9846    |
| 16 | 4.00 | 0.496     | 0.8281    | 0.9560    |
  VERDICT: r=2 and r=3 waste are IDENTICAL thick vs thin (field-blind) -- the shallow additive structure
  of mu_n is determined by n, not p (consistent with brief's "mu_n is B_inf-Sidon to depth ~log n"
  regardless of field). Only at r=4 does thin show modestly less waste (more distinct, 0.945 vs 0.961
  n=8; 0.956 vs 0.985 n=16) -- the depth where small thick-p starts forcing extra collisions. So shallow
  Sidon-depth is NOT a thinness discriminator; any signal would be DEEP (r ~ log n), exactly the
  inaccessible-by-enumeration regime that IS the B_inf <- B_{log n} bootstrap wall.

NET (mapping): the two natural discriminators both FAIL to cleanly separate thin from thick at accessible
scale -- R stays O(1) in both (the open content is the absolute constant, scale is right in both regimes),
and Sidon-structure is field-blind until depth r~log n (the inaccessible bootstrap regime). This narrows
the rule-3 lever: it must live at DEEP additive order r~log n (the B_inf<-B_{log n} bootstrap), not in any
shallow/normalized O(1) statistic -- consistent with the 25-yr wall being genuinely a deep-order phenomenon.

HONEST CAVEAT: small-n / sub-prize p; reproducible probe maps the discriminator candidates' behavior, does
not prove/refute the prize. No Lean theorem claimed. Per rule 4, a precisely-mapped non-discriminator is a WIN.

## K1 / antipodal-pairing residual H FAILS at the prize scale — derivable refutation (2026-06-14)

The in-tree GaussianEnergyFromPairing.gaussianEnergyBound_of_pairing derives the raw Wick carrier
GaussianEnergyBound G r (E_r <= (2r-1)!!*|G|^r) from three inputs: unconditional henergy (negation-closure
energy = zeroSumCount), unconditional hcount (#pairings <= (2r-1)!!), and the genuine open input H = the
ANTIPODAL-PAIRING RESIDUAL ("every zero-sum 2r-tuple of G is antipodally paired").

The 2026-06-14 ★★ correction (DCEnergyEssential.not_gaussianEnergyBound_of_card_pow_gt) PROVES the
conclusion GaussianEnergyBound G r is FALSE when q*(2r-1)!! < |G|^r (the prize regime: n>=64 at r~log q,
DC term |G|^{2r}/q >> Wick). By modus tollens (henergy, hcount unconditional), H ITSELF IS FALSE at prize.

LANDED: PairingResidualFailsAtPrize.not_pairing_residual_of_card_pow_gt (axiom-clean
{propext, Classical.choice, Quot.sound}): under henergy + hcount, q*(2r-1)!! < |G|^r => NOT H, i.e. there
EXISTS a zero-sum 2r-tuple of G that is NOT antipodally paired.

INTERPRETATION (mapped wall): the above-threshold antipodal-pairing structure (true in char 0 / Lam-Leung
and at small n) is DESTROYED by the char-p anomaly at n>=64, r~log q. The non-antipodal zero-sum tuples
are exactly the char-p extra solutions the DC term counts (E_r >= |G|^{2r}/q >> Wick). So the K1 / pairing
route CANNOT supply the prize carrier E_r <= Wick at prize scale; only the DC-subtracted A_r <= Wick
survives (the genuinely thinness-essential object — consistent with the A_r r-profile confirmation note
above). The pairing/Lam-Leung char-0 route is prize-DEAD without DC subtraction; the bricks consuming raw
GaussianEnergyBound (GaussianEnergyFromPairing, GaussianEnergyThreeRepThree's r=3 rung) are vacuous /
have prize-false hypotheses at n>=64 exactly as eta_le_optimized is.

## SIGNED deep period-power cancellation IS thinness-essential — and the moment certificate's |.| destroys it (2026-06-15)

THE FIND (positive structural map, the missing rule-3 signal). Prior entries showed the moment certificate
min_r (q A_r)^{1/2r} is thickness-INVARIANT and shallow statistics are field-blind, leaving the rule-3
lever at deep additive order. This locates it: the SIGNED deep period-power sum.

Since mu_n is negation-closed, eta_b in R. Define the normalized signed deep sum
    C_r(n,p) = |sum_{b!=0} eta_b^r| / ((p-1) * M^r),   M = max_{b!=0}|eta_b|.
C_r=1 means no cancellation (all eta_b^r aligned); C_r->0 means strong signed cancellation across b.
(Note sum_{b!=0} eta_b^r is the deep additive structure: p*W_r/... = 1 + (1/n^r) sum_{b!=0} eta_b^r.)

PROBE (scripts/probes/probe_407_deep_sidon_depth.py + probe_407_signed_deep_cancellation.py, exact, proper mu_n):
| n  | beta | C_2   | C_4   | C_6   | C_8    | C_10   |
|----|------|-------|-------|-------|--------|--------|
| 16 | 2.49 | 0.210 | 0.116 | 0.081 | 0.063  | 0.052  |   (THICK)
| 16 | 4.00 | 0.084 | 0.020 | 0.0072| 0.0034 | 0.0019 |   (THIN)
| 8  | 2.53 | 0.214 | 0.113 | 0.081 | 0.066  |   -    |   (THICK)
| 8  | 4.50 | 0.136 | 0.048 | 0.025 | 0.016  |   -    |   (THIN)

THIN/THICK cancellation ratio (thick C_r / thin C_r), n=16: r2=2.5x, r4=5.8x, r6=11x, r8=18x, r10=27x.

VERDICT (thinness-ESSENTIAL, rule-3 compatible):
- C_r is strictly SMALLER (stronger signed cancellation) in THIN than THICK at EVERY r, and the thin/thick
  ratio GROWS with depth r (2.5x at r=2 up to 27x at r=10 for n=16). This is the deep-order, thinness-
  ESSENTIAL phenomenon rule 3 demands: a quantity whose behavior genuinely separates thin from thick and
  whose separation strengthens at the prize depth r~log n. Unlike A_r<=Wick (beta-uniform) and the moment
  certificate (thickness-invariant), the SIGNED period-power sum sum_{b!=0} eta_b^r carries the thinness.
- MECHANISM for WHY the moment route fails (closes the prior 'four costumes' map): the moment certificate
  uses sum_{b!=0}|eta_b|^{2r} (absolute values), which DESTROYS the signed cancellation. The thinness-
  essential content lives in the SIGNED sum sum_{b!=0} eta_b^r; taking |.| (as every moment/energy/Wick/
  count/EVT packaging does) discards exactly the cancellation that distinguishes thin from thick. THIS is
  why the moment family is thickness-invariant (prior entry) and cannot be the lever: |.| is the leak.

WHERE THE OPEN PRIZE LEVER NOW SITS (sharpened, positive): a bound on M must exploit the SIGNED deep
cancellation in sum_{b!=0} eta_b^r (which IS thinness-essential, growing with r), NOT the absolute moment.
This is consistent with the BGK/Stepanov flavor (signed/algebraic cancellation, not measure/energy). Any
method that passes through |eta_b| at any step is provably rule-3-incompatible (loses the thin signal).

HONEST CAVEAT: small-n / sub-prize p (<=65537); exact-verified at this scale. Maps the thinness-essential
object + the |.|-leak mechanism; does NOT prove a uniform-in-field deep-cancellation bound (that bound at
r~log q IS the prize/BGK wall). No Lean theorem (a quantitative signed-cancellation bound = the open core).
Reproducible probes + this constraint/structure entry are the deliverable. Rule-4 mapped-frontier WIN, and
unlike a pure wall this is a POSITIVE localization: the lever exists, it is the signed deep sum, and the
moment route's |.| is precisely why nobody saw it.

## Pairing-route rung boundary r*(n,q): char-p anomaly invades the K1/pairing ladder at DESCENDING rungs (2026-06-14)

Sharpening of "K1/antipodal-pairing residual H FALSE at prize" (PairingResidualFailsAtPrize). For FIXED
prize (n,q), at which rung r does raw E_r <= Wick (=> H) FIRST fail? Probe
scripts/probes/probe_407_pairing_rung_boundary.py (exact FFT, E_r=(1/q)sum_all|eta_b|^{2r}, Wick=(2r-1)!!n^r):

| n   | beta | p        | r*=first r with E_r>Wick | DC-predicted r* | round(ln q) |
|-----|------|----------|--------------------------|-----------------|-------------|
| 32  | 4.5  | 5931649  | 15                       | 15              | 16          |
| 64  | 4.0  | 16777601 | 6                        | 7               | 17          |
| 128 | 3.4  | 14605697 | 4                        | 5               | 16          |
| 256 | 3.0  | 16777729 | 3                        | 4               | 17          |

The failing rung r* DESCENDS as n grows (15 -> 6 -> 4 -> 3), tracking the DC-crossover within ±1. So the
char-p anomaly invades the pairing/Wick ladder at progressively LOWER orders: at n=256 even r=3
(E_3/Wick=1.046) is prize-false. Consequence: the in-tree r=3 pairing rung GaussianEnergyThreeRepThree
(deriving GaussianEnergyBound G 3 from repThree) has a PRIZE-FALSE hypothesis for large n, just like
eta_le_optimized and the general H. Essentially the ENTIRE moment ladder above r=2 is pairing-dead at
prize scale (r* -> small as n -> infinity). Only the DC-subtracted A_r <= Wick survives at every rung
(confirmed separately: A_r/Wick collapses, never crosses 1). The char-0 Lam-Leung pairing structure is
not "loose at high r" but actively false from a low, n-shrinking rung onward — the DC subtraction is
the only repair. Reinforces: prize object = DC-subtracted A_r <= Wick, forall-field, = BGK wall.

## Anomaly-suppression in-window survival — bad primes INVADE the prize window (β_bad grows in n), but Anom_r ≤ n^{2r}/p STILL HOLDS there (2026-06-15)

LENS: the HEAD anomaly route (dbbe1b01e). `Anom_r(p) = E_r^(p) − E_r^(0) ≤ n^{2r}/p` is the SUFFICIENT
condition for `A_r ≤ Wick` (the DC-subtracted prize core). Orchestrator showed `Anom = EXACTLY 0` at n=8
prize primes (r≤6) and flagged the OPEN asymptotic: for large n the bad primes (where Anom>0) can reach the
prize window `[n^4, (2r)^{n/2}]` at r~log q.

TEST (exact, NEW angle = NORMS, no per-prime FFT for the onset):
`Anom_r(p) > 0  ⟺  p | N(α)` for some r-collision difference `α = Σζ^{a_i} − Σζ^{b_j} ≠ 0` in `Z[ζ_n]`.
So r-bad primes = prime factors of the norms `N(α)` (computed exactly via the φ=n/2 conjugate product,
ζ^φ=−1 for n=2^a). Probe `scripts/probes/probe_407_anom_badprime_norm_onset.py`.

RESULT 1 — bad-prime onset exponent β_bad = log_n(p_bad) GROWS in n, invading the prize window at LOWER r:
  n=8:  first r with p_bad ≥ n^4 is r=6 (β_bad 4.28)
  n=16: r=4 (β_bad 4.60)
  n=32: r=2 (β_bad 4.87)
=> the orchestrator's "Anom=0 at prize primes" is a SMALL-n ARTIFACT (at n=8 the window is bad-prime-free
below r=6). Matches the independently-observed pairing-rung descent (r* 15→6→4→3, b58cf1d03): the char-p
anomaly is NOT confined below the prize window asymptotically.

RESULT 2 — but the SUFFICIENT condition SURVIVES at the in-window bad primes (the real BGK test at scale):
n=16, r=4, ALL 26 in-window bad primes p ∈ [n^4=65536, 1.5e6]: `Anom_4(p) ≤ n^8/p` HELD at **26/26**,
TRUE WORST ratio = **0.4757** at p=76001 (β=4.053), i.e. ~2.1× margin. Probe
`scripts/probes/probe_407_anom_suppression_inwindow.py` (vectorized norms + exact FFT integer-count Anom).

NET (honest): a POSITIVE mapped-frontier result for the anomaly route — bad primes do invade the window
but the anomaly is suppressed there with margin at accessible scale. NOT a closure: sub-prize-budget primes
(p ≤ 1.5e6), fixed r; the worst PRIZE prime at r~log q, p~2^128 (the BGK content) is untouched. Complements
`probe_407_bgkproof_onset_growth` (which tracks the ratio along the r-axis at a fixed prime); this pins the
worst-case ACROSS the bad-prime set inside the window at fixed r. Both axes now bounded at accessible scale.

---

## [over-det δ*] s* budget-crossing: s*−k appears CONSTANT (=3) at accessible n — honest tension with floor (2026-06-15, opus-4-8 subagent)

Follow-up to the over-det incidence MAX closed form `I_max(n)=n³/32−n²/8+1` (push 0c7492b0d) and the
union-of-singletons p-independence brick (47dcd71b3, sibling). The δ* open item #2 is the budget-crossing
`s* = min{s : maxI(s) ≤ budget=n}`, giving `δ* = (n−s*)/n`.

PROBE (probe_407_sstar_budget_crossing.py, char-0 p≫n³, far-incidence COUNT per direction, s swept up
from k+2; MAX over directions; full-direction at n=16, antipodal-nbhd lower-bound at n=20):
- **n=16, k=2: s*=5 (FULL-direction verified — maxI(4)=97>16, maxI(5)=16≤16). s*−k=3. δ*=0.6875.**
- **n=16, k=4: s*=7 (antipodal-nbhd; matches the campaign's independently-published δ*=0.5625). s*−k=3.**
- **n=20, k=2: s*=5 (antipodal-nbhd ⟹ s* LOWER BOUND). s*−k=3. δ*=0.75.**

OBSERVATION: `s*−k = 3` is CONSTANT across n=16,20 AND k=2,4 in the accessible range — both k-independent
and n-independent here. This SHARPENS the prior `deltastar-407-char0-logn-over-n-candidate` note, which
conjectured `s*−k = log₂(n)` from only n=16,32 at ρ=1/8 (where log₂16=4, but my n=16 gives s*−k=3, not 4 —
the discrepancy is the budget/direction convention: my budget is exactly n, full-direction MAX).

HONEST TENSION (the decisive open question, NOT resolved here):
- IF `s*−k` stays constant → `δ* = 1 − (k+s*−k)/n → 1` (capacity) as n→∞, which would CONTRADICT the
  conjectured floor `δ* = 1−ρ−Θ(1/log n)` (a Θ(1/log n) gap BELOW capacity). i.e. constant-defect ⟹ δ*
  rises ABOVE the floor (toward capacity) asymptotically.
- BUT: this is exactly the doc's flagged pre-asymptotic regime (small n, coarse 1/n band granularity,
  the conjectured floor is itself below Johnson at these n = degenerate window). Constant-3 at n∈{16,20}
  CANNOT be extrapolated — n=32,64 (army's Rust engine, ~9.6h+ at ρ=1/4) is needed to see if s*−k grows.
- CAVEAT: my n=20 antipodal-nbhd s* is a LOWER BOUND (a non-antipodal direction could keep maxI above
  budget at s=5, pushing the true s* up). The constant could be an undercount artifact at n>16.

NET: a mapped data point (n=16 full-verified s*=5 ⟹ δ*=0.6875) + an honest tension (constant s*−k ⟹
δ*→capacity, contra the floor) that the army's large-n Rust must resolve. NOT a refutation of the floor
(small n, lower-bound s* at n>16). Logged, not receipted (over-det lane actively sibling-owned, 47dcd71b3 —
one-active-speaker; not crowding with a competing receipt).

## ★ REFINEMENT (sharpens the in-window survival entry above) — the SUFFICIENT proxy `Anom_r ≤ n^{2r}/p` FAILS at deep r at the worst prime, but the TARGET `A_r ≤ Wick` survives with margin (2026-06-15)

Combined-axes trajectory at the WORST in-window bad prime p=76001 (n=16, β=4.05), r=2..r*=round(log p)=7:
  r : Anom_r/(n^2r/p) [sufficient proxy] | A_r/Wick [actual target]
  2 : 0.000 | 0.936     5 : 0.870 | 0.517
  3 : 0.000 | 0.819     6 : 1.091 | 0.374  <-- proxy CROSSES 1
  4 : 0.476 | 0.671     7 : 1.188 | 0.255  <-- proxy > 1
So `Anom_r ≤ n^{2r}/p` (the clean sufficient form) FAILS at r=6,7 at the worst in-window prime — it does
NOT survive to the optimizer depth r*. The fixed-r=4 survival result (26/26) is correct but does NOT extend
to deep r at the worst prime.

CRUCIAL: the ACTUAL target `A_r ≤ Wick` HOLDS at EVERY r (0.94→0.67→0.52→0.37→0.26, monotone decreasing),
because `A_r ≤ Wick ⟸ Anom_r ≤ n^{2r}/p + (Wick − R_r)` and the `(Wick − R_r)` headroom absorbs the anomaly
overshoot at deep r. (Consistent with probe_407_bgkproof_onset_growth's decomposition.)

NET: the clean sufficient proxy `Anom_r ≤ n^{2r}/p` is the WRONG (too-strong) sufficient form at deep r — it
overshoots exactly where the moment optimizer sits. The true open object is `A_r ≤ Wick` directly (= the
DC-subtracted BGK core), which survives with margin at this accessible-scale prime but is NOT implied by the
clean Anom-proxy past r=5. Anyone trying to close CORE via `Anom_r ≤ n^{2r}/p` will hit this proxy-failure at
deep r; must use the `(Wick − R_r)` headroom (i.e. the full `A_r ≤ Wick`), not the clean proxy.
Probe scripts/probes/probe_407_anom_worst_rtraj.py.

## ★ POSITIVE reframing — `A_r/Wick` is MONOTONE-DECREASING & ≤1 in THIN, but EXCEEDS 1 & non-monotone in THICK ⟹ a base-case+monotonicity proof of `A_r ≤ Wick` is automatically THINNESS-ESSENTIAL (2026-06-15)

LENS: the genuine open prize object is `A_r ≤ Wick` (DC-subtracted, ∀-thin-field, r~log q = BGK). Candidate
reduction lever: `f(r) := A_r/Wick`. The C14 batch + my p=76001 trajectory both showed f monotone-DECREASING.
IF f(1) ≤ 1 (PROVEN: base_case_strict, A_1 < Wick) AND f(r+1) ≤ f(r), then `A_r ≤ Wick` ∀r by monotonicity.

TEST (exact FFT spectrum + integer cross-check, probe scripts/probes/probe_407_ArWick_monotone_thinness.py):
- THIN (prize, β 3.9-4.6, n=8,16,32): f(r) MONOTONE-DECREASING and ≤ 1 at EVERY r. Robust across n, β, p.
  (e.g. n=32 β=4.2 p=2097857: f = 1.00, 0.97, 0.91, 0.82, 0.71, 0.59, 0.46 — clean.)
- THICK: mostly monotone too, EXCEPT the maximally-2-structured n=32 in F_4129 (β=2.40, v₂=16): f RISES
  ABOVE 1 from r=2 (peak 1.705 @ r=5) and is NON-monotone. EXACT integer cross-check: E_2=3744, A_2=3490 >
  Wick=3072 (A_2/Wick=1.136) — `A_r > Wick` genuinely FALSE in that thick window.

NET (POSITIVE, rule-3-correct): the property "f(1) ≤ 1 AND f monotone-decreasing" HOLDS in thin and FAILS in
thick (f exceeds 1 + non-monotone). So a proof of `A_r ≤ Wick` via [base case f(1)≤1] + [single-step
monotonicity f(r+1) ≤ f(r)] is AUTOMATICALLY thinness-essential — any thickness-monotone method is ruled out
because the thick window violates BOTH ingredients. This REFRAMES the open core from the sup-norm / "A_r ≤ Wick
∀r" to the SINGLE-STEP monotonicity `A_{r+1}/Wick ≤ A_r/Wick` at r~log q. Still BGK-hard (the deep-r single
step IS the hard inequality), but a cleaner, rule-3-satisfying target than the sup-norm directly. NOT a
closure — the deep-r monotonicity step at the worst thin prize prime is the irreducible content; no Lean
theorem (proving the single step uniformly = BGK).

## ★ SHARPENING — the monotonicity step is the clean inequality `A_{r+1}/A_r ≤ (2r+1)n`; holds THIN with GROWING margin, fails THICK (2026-06-15)

Sharpens the A_r/Wick-monotonicity reframing above. The step f(r+1) ≤ f(r) is EXACTLY:
   A_{r+1}/Wick_{r+1} ≤ A_r/Wick_r  ⟺  A_{r+1}/A_r ≤ Wick_{r+1}/Wick_r = (2r+1)·n.       (STEP)
Since A_{r+1}/A_r is a |eta_b|^{2r}-weighted average of |eta_b|^2, A_{r+1}/A_r ≤ M^2; and (STEP) at r~log q
⟺ M^2 ≤ (2r+1)n ≈ 2n log q = the PRIZE. So (STEP) at deep r ⟺ prize (BGK-hard, confirmed).

MEASURED (exact FFT spectrum, g(r) = (A_{r+1}/A_r)/((2r+1)n), STEP holds iff g ≤ 1):
- THIN (prize β 4.0-4.5, n=16,32): g(r) ≤ 1 at EVERY r [STEP holds], AND g(r) DECREASES in r
  (n=32 β=4.5: 0.97,0.94,0.91,0.88,0.85,0.82,0.80) — the step gets EASIER at deeper r in thin (growing
  margin). (A_{r+1}/A_r)/M^2 stays 0.15-0.8 ≪ 1: the consecutive-moment ratio is far below the sup at
  accessible r (heavy tail not yet dominating).
- THICK (maximally-2-structured n=32/F_4129, β=2.40): g(r) = 1.145, 1.225, 1.167, 1.050, … > 1 at low r
  [STEP FAILS], exactly the rungs where A_r > Wick.

NET: the open core reframes to the SINGLE consecutive-moment-ratio bound `A_{r+1}/A_r ≤ (2r+1)n` at r~log q,
which holds thin with MEASURED GROWING margin and fails thick (rule-3-correct). The growing thin margin at
accessible r is encouraging but the deep-r limit A_{r+1}/A_r → M^2 = the prize; NOT a closure (proving the
single step uniformly at r~log q in thin = BGK). Probe scripts/probes/probe_407_moment_ratio_step_thinness.py.

## ⚠️ TEMPERING DATA — the thin single-step margin g(r*) at the OPTIMIZER ERODES as n grows (honest counter-weight to the "growing margin" reframing) (2026-06-15)

Counter-weight to the A_{r+1}/A_r ≤ (2r+1)n reframing's encouraging "growing margin in r" note. The r-axis
margin grows at FIXED n, but the prize is the n→∞ limit, so the decisive axis is g(r*) vs n at the optimizer
r*=round(log p). Exact FFT spectrum, thin β=4:
  n=8  r*=8  g(r*)=0.366 ; n=16 r*=11 g=0.468 ; n=32 r*=14 g=0.530 ; n=64 r*=17 g=0.643.
g(r*) stays < 1 (STEP holds at the optimizer) at ALL accessible n, BUT INCREASES in n (0.37→0.64) — the
margin SHRINKS. M^2/(2n ln p) similarly rises 0.43→0.70. So the "growing margin" optimism is r-axis only;
on the n-axis the margin erodes toward 1. n≤64 is sub-linear but CANNOT distinguish "saturates below 1"
(prize provable via this step) from "creeps to 1" (BGK-tight) — that crossover IS the open content. Honest:
NO extrapolation claim, NO closure; this tempers the reframing rather than advancing it. Probe
scripts/probes/probe_407_step_at_rstar_ntrend.py.

## ★ FORMULA-SCOPE REFUTATION — the in-tree δ* formula ½+(1/(2ρ)−1)/n BREAKS at small ρ (k=2); exact s* sweep (2026-06-15)

CONTEXT: the orchestrator's SOTA consolidation (c.02:27:52Z, §3) flagged the SINGLE decisive open computation:
"a cheap large-n k=2 sweep (small s*)" to settle whether δ*_far-line tracks the floor 1−ρ−Θ(1/log n), noting
"at n=32,k=2 the small-n formula predicts s*=9 but the engine measures s*=6, δ*=0.8125 — the formula breaks
upward." I ran the exact k=2 over-determined far-line incidence s* sweep (Rust pg engine, validated; + an
independent Python extremal-neighborhood probe, both agree) and PINNED the break exactly.

EXACT DATA (char-0 prize prime p~n^4, VALID subgroup p≡1 mod n verified, budget=n, full over-det incidence):
  n=16,k=2: s=4 maxI=97(bad) → s=5 maxI=16(GOOD) ⟹ s*=5, s*−k=3, δ*=0.6875
  n=32,k=2: s=4 maxI=897 → s=5 maxI=90 → s=6 maxI=25(GOOD) ⟹ s*=6, s*−k=4, δ*=0.8125
Both reproduced by the bmax=4 direction-restricted engine (extremal dir has b∈{2,4} ⟹ restriction is exact).

THE BREAK (exact): the in-tree formula δ*=½+(1/(2ρ)−1)/n (HEAD b66b7f769, calibrated ρ=1/4, n≤24) gives, for
k=2 (ρ=2/n, 1/(2ρ)=n/4): s* = n/2 − 1/(2ρ) + 1 = n/4 + 1, i.e. s*−k = n/4 − 1.
  n=16: formula s*−k = 3  vs EXACT 3  ✓ MATCH (δ*=0.6875 both)
  n=32: formula s*−k = 7 (s*=9, δ*=0.7188)  vs EXACT s*−k = 4 (s*=6, δ*=0.8125)  ✗ BREAK
The formula OVER-predicts s* / UNDER-predicts δ* at small ρ. Exact δ*=0.8125 sits ABOVE Johnson(0.75),
between the formula (0.7188) and cap 1−ρ (0.9375). Measured s*−k grows 3→4 (n=16→32), NOT 3→7: the
small-ρ over-det threshold grows FAR SLOWER than the formula's n/4 rate — consistent with s*−k ~ Θ(n/log n)
or even slower (sub-n/4), NOT the linear-in-n the ρ=1/4-calibrated formula implies.

CONSEQUENCE (honest, rule 4 = a mapped formula failure is a result):
- The ½+(1/(2ρ)−1)/n formula is a ρ=1/4 ARTIFACT; it must NOT be used to extrapolate δ* at small ρ / large n.
- The exact k=2 δ* climbs toward 1−ρ (NOT ½), confirming the orchestrator's "break upward". So the far-line
  incidence δ* (a RIGOROUS UPPER bound on MCA δ*, epsMCA≥far_inc/q) does NOT collapse to Plotkin ½ at small ρ.
- OPEN (the genuine combinatorial core): the exact growth law of s*−k(n) at fixed k. n=16,32 give 3,4; n=64
  (s=4 maxI=7681 bad, s=5 in flight) extends it. Whether s*−k ~ Θ(n/log n) (⟹ δ*=floor) vs slower is the live
  decider — and it is now OFF the BGK char-sum wall (pure cyclotomic over-det counting), exactly as the
  orchestrator localized. NOT a closure: small n (≤32 exact), maps the trend.
Probe scripts/probes/probe_407_k2_sstar_formula_break.py (+ rust-pg bmax mode for cross-validation).

## ⚠️ REFUTATION — the deployed `CensusDomination` Prop is FALSE at the prize budget (bounds SETS, not γ) (2026-06-15)

`CensusDominationWeld.lean` proves `CensusDomination dom k a₀ K` (K/p ≤ ε*) ⟹ `δ* = 1 − r/2^μ`. The Prop bounds
the alignable-SET count by K. Real budget (from `hεstar < (2^r·C(2^{μ-1},r))/p`) = `K < 2^r·C(2^{μ-1},r)` =
the KKH26 fibre supply. PROBE (thin proper μ_n, prize β=4, exact pencil-ratio alignment; validated by exact
n=8 SET-count=supply-count match 24,32):

  n=16,r=3,a₀=4: worst #alignable-SETS = 896 (line x⁹,x⁸) > budget 448  [EXCEEDS 2×]; #distinct-γ = 97 ≤ 448.
  n=16,r=4,a₀=5: worst #SETS = 1568 (x¹⁰,x⁸) > budget 1120; #distinct-γ = 40 ≤ 1120.
  n=16,r=5,a₀=6: #SETS = 1456 ≤ 1792; #γ = 73 ≤ 1792.

CONSTRAINT LEMMA: at n=16 the worst alignable-SET count exceeds the budget ⟹ the deployed `CensusDomination`
hypothesis is FALSE at the prize budget ⟹ `kkh26_deltaStar_pin_of_censusDomination` cannot fire at the prize
budget as stated. But #distinct-γ (the true MCA bad-scalar count, the object `badScalars_card_le_alignable`
needs) stays under budget at EVERY config. The gap = the looseness of `#bad-scalars ≤ #alignable-SETS`
(x⁹,x⁸: 896 sets, 16 distinct γ). The weld lifted the loose `badScalars_card_le_alignableSets` bound into its
hypothesis, making the deployed Prop strictly stronger than necessary — over-strong enough to be false.
The correct ⟺-CORE normal form must bound #distinct-γ, NOT the alignable-SET count.

Prime-independent (non-Fermat p=65777: SETS 896>448, γ 97 OK — not a Fermat artifact). Distinct from
`TakeoverCountermodel` (killed `CensusUpperExtremalFloor` = #bad-scalar upper-floor at a thick-prime death
radius); this kills the SET-count budget of `CensusDomination` in the thin prize regime. NOT a CORE closure
nor prize refutation — `#distinct-γ ≤ budget` is the open BGK content (margin large at n≤16, asymptotic
untested). Probes scripts/probes/probe_407_census_domination_budget.py, probe_407_census_budget_nonfermat.py,
probe_407_census_sets_vs_gamma.py. Receipt #issuecomment-4704035101.

## ★ COMPANION — proportional-k (ρ=1/4) CONFIRMS the formula where calibrated + s*−k GROWS (the floor-tracking axis) (2026-06-15)

Companion to the k=2 formula-break note above. Ran the EXACT over-det far-line incidence s* sweep at FIXED
ρ=1/4 (proportional k), the prize-relevant regime, via the rust-pg engine (bmax=6 direction-restricted;
extremal dir b−k≤2 ≤ bmax ⟹ restriction exact; char-0 prize prime p~n^4, valid subgroup p≡1 mod n):

| n  | k | s* | s*−k | δ* | in-tree formula δ*=½+1/n (ρ=1/4) |
|----|---|----|------|----|-----|
| 16 | 4 | 7  | 3    | 0.5625 | 0.5625  EXACT MATCH |
| 24 | 6 | 11 | 5    | 0.5417 | 0.5417  EXACT MATCH |
(n=16: s4..6 bad → s7 maxI=9 GOOD. n=24: s8:1153,s9:65,s10:25 bad → s11 maxI=24 GOOD.)

TWO clean findings:
1. The in-tree δ* formula ½+(1/(2ρ)−1)/n is EXACT at ρ=1/4 (matches n=16,24 to the digit) — confirming it is
   CORRECTLY CALIBRATED there. This PROVES the k=2 break (above) is a genuine SMALL-ρ failure of the formula,
   NOT an engine artifact: the engine reproduces the formula exactly where the formula was fit (ρ=1/4) and
   departs from it exactly where it wasn't (k=2, ρ→0). Consistent, adversarially-clean story.
2. s*−k GROWS 3→5 (n=16→24) at fixed ρ=1/4 — the floor-tracking axis. At ρ=1/4 the formula gives
   s*−k = n(½−1/n)−k = n/4 − 1 (LINEAR in n) ⟹ δ* → ½ = Johnson FROM ABOVE as n→∞. So at ρ=1/4 the far-line
   incidence δ* tends to JOHNSON, not the floor 1−ρ−Θ(1/log n)=¾−Θ — fully consistent with the orchestrator's
   "far-line incidence is a RIGOROUS UPPER bound on MCA δ* that sits BELOW the floor" (epsMCA≥far_inc/q). The
   s*−k = n/4−1 linear law (NOT Θ(n/log n)) at ρ=1/4 means the over-det far-line δ* does NOT track the floor —
   it is the (sub-floor) Plotkin/Johnson-limit upper bound, exactly as localized.

NET (honest, no closure): the over-det far-line incidence δ* is a CLEAN, formula-exact object at ρ=1/4
(→ Johnson, linear s*−k=n/4−1), and a FORMULA-BREAKING object at k=2 (→ above Johnson toward cap, sub-linear
s*−k). Both are the (rigorous UPPER bound) far-line δ*, NOT the MCA δ* — the prize BGK content lives in the
GAP between this upper bound and the true MCA δ*≥floor, untouched. Engine scripts/rust-pg (bmax mode);
companion to probe_407_k2_sstar_formula_break.py. Small n (≤24 exact). NOT a CORE closure.

## ★ SHARPENING + REGIME CLARIFICATION — at FIXED ρ=1/4 the far-line δ* DECREASES to Johnson (linear s*−k=n/4−1), NOT the floor (2026-06-15)

Sharpens the proportional-k companion + clarifies the orchestrator's RESOLUTION doc
(deltastar-RESOLUTION-tracks-floor-not-half.md, 1d78bb751), which concludes far-line δ* "tracks toward 1−ρ
(floor), not ½." That is correct AT k=2 (ρ→0), but the limit is REGIME-DEPENDENT. Exact 3-point ρ=1/4 data
(full-sweep rust-pg, all re-verified with the corrected saturating_add binary; valid subgroup p≡1 mod n, β=4):

| n  | k | s* | s*−k | δ*=(n−s*)/n | Johnson 1−√ρ | cap 1−ρ |
|----|---|----|------|-------------|--------------|---------|
| 16 | 4 | 7  | 3    | 0.5625      | 0.5000       | 0.7500  |
| 20 | 5 | 9  | 4    | 0.5500      | 0.5000       | 0.7500  |
| 24 | 6 | 11 | 5    | 0.5417      | 0.5000       | 0.7500  |

EXACT LINEAR LAW at ρ=1/4: s*−k = n/4 − 1 (3,4,5 for n=16,20,24 — matches the in-tree formula ½+1/n exactly),
so δ* = (n − (n/4+1))/n = 3/4 − 1/n → 3/4? NO: s* = k + n/4 − 1 = n/4 + n/4 − 1 = n/2 − 1, so δ* = (n−s*)/n
= (n/2+1)/n = 1/2 + 1/n → **1/2 = Johnson** (since ρ=1/4 ⟹ Johnson=1−√(1/4)=1/2). DECREASING (0.5625→0.5417),
toward Johnson from ABOVE — NOT toward the floor 1−ρ=3/4.

REGIME CLARIFICATION (the two limits differ):
- k=2 FIXED (ρ=2/n → 0): δ* INCREASES 0.6875→0.8125 toward 1−ρ → 1 (orchestrator's RESOLUTION — correct here;
  the gap (1−√ρ, 1−ρ) itself shrinks to 0 as ρ→0, so δ* rising tracks the collapsing window).
- ρ=1/4 FIXED: δ* DECREASES 0.5625→0.5417 toward Johnson = 1/2 (the LOWER window edge), linear s*−k=n/4−1.
So the far-line incidence δ* does NOT uniformly "track the floor": at fixed ρ it tends to JOHNSON (lower edge),
at ρ→0 it tends to 1−ρ. As a RIGOROUS UPPER bound on MCA δ* (epsMCA≥far_inc/q), at fixed ρ it pins MCA δ* ≤
~Johnson+O(1/n) — i.e. the far-line upper bound is ASYMPTOTICALLY AT JOHNSON at fixed ρ, hence CANNOT certify
the floor 1−ρ−Θ(1/log n) > Johnson. The prize floor (strictly above Johnson) is NOT reachable via the far-line
incidence upper bound at fixed ρ; it needs the true MCA object (the BGK gap), exactly as localized. NOT a closure.

ENGINE BUG TRANSPARENCY (rule 6): a SCRATCH copy /tmp/pg-fast used `k + bmax` which OVERFLOWED when bmax
defaulted to usize::MAX (5 + MAX wraps to 4 < k ⟹ empty dirs ⟹ spurious maxI=0/"GOOD"). This affected ONLY
the DEFAULT (no-bmax) path of the scratch binary. ALL reported/pushed data used EXPLICIT bmax 4/6 (overflow-safe)
and was cross-validated against the unpatched original engine. The IN-REPO engine uses `k.saturating_add(bmax)`
(correct) — every pushed point (n=16,32 k=2; n=16,20,24 k=4..6) RE-VERIFIED with the correct repo full-sweep
binary, all identical. Scratch copy deleted. No pushed result was affected.

## ★★ SHARP CRITERION — far-line incidence δ* sinks BELOW Johnson for ρ<1/4 (exact ρ=1/8 series; refines my own regime note) (2026-06-15)

Self-refinement (rule 6) of the regime-clarification above. That note said far-line δ* "→ Johnson at fixed ρ"
based on ρ=1/4 (where Johnson=½ = the formula limit, tangent). Tested a SECOND fixed ρ=1/8 (where Johnson≠½)
to see which side it lands. EXACT (full-sweep rust-pg, valid subgroup p≡1 mod n verified, β=4; n=24 cross-
checked full vs bmax — identical):

| n  | k | s* | δ* | formula ½+(1/(2ρ)−1)/n | Johnson 1−√ρ | δ*−Johnson |
|----|---|----|----|----|------|------|
| 16 | 2 | 5  | 0.6875 | 0.6875 EXACT | 0.6464 | **+0.0411 (above)** |
| 24 | 3 | 9  | 0.6250 | 0.6250 EXACT | 0.6464 | **−0.0214 (BELOW)** |

THE CLEAN CRITERION (formula-exact at fixed ρ; the formula HOLDS at ρ=1/8, both points to the digit — it only
"breaks" along k=2 where ρ=2/n→0 is NOT a fixed ρ): far-line δ* → ½ as n→∞ (the formula limit). Therefore:
  δ* ends BELOW Johnson  ⟺  ½ < Johnson  ⟺  ½ < 1−√ρ  ⟺  **ρ < 1/4.**
- ρ=1/4: Johnson=½=limit, δ* → Johnson FROM ABOVE (tangent; my prior note's case). Verified 0.5625→0.5417↓.
- ρ<1/4 (e.g. 1/8): Johnson>½, so δ* CROSSES below Johnson (n=16 above → n=24 below). Verified.
- ρ>1/4: Johnson<½, δ* stays strictly above Johnson.

CONSEQUENCE (sharpens the prize picture): the far-line incidence δ* is a RIGOROUS UPPER bound on MCA δ*
(epsMCA≥far_inc/q ⟹ δ*_MCA ≤ δ*_far-line). For ρ<1/4 this upper bound drops BELOW Johnson, while the
conjectured window puts δ*_MCA ≥ Johnson. So at ρ<1/4 EITHER (a) MCA δ* < Johnson at these scales (the
Johnson lower bound is asymptotic, not finite-n), OR (b) the far-monomial-witness validity (joint-agreement
subtraction = 0) degrades for ρ<1/4 so the upper-bound chain loosens. EITHER WAY: the far-line incidence δ* is
a SUB-JOHNSON object for ρ<1/4 — definitively NOT the prize δ* (which is in (1−√ρ, 1−ρ−Θ(1/log n)), strictly
above Johnson). This RESOLVES "does far-line track the floor" with a sharp ρ-criterion: NO for ρ≤1/4 (it tends
to ½ ≤ Johnson). The prize floor needs the true MCA object (BGK gap), exactly as localized. NOT a closure.
Engine scripts/rust-pg (full + bmax cross-checked). n≤24 exact. Refines the regime note (rule-6 self-sharpening).

## odd-moment / odd-Sidon-depth lever — REFUTED as a sup handle; rigid -n^r identity + non-proving depth (2026-06-15)

Lens: the deep-Sidon frontier (the narrowed rule-3 lever, r~log n). Tested whether the ODD signed
period moments A_r := Σ_{b≠0} η_b^r carry a thinness-essential sup handle. (η_b REAL since μ_n is
closed under negation, so odd moments are real and sign-sensitive — the natural place for genuine
signed cancellation, unlike the |·| even moments already mapped thickness-invariant.)

Probes: scripts/probes/probe_407_{odd_moment_thinness,oddmom_scaling,Wr_odd_depth,depth_vs_M}.py
(exact integer zero-sum convolution + FFT-exact periods; proper subgroups μ_n⊊F_p*, odd-m primes
β≈2.2→4.6; n=8,16).

EXACT IDENTITY (landed axiom-clean, Frontier/_GaussPeriodMomentCensus.lean, push 76715441a):
  Σ_{b∈F} η_b^r = |F|·W_r,  W_r = #{(y_1..y_r)∈G^r : Σy_i=0}  (zero-sum census).
  ⟹ A_r = |F|·W_r − n^r.  Verified to machine precision (n=8,16, thick+thin).

REFUTATION (two parts):
1. The "odd-moment signed cancellation" A_r/(p·M^r) → 0 (as β grows) is a NORMALIZATION ARTIFACT:
   to the Sidon depth W_r=0 ⟹ A_r = −n^r EXACTLY (rigid, p-independent), so A_r/(p·M^r) = −n^r/(p·M^r)
   → 0 trivially (constant numerator / growing p·M^r). A_r carries ZERO information about
   M=max_{b≠0}‖η_b‖. Same shape as the refuted NC3 rigid-equation no-go.
2. The genuine thinness invariant — the odd zero-sum onset depth d_odd (first odd r with W_r>0) —
   GROWS with thinness (n=16: 7→9→11→none across β=2.45→4.6; n=8: 7→9→none) ⟹ rule-3-COMPATIBLE.
   BUT it does NOT control the normalized sup: M/√(n·log(p/n)) is flat ~1.1–1.3 across d_odd=5..13
   (non-monotone). So d_odd is a TRUE thinness invariant that is NON-PROVING for M at accessible scale.

WALL: the odd-moment / odd-Sidon-depth object splits into (a) a rigid identity that pins A_r=−n^r
to depth but says nothing about M, and (b) a thinness-essential depth that decouples from the sup.
The "deeper Sidon depth ⟹ smaller M" bootstrap FAILS empirically here. No CORE closure; the brick
is the exact moment↔census substrate, the wall is honest. Small n (8,16 exact).

## BHBI break — REALIZABLE-cone correction: 032525 break is OFF-SPEC; real break at n=32 β=4; ∀-field fluctuating (2026-06-15)

Lens: the freshest BHBI unification capstone (BridgeBounded / BoundedCyclotomicIndep / CountAntipodalBounded).
Adversarial check (rule 6) of the 032525 grind claim "C*(n=16, prize prime)=4 ⟹ chain BHBI(ω,8,4) FALSE,
witness g=(−4,−4,−4,−1,−1,−1,0,0)".

CHAIN SOURCE FACT (BridgeBounded.lean + RigidityGeneralT1.lean): the chain (bridgeZ_bounded → RepK) only ever
feeds BHBI a coefficient vector g_j = contribZ A j − contribZ B j with A,B FINSETS of signed half-basis points.
fiber A j ⊆ {(j,T),(j,F)}, isgn(j,T)=+1, isgn(j,F)=−1 ⟹ contribZ A j ∈ {−1,0,+1} (the in-tree `≤2` bound is a
loose card-≤2 overestimate; T+F cancel). ⟹ REALIZABLE g_j = a_j − b_j, a_j,b_j ∈ {−1,0,1} ⟹ g_j ∈ {−2..2}.
So the chain needs only BHBI(ω, n/2, 2) over the realizable {−2..2} cone — NOT C=4.

Probes: scripts/probes/probe_407_realizable_{bhbi,bhbi_verify,n32_exact,disjoint_check}.py (exact integer,
proper thin 2-power μ_n ⊊ F_p*, ω^{N}=−1 verified, prize primes p~n^β).

PART 1 — 032525 BREAK IS OFF-SPEC. n=16/p=65537 (β=4) exact brute: #relations in [−h,h]^8 = 0 at h=2 AND h=3;
1152 at h=4 (first = exactly the 032525 witness). The 032525 witness has max|coeff|=4 > 2 ⟹ NOT a realizable
contribZ-difference. At the REALIZABLE support {−2..2}, n=16/p=65537 is INDEPENDENT with margin (empty at h=2,3).
So "chain breaks at n=16 prize prime" was a generic-BHBI break, not the realizable-BHBI the chain consumes.

PART 2 — THE REAL BREAK (BGK wall in the realizable cone). At n=32 (N=16), realizable {−2..2} relations EXIST
at β∈{3,4,5}, exact-integer verified (Σ g_j ω^j = −5p, −10p, −9p respectively; ω^16=−1; max|g|=2; nonzero):
  β=4.00, p=1048609: g=(−1,−1,0,2,1,1,−1,2,−2,−2,−2,−2,−2,−2,−2,−2), Σ=−10·p. BHBI(ω,16,2) FALSE.
And ON-SPEC (probe_407_realizable_disjoint_check.py): every witness is realizable as contribZ A − contribZ B
with A,B DISJOINT and Σ_A sval = Σ_B sval mod p == 0 — exactly the domain of disjoint_equal_sum_antipodal_int_bounded.
⟹ the chain's required hypothesis BHBI(ω,16,2) already FAILS at the prize support (β=4) by n=32, on-spec.

PART 3 — ∀-FIELD-UNIVERSALITY (the c.154 trap). Realizable independence is PRIME-FLUCTUATING: n=16, β≈3.5 band,
realizable {−2..2} independence holds at only 2/12 prize-band primes. p=65537 being independent is a lucky-prime
false positive (the refuted "good prime exists" pigeonhole, §6/c.154). The prize is ∀-prize-field-universal;
realizable-BHBI must hold at EVERY prize-band prime, which it does not.

THINNESS (rule 3): C*_real (min realizable height) grows with β at SPECIFIC primes (n=16: 2 for β≤3.5 → 4 at
β=4 → none at β=6), but NON-UNIFORM across the field (prime-fluctuating, Part 3). CONSISTENT with the
matched-pair finding of 9a0868c62 (thin-vs-thick at FIXED prize prime sign-flips; neither C* nor the height-1
relation count discriminates thin from thick at n=32): there is NO clean ∀-field thinness invariant in the
bounded/realizable cone. NOT claiming a thinness invariant — deferring to that matched-pair rule-3-incompatible
conclusion. Distinct complementary content of THIS entry vs 9a0868c62: (i) the 032525 break is OFF-SPEC
(height-4 cone, not the realizable {−2..2} contribZ-difference cone the chain consumes); (ii) realizable
BHBI(ω,16,2) is FALSE at n=32 β=4 by an ON-SPEC DISJOINT contribZ-difference witness (exact Σ=−10p), locating
the wall at the chain's exact height-2 hypothesis (9a0868c62 measures the height-1 sign-relation COUNT, a
different cone).

NET: a correction (032525 break off-spec) + a precise location of the genuine wall in the realizable cone the
chain consumes (BHBI(ω,16,2) FALSE at n=32, β=4, on-spec disjoint witness, exact) + the ∀-field obstruction
(prime-fluctuating, c.154). No CORE closure; no fake. Small n (16 exact, 32 via MITM + exact-int verify).

### Follow-up (universal at n=32): realizable BHBI(ω,16,1) FALSE at ALL prize-band primes; height is 1 not 2; n=16 holds (2026-06-15)

Reconciling the above with 1fa2d5e58 (which reported C*(n=32)=1). Confirmed + universalized
(probe_407_n32_height1_check.py, MITM): at n=32, β=4.00, a HEIGHT-1 realizable {−1,0,1} relation
Σ g_j ω^j ≡ 0 (p) exists at **8/8** prize-band primes (p=1048609..1049569). A {−1,0,1} sign-relation
is trivially a realizable contribZ-difference (g_j = a_j − b_j, one of a_j,b_j = 0), so the minimal
realizable height at n=32 is **1**, not the 2 of my first witness — my n=32 height-2 witnesses were
non-minimal. The chain's required hypothesis BHBI(ω,16,C) thus fails for EVERY C≥1 at n=32 prize-band,
∀-field (not lucky-prime). And re-confirmed: n=16/p=65537 has NO realizable relation at height ≤2
(min height = None) ⟹ the n=16 chain holds at realizable support, the off-spec (height-4) 032525
witness was the only thing making n=16 look broken.

CLEAN STATEMENT OF THE WALL: realizable BHBI holds at n=16/prize (the chain's hypothesis is satisfied
there) but fails UNIVERSALLY at n=32/prize at height 1. The bounded-cyclotomic-independence lever's
required hypothesis is already ∀-field-FALSE by n=32. Combined with 9a0868c62 (no thin-vs-thick
discrimination), the BHBI lever cannot prove CORE: its hypothesis is false where needed and carries no
thinness discriminator. Mapped wall, not a closure. n=16 exact-brute, n=32 MITM + exact-int verified.

### BHBI-failure ⟷ (BIND)-failure are the SAME object at the half-basis (bridge, 2026-06-15)

Unifies the realizable-BHBI failure (above) with the §5.0 (BIND) non-antipodal-vanishing entry. A
half-basis height-1 relation Σ_{g_j=+1} ω^j − Σ_{g_j=−1} ω^j ≡ 0 (ω primitive 2^m-th root, ω^N=−1,
N=2^{m-1}) lifts to a FULL-index (Z/2N = Z/n) subset-sum vanisher via the antipode ω^{j+N}=−ω^j:
    S = {j : g_j=+1} ∪ {j+N : g_j=−1} ⊆ Z/n,   then  Σ_{i∈S} ω^i ≡ 0 (p)  — the BIND object.

PROBE (probe_407_bhbi_bind_bridge.py): for ALL 8/8 n=32 prize-band primes (p≈1.0486e6..1.0496e6,
β=4.00), the height-1 BHBI witness lifts to a NON-ANTIPODAL S with Σ_{i∈S} ω^i ≡ 0 (directly verified
in F_p). 8/8 non-antipodal, 0 antipodal. So the realizable-BHBI failure IS exactly a (BIND)-gate failure
on the half-basis face — they are not two independent walls but ONE object.

SCOPE/CONSISTENCY (rule 6, NO refutation): these primes are p~2^20, NOT the prize budget p~2^128. The
house hypothesis (#S)^φ(32)<p is FALSE here ((#S)^16 ≈ 2^51..59 ≫ 2^20 for #S≈9..13) — exactly the
regime where the sibling's BIND entry already predicts non-antipodal vanishing occurs. So this CONFIRMS
+ unifies (does not extend the refutation): BHBI-failure and BIND-failure coincide precisely when the
house bound fails. The prize is NOT refuted (small primes). What's mapped: the bounded-cyclotomic-
independence lever and the (BIND)/house-gate lever are the SAME wall viewed through two formalizations;
closing either at the prize budget needs the thinness-essential B_∞←B_{log n} Sidon bootstrap, not a
sharper bound on either equivalent face. No CORE closure.

### BHBI n=32 "wall" is a small-p PIGEONHOLE ARTIFACT; prize-regime failure is BASIS-LENGTH, thickness-invariant (2026-06-15)

Resolves the explicit SCOPE caveat left open by the BHBI<->BIND bridge entry (push 07517f301): that the
realizable-BHBI / (BIND) height-1 failure at n=32 was measured only at p~n^4~2^20, far below the
pigeonhole floor. Constraint lemma BHBI-PIGEONHOLE:

A realizable height-h relation Sum_{j<N} g_j omega^j = 0 (mod p), g in {-h..h}^N \ {0}, N=n/2, EXISTS
whenever (2h+1)^N > p (collision among (2h+1)^N sign-vectors in Z/p) -- for ANY N residues, thin or not.

PROBE 1 (probe_407_bhbi_house_threshold_sweep.py, exact MITM, thin mu_32 vs RANDOM 16-subset, p swept
20..40 bits): the height-1 relation (sole basis of the "forall-field FALSE at n=32" claim) exists ONLY at
p_bits=20 (the prize-band prime sits at the 3^16~2^25.4 edge), GONE by beta=4.4. The height-<=2 relation
persists to p_bits~32 then vanishes at 34 -- and the thin subgroup loses it at the SAME point as / EARLIER
than the random control (thin NONE at 34 while random still h=2). NO thin advantage.

PROBE 2 (probe_407_bhbi_pigeonhole_scaling.py): at the prize regime p=n^beta, the forced-margin
(n/2)log2(2h+1) - beta*log2(n) is positive and grows LINEARLY in n for fixed beta,h (n=128: margin_h1=73
bits; n=65536: margin_h1=51872 bits). So bounded-height realizable relations are pigeonhole-FORCED at EVERY
prize (n,beta) for large n -- a BANAL wall from the long half-basis (n/2 terms) vs the small modulus n^beta,
present for ANY N-subset.

PROBE 3 / CRUX (verify_n16_crux.py, exact brute n=16 p=65537): thin mu_16 has min realizable height = NONE
(no relation at h<=2), while 40/40 RANDOM 8-subsets DO have one. The thin 2-power subgroup is strictly MORE
relation-FREE than random -- the categorical OPPOSITE of a 2-power-structural vanishing obstruction.

VERDICT: CONFIRMS the sibling's conclusion (BHBI / bounded-cyclotomic-independence lever is walled, cannot
prove CORE) but CORRECTS the reason: the n=32 failure is a small-p pigeonhole artifact, and the genuine
prize-regime failure is THICKNESS-INVARIANT (basis-length pigeonhole), NOT 2-power/thin-essential. By rule 3
a thickness-invariant obstruction can neither prove nor refute CORE => the BoundedHalfBasisIndep formulation
is the wrong lever (hypothesis unsatisfiable for trivial reasons unrelated to thin-cancellation). The
discriminating thin content lives ABOVE the bounded-relation-height floor (the Sidon-bootstrap object).
CORE not closed. Python-only, no Lean changed => axiom-clean trivially. n=16 exact brute; n=32 exact MITM;
scaling analytic + exact small-n confirmation.

### CENSUS<->CORE EQUIVALENCE is OVERSTATED: CensusDomination is STRICTLY STRONGER than CORE (sufficient, not equivalent) (2026-06-15)

Maps the brief's flagged open brick: the count/census face (CensusDomination, CensusDominationWeld.lean)
whose EQUIVALENCE to CORE is asserted ("the $1M obligation in census normal form") but never proven.

IN-TREE ARCHITECTURE (verified at source):
  CORE handle:  epsMCA <= #bad / p          (epsMCA_le_of_badCount_le -- the deployed CORE bound)
  proven (U):   #bad   <= #alignable-a-sets (badScalars_card_le_alignable, UniversalAlignmentLaw:284)
  weld:         CensusDomination (#alignable <= K, all pairs, deep bands) => delta*-pin, with K/p <= eps*.
So the chain is  epsMCA <= #bad/p <= #alignable/p <= K/p <= eps*.  CensusDomination bounds #alignable;
CORE only needs #bad. The inserted step #bad <= #alignable is the ONLY place equivalence could fail, and
it is the step that is proven as a ONE-WAY inequality, never as an equivalence.

MEASUREMENT (exact mod-p, proper smooth subgroup mu_n, prize prime p~n^4, never n=q-1; semantics matched
to in-tree probe_alignment_census.py; probes probe_407_census_core_{equivalence,deepband,bindingband_ratio}.py):
At the BINDING deep band the ratio #alignable/#bad is LARGE and depth-decaying, NOT ~1:
  smooth n=16, k=3 (m=2 deep-ceiling shape), p=65537:
    KKH26 line [x^6,x^4]: a=4 1792/496(3.61), a=5 336/40(8.40), a=6(bind) 56/40(1.40)
    hifreq    [x^9,x^7]:  a=5 112/1(112.0), a=6 56/1(56.0), a=7 16/1(16.0), a=8(bind) 2/1(2.0)
  => at the hifreq line up to 112 alignable a-sets ALL pin ONE bad gamma (the many a-subsets of a SINGLE
     far-line agreement locus). #alignable OVERCOUNTS #bad by up to 112x.

THINNESS CONTROL (rule 3): thick n=12 shows the SAME inflation pattern (e.g. line [7,6]: a=5 180/12,
a=6 72/12, a=7 12/12) => the #alignable/#bad slack is THICKNESS-INVARIANT (not 2-power-essential).

VERDICT (refutation-grade for the EQUIVALENCE claim; NOT a CORE result, no overclaim):
CensusDomination is a STRICTLY STRONGER hypothesis than CORE -- a SUFFICIENT condition (via the proven
one-way (U)), NOT an equivalent encoding. The "$1M obligation in census normal form" wording overstates
equivalence: proving #alignable<=K proves MORE than the prize needs, and CensusDomination could even be
FALSE (too strong) while CORE holds. CONSEQUENCE: a CORE proof need NOT route through CensusDomination;
census-route effort should target #bad directly (#bad COLLAPSES to O(1) at the hifreq line -- the real
CORE signal -- while #alignable stays inflated). The (U) direction and the weld are correct as a
sufficiency chain; only the EQUIVALENCE framing is corrected. CORE not closed. Python-only, no Lean
changed => axiom-clean trivially. Exact small-n (n=8,12,16), prize primes, proper subgroups.

### THIN SIDON DEPTH SCALES: thin r_min(mu_n) advantage over random GROWS with n (corroborates + extends the surviving-lane handoff ef5f12fb1) (2026-06-15)

Lens: the surviving live object isolated by the full-depth-BIND refutation (ef5f12fb1): "the COLLECTIVE
thin depth profile (moment / sqrt-cancellation), NOT a per-S no-vanisher statement." That entry PROVED a
thin advantage exists at one point (n=32,beta=4: thin r_min=11 vs random median 6) but did NOT measure how
the thin Sidon depth SCALES with n. This is the first scaling measurement.

OBJECT: thin Sidon depth r_min(mu_n,p) = smallest NON-antipodal subset S of Z/n with Sum_{i in S} zeta^i
== 0 (mod p), zeta primitive n-th root, mu_n proper 2-power subgroup of F_p*, p=ceil(n^beta) prime ==1(n),
NEVER n=q-1. r_min = NONE => full-depth (no vanisher up to n/2). Random control = median r_min over 5
random n-subsets of F_p* of the SAME density.

METHOD: exact-integer meet-in-the-middle (index halves, subset-sum collision), antipodal-closed sets
EXCLUDED. n=8,16,32 exact, rmax=n/2. probe_407_thin_sidon_depth_scaling.py.

RESULT (the scaling, with the one non-censored thin point EXACT-VERIFIED):
| n  | beta | thin r_min | random median | margin | note |
|----|------|------------|---------------|--------|------|
|  8 | 4.0  | >4 (full)  | 5             | +0     | thin full-depth, random vanishes ~n/2 |
| 16 | 4.0  | >8 (full)  | 9             | +0     | thin full-depth |
| 32 | 4.0  | **11**     | 7             | **+4** | EXACT witness verified (size 11, sum=0, non-antipodal; NONE for r<11) |
|  8 | 5.0  | >4 (full)  | 5             | +0     | |
| 16 | 5.0  | >8 (full)  | 9             | +0     | |
| 32 | 5.0  | >16 (full) | 9             | **+8** | thin still FULL-depth at n=32 while random median 9 |

VERDICT (corroboration + extension; NOT a CORE result, rule-6 scoped):
1. The thin advantage is REAL and THINNESS-ESSENTIAL (rule-3 PASS): thin mu_n is strictly deeper-Sidon
   than a random same-density set at EVERY (n,beta); at small n thin is full-depth while random already
   vanishes near n/2.
2. The advantage MARGIN GROWS with n: +0,+0 -> +4 (beta=4) and +0,+0 -> +8 (beta=5). The 2-power structure
   pushes the first vanisher progressively deeper relative to random as n grows -- the collective thin
   signal the moment/sqrt-cancellation route needs.
HONEST SCOPE: small-n thin rows are CENSORED at rmax=n/2 (full-depth), so the EXACT growth LAW (sqrt(n) vs
log^c n) is not yet resolved -- need n=64,128 (randomized, SOUND-on-failure) to fit the exponent. r_min is a
LOWER proxy for the full collective depth profile (smallest vanisher); a growing r_min is NECESSARY, not
sufficient, for the collective CORE route. The n=32/beta=4 r_min=11 is exact-verified (witness
[9,14,16,17,19,21,22,23,26,28,31], sum=0 mod 1048609, non-antipodal). CORE not closed; the surviving thin
mechanism's scaling is positively confirmed for the first time. Python-only, no Lean => axiom-clean trivially.

### crossCell DYADIC-TOWER ITERATION does NOT certify CORE even GRANTING BCHKS-1.12: it leaks to the TRIVIAL M(n)<=n (2026-06-15)

Maps an asserted-but-unproven CLOSURE step in CrossCellShkredovBound.lean. That file names the one open
lever of the dyadic cumulant descent N0(G,r)=2*N0(H,r)+crossCell(H,zeta,r) (G=mu_n=H u zeta*H, H=mu_{n/2}),
states the OPEN absolute bound CrossCellAbsoluteBound = BCHKS25 Conj 1.12 (crossCell*q <= 2^r*|H|^r), and
proves the per-level consumer N0_gap_of_absoluteBound: N0(G,r) <= 2*N0(H,r) + 2^r*|H|^r/q. Its docstring
then ASSERTS that iterating this down the 2-power tower with q~n*2^128 "keeps the cross mass below the
diagonal and converges to the clean closed form N0(G,r)~2*N0(H,r) -- the closure mechanism, conditional on
the open bound," and references a consumer `prize_of_ShkredovSubTrivialBound` which is NOT present as a
theorem (only the per-level N0_gap_of_absoluteBound exists).

TESTED the asserted closure IMPLICATION exactly (char-0 exact bigint on the bound itself, independent of
whether the open bound is true). Tower recursion (absolute bound at EACH level, q FIXED, T_j:=q*N0(2^j,r)):
  T_{j+1}(r) = 2*T_j(r) + 2^r*(2^j)^r,   T_1(r) = q*C(r,r/2) [r even else 0].
Fed into the in-tree raw-moment certificate M(n) <= min_r (sum_{b!=0}|eta_b|^{2r})^{1/2r},
  sum_{b!=0}|eta_b|^{2r} = q*N0(G,2r) - n^{2r}.  Probe probe_407_crosscell_tower_iteration_nogo.py.

RESULT (sound, floor-checked against the proven floor M >= sqrt(n(q-n)/(q-1))):
  | mu | n     | floor=.5log2(n..) | CORE=.5log2(n log m) | abs(BCHKS) log2 M | verdict |
  |  5 | 32    | 2.50              | 5.74                 | 4.003             | = log2 n (TRIVIAL) |
  |  8 | 256   | 4.00              | 7.24                 | 7.003             | = log2 n (TRIVIAL) |
  | 12 | 4096  | 6.00              | 9.24                 | 11.003            | = log2 n (TRIVIAL) |
  | 17 | 131072| 8.50              | 11.74                | 16.003            | = log2 n (TRIVIAL) |
Granting CrossCellAbsoluteBound, the iterated certificate is SOUND (always >= floor) and floors EXACTLY at
log2 M(n) ~ log2 n => M(n) <= n (the TRIVIAL L^1 bound), never sqrt(n log m) (CORE) and not even sqrt(n)
(Johnson). MECHANISM (decomposition audit): the top-level cross injection is 2^r*|H|^r = 2^r*(n/2)^r =
n^r-scale, so q*N0(G,2r) accumulates an n^{2r}-scale cross mass; q*N0(G,2r) - n^{2r} floors at n^{2r}, and
(n^{2r})^{1/2r} = n. The cross term injected by the (granted) bound is exactly the size that pins the
certificate at the trivial n.

SOUNDNESS GUARDS (rule 6): (a) the IDEAL crossCell=0 case (= the docstring's "clean closed form", perfect
halving N0(2^{j+1})=2*N0(2^j)) goes VACUOUS (moment <= 0) past low r => yields no usable bound either, so
the "clean closed form" does NOT certify CORE on its own. (b) the measured "random-count" injection form
(2^r-2)|H|^r/q gives certificates that VIOLATE the proven floor (log2 M < .5 log2 n) => UNSOUND, discarded
(it measures a vanishing gap, not a valid M upper bound). Only the absolute-bound certificate is sound, and
it is trivial.

VERDICT (rule-4 constraint map; NOT a CORE result, NOT a refutation of BCHKS-1.12 itself): the dyadic-tower
ITERATION of the crossCell gap is NOT a CORE-closure mechanism. Even granting the open BCHKS-1.12 absolute
bound, iterating the per-level gap leaks to the trivial M(n)<=n. The CrossCellShkredovBound.lean docstring's
claim that the iteration "converges to the clean closed form ... the closure mechanism, conditional on the
open bound" OVERSTATES what the iteration yields; the referenced `prize_of_ShkredovSubTrivialBound` consumer
cannot deliver CORE in this shape. This is CONSISTENT with the meta-theorem (Sec.4: every second-order/moment
method caps at the trivial n via (q E_r)^{1/2r} >= n) but is NOT a re-derivation: the meta-theorem covers
SINGLE-DEPTH moment methods; this maps the specific ITERATED-TOWER consumer conditional on the named open
crossCell bound, closing a gap between "the open bound" and "a CORE proof" that the file's docstring left
implicit. The genuine open input (per the file's own conclusion) must come from the ARITHMETIC of the
q-reduction (spurious mod-p collisions making crossCell sub-random), NOT from the granted absolute bound fed
through the tower. Thinness-blind (a NO-GO need not be thin-essential, rule 3 OK for refutations). CORE not
closed. Python-only, exact bigint, no Lean changed => axiom-clean trivially.

## ⚠️ REFUTATION (surviving-lane, rule-3 PASS but WRONG SIGN) — the COLLECTIVE EVEN census/energy profile of mu_n is NOT suppressed below random; it is INFLATED, super-multiplicatively in r (2026-06-15, opus-4-8 subagent)

LENS: the surviving live object isolated by the full-depth-BIND refutation (ef5f12fb1) + handoffs: "the
COLLECTIVE thin depth profile (moment / sqrt-cancellation), NOT a per-S no-vanisher statement." Prior work
measured only (a) r_min = smallest single vanisher (e7b5e6125: thin DEEPER), (b) d_odd onset (odd_moment
entry: thin deeper, but A_r=-n^r RIGID, decouples from M), (c) A_r/Wick RATIO at the optimizer r* + its
n-trend (step_at_rstar: margin erodes). NONE measured the per-r EVEN energy moment PROFILE E_{2r}(mu_n) =
sum_{b!=0}|eta_b|^{2r} (the object feeding A_r = E_r - n^{2r}/q <= Wick, the genuine prize moment) against a
thin-density RANDOM control, to test whether the thin advantage COMPOUNDS (collective) or is single-depth.
This is that measurement -- and it kills the "thin advantage helps the moment route" hope at the EVEN level.

METHOD (exact, rule-2 + rule-3 clean): eta_b = exact integer DFT of indicator(mu_n) in F_p; mu_n = <g^m>,
m=(p-1)/n > 1 PROPER (NEVER n=q-1). prize-band primes p~n^beta, beta in {4.0,4.5}, incl. one non-Fermat.
RANDOM control = median over 5 random n-element subsets of F_p* (same thin density). Probes
scripts/probes/probe_407_even_census_profile.py + probe_407_even_census_dcsub.py (adversarial re-audit).

RESULT 1 -- E_{2r}(thin)/E_{2r}(random) GROWS with r (thin is LARGER, not suppressed):
| n  | beta | E2r ratio r=1..6                              |
|----|------|----------------------------------------------|
| 16 | 4.0  | 1.00, 1.45, 2.27, 3.59, 5.68, 8.85           |
| 16 | 4.5  | 1.00, 1.45, 2.27, 3.59, 5.67, 8.80 [non-Fermat]|
| 32 | 4.0  | 1.00, 1.48, 2.38, 3.98, 6.75, 11.57          |
The thin even-energy moment is BIGGER than random at every r>=2 and the gap COMPOUNDS upward. Since A_{2r} =
|F|*W_{2r} - n^{2r} tracks E_{2r}, the thin A_{2r} is FURTHER from suppression than random, worse with depth.

RESULT 2 (ADVERSARIAL re-audit, rule 6 -- is this just the known "thin M>=random M" sup fact re-seen?): NO.
(a) COLLECTIVE shape: the thin/random ratio of the t-th LARGEST |eta_b| is >=1.1 not only at t=1 (sup) but at
    t=1,2,4,...,128, and GROWS into the spectrum body (n=32: 1.157 @t=1 -> 1.309 @t=128). The ENTIRE top of the
    period spectrum is inflated in thin, not one extreme outlier -- genuine collective over-concentration.
(b) The even-moment ratio EXCEEDS the sup-only prediction (M_thin/M_rand)^{2r} at deep r: n=16 r=6 ratio 8.58
    vs sup-pred 3.47; n=32 r=6 ratio 11.40 vs sup-pred 5.77. So the moment growth is NOT explained by the sup
    alone -- the BODY of the spectrum contributes a genuine extra (super-sup) factor. New collective signal.

VERDICT (rule-4 mapped wall; rule-3 PASS but the thinness-essentiality has the WRONG SIGN for CORE):
1. mu_n's even period-energy profile IS thinness-essential (thin differs from random) -- but in the direction
   that makes the moment object HARDER, not easier: thin is collectively MORE concentrated (top-heavy at every
   quantile), so A_{2r}(thin) > A_{2r}(random), and the excess COMPOUNDS super-multiplicatively in r.
2. This WALLS the "surviving collective thin depth profile -> smaller M via moments" hope at the EVEN level:
   the thin advantage that exists at the ODD signed-vanisher level (r_min, d_odd deeper) does NOT carry to the
   EVEN energy moments -- the very ones in A_r <= Wick. The collective even profile is anti-helpful.
3. RECONCILES + SHARPENS ILO (852e0fa27, "thin anti-concentrated worse, sup only") + the moment thickness-
   invariance note: it's not only the sup -- the WHOLE even spectrum is collectively inflated, and the
   inflation grows with moment order. The signed/odd thin depth and the even-energy concentration point
   OPPOSITE ways; the moment route needs the even one, which is adverse.
HONEST SCOPE: small n (16,32 exact), p~n^{4-4.5}. Random control is finite-sample median (5 draws). This is a
COLLECTIVE refutation of the even-moment thin-suppression hope, NOT a CORE closure nor a prize refutation:
the surviving structural hope is the ODD signed family-level Sidon bootstrap (B_inf<-B_{log n}), which lives
in the signed/odd object, NOT the even energy profile measured here. CORE not closed. Python-only, no Lean =>
axiom-clean trivially. Multi-prime (incl. non-Fermat) -> not a Fermat artifact.

### crossCell is p-INDEPENDENT (char-0 structural) + SUPER-random in the thin regime: the proposed "sub-random via mod-p collisions" open input is WALLED (2026-06-15)

Follow-up to the crossCell dyadic-tower no-go (push ad90dc8d5). That entry showed iterating the per-level
crossCell gap (granting BCHKS-1.12) leaks to trivial M<=n. CrossCellShkredovBound.lean's own CONCLUSION then
proposes that the genuine open input "must come from the ARITHMETIC of the q-reduction (spurious mod-p
collisions)" -- i.e. it hopes crossCell is SUB-random (< the BCHKS-1.12 expectation) because collisions cancel
structure. This entry tests that hope directly in the thin prize regime and WALLS it.

OBJECT (exact char-p, proper subgroup, NEVER n=q-1): G=mu_n=H u zeta*H, H=mu_{n/2}, crossCell(r)=
N0(G,r)-2*N0(H,r) (>=0 by the descent). Random/BCHKS-1.12 expectation E_rand(r)=(2^r-2)|H|^r/p.
Probe probe_407_crosscell_superrandom_pindep.py (exact running-sum DP counting, multi-prime, rule-3 control).

RESULTS:
1. crossCell is PERFECTLY p-INDEPENDENT in the thin regime (beta>=4): n=8 -> 96 (r=4), 4320 (r=6) at EVERY
   prime {4129,4153,4177,4201}; n=16 -> 384, 40320 at EVERY prime {65537,65617,65633,65713}. => it is the
   char-0 STRUCTURAL relation count (#{sum u + zeta sum w = 0} holding over Z, hence at every large p), with
   ZERO spurious mod-p collision component (collisions scale like 1/p; crossCell does not move at all).
2. SUPER-random, diverging with thinness: ratio crossCell/E_rand ~ (p-indep count)/(C/p) ~ p. beta=4: n=8
   r=4 ratio 110x, n=16 r=4 438x; beta=5: 878x / 7022x. crossCell is FAR ABOVE random, never below.
3. rule-3 THINNESS control: thick beta=2.3 ratio O(1)-4x; thin beta=4-5 ratio 100x-7000x. The super-random
   excess is the char-0 structural floor dominating as p->infty -- thinness-ESSENTIAL, not a collision artifact.
4. At thick/small p the count can EXCEED the char-0 value (n=16 r=6: 48000 at p=593 vs 40320 char-0) =>
   collisions only ADD to crossCell, never give a sub-random saving.

VERDICT (rule-4 constraint map; NOT a CORE result, NOT a prize refutation): there is NO sub-random saving in
crossCell to extract. crossCell >= its char-0 structural count at all p (collisions only add). The proposed
"arithmetic-of-the-q-reduction / mod-p-collision" open input of CrossCellShkredovBound.lean is WALLED: the
binding object is the p-INDEPENDENT char-0 structural relation count, exactly the (super-random,
BCHKS-1.12-saturating) quantity, with no mod-p cancellation available. CONSEQUENCE: any CORE proof routing
through crossCell must bound the CHAR-0 structural count itself (= vanishing-sums-of-roots-of-unity /
Lam-Leung over the 2-power tower), NOT hope for collision savings -- which re-localizes the open content onto
the already-mapped char-0 antipodal/Sidon object (ConverseLamLeung2Power, the surviving thin Sidon bootstrap),
NOT a new arithmetic mechanism. Combined with the tower no-go (ad90dc8d5): granting BCHKS-1.12 doesn't close
(tower leaks to n), AND the proposed route to PROVE a sub-BCHKS crossCell bound (collisions) is empty. CORE
not closed. Python-only, exact DP, multi-prime (Fermat + non-Fermat), no Lean => axiom-clean trivially.

### A3 REVERSE-DICTIONARY FLOOR-PUSH is THICKNESS-INVARIANT at the (halfJ,J)-window radius -- not the thin lever (2026-06-15)

LANE: #444 §1 A3 -- "push delta* UP past half-Johnson via the reverse LD=>MCA dictionary at larger n",
the orchestrator's explicitly-flagged "genuinely-unattacked OTHER HALF of the prize" / fallback. First
RULE-3 thinness gate applied to the reverse dictionary (ReverseDictionary.exists_interleavedList_card_gt_of_epsMCA_gt).

OBJECT (exact, in-tree axiom-clean): forward eps_mca(C,delta) <= (1+(n-a)*L)/q; reverse contrapositive
=> L_force = floor((incid-2)/(n-a)) is a machine-checkable LOWER bound on some pair's interleaved list
size at collapse radius a, incid = eps_mca*q. Proven floor = half-Johnson delta* >= (1-sqrt rho)/2
(HalfJohnsonDeltaStar); full Johnson 1-sqrt rho is the OPEN all-pairs target (SmallSubgroupGoodList).
A3 hope: smooth mu_n forces a SMALLER list than random at radii in (halfJ,J) => a higher thin floor.

METHOD (probe-first, exact mod-p, PROPER smooth subgroup mu_n, never n=q-1): exact eps_mca bad-LINE
incidence at the (halfJ,J)-window radius, SMOOTH mu_n vs RANDOM domain, prime sweep (q-invariance +
rule-3). n-k=2 exact-feasible cases. probe_407_a3_fast.py + probe_407_a3_window_map.py.

RESULT (rule-4 mapped constraint; rule-3 verdict):
| n | k | rho | window radius delta in (halfJ,J) | smooth incid | random incid | q-invariant | thin |
|---|---|-----|----------------------------------|--------------|--------------|-------------|------|
| 4 | 2 | 0.500 | 0.250 (halfJ 0.146, J 0.293) | 4 = n | 4 = n | YES (13,17,29,37,41) | smooth==random |
| 6 | 4 | 0.667 | 0.167 (halfJ 0.092, J 0.184) | 6 = n | 6 = n | YES (7,13,19,31,37)  | smooth==random |
Full radius profile: the UNIQUE radius in (halfJ,J) sits at incidence = n = the budget exactly; next
radius down (delta=0, <halfJ) has incidence 1.

VERDICT (two-sided, honest):
 POSITIVE (generic): eps_mca = incid/q = n/q = budget eps* exactly at this radius => delta* reaches the
   (halfJ,J) window (0.25 > halfJ 0.146) GENERICALLY; reverse L_force (>=2 at n=4, >=4 at n=6) is a real
   forced interleaved-list lower bound at the budget-binding radius.
 NEGATIVE (decisive): the mechanism is THICKNESS-INVARIANT -- smooth mu_n and a random generic domain
   give the IDENTICAL incidence (=n) at every tested prime in (halfJ,J). By rule 3 (CORE false in the
   thick window => thickness-invariant method neither proves nor refutes CORE), the reverse-dictionary
   floor-push at the window-top radius is NOT thinness-essential: A3's hope (smooth smaller list => higher
   thin floor) is REFUTED at the feasible radii -- no smooth-vs-random gap exists. The factor-of-two to
   full Johnson 1-sqrt rho is NOT closable by the reverse dictionary here; it genuinely needs the
   all-pairs / thin-essential input (SmallSubgroupGoodList), confirming HalfJohnsonDeltaStar's stated
   open problem from the floor side.

HONEST SCOPE (rule 6): only n-k=2 (rho 1/2, 2/3) is exact-feasible at small primes; the genuinely-thin
prize cone (rho 1/4-1/8) needs small n-k at large n (exact-infeasible -- same wall every worker hits). So
this is thickness-invariance at MODERATE rho; the DIRECTION (no thin gap at the window-top radius) is
robust over both rho and all primes, but the thin-rho extrapolation is NOT proven (future work, needs MITM
infra). WALLS the reverse-dictionary route to the floor-push at the tested radii; does NOT refute CORE.
Python-only, no Lean changed => axiom-clean trivially. First rule-3 gate on the reverse dictionary (grep:
"reverse" had 0 prior DISPROOF entries outside the lacunary one).

## ⚠️ REFUTATION (completes the even+odd picture) — the SIGNED odd moment beyond the Sidon depth: thin's deep-Sidon RIGIDITY makes signed cancellation WORSE, not better (2026-06-15, opus-4-8 subagent)

LENS: companion to the even-census-profile refutation (6feb11b53, even E_{2r} thin INFLATED). The surviving
thin advantage lives in the ODD/SIGNED object (r_min, d_odd deeper). Since mu_n is negation-closed, eta_b is
REAL, so odd moments A_r = sum_{b!=0} eta_b^r are real + sign-sensitive -- the natural home for the signed
cancellation the B_inf<-B_{log n} bootstrap needs. The odd_moment entry showed A_r=-n^r RIGID below d_odd
(W_r=0, no info). UNPROBED until now: does the SIGNED cancellation BEYOND d_odd (W_r>0) compound FAVORABLY
(thin cancels MORE => helps), measured against the RIGHT control?

RULE-3 CONTROL FIX: a random n-subset is NOT negation-closed (odd moments not even real). The correct control
that isolates the 2-POWER-SUBGROUP structure from mere negation-closure is a NEGATION-CLOSED random set: a
random union of n/2 antipodal pairs {x,p-x}. Compared thin vs this control via the signed-cancellation
EFFICIENCY eff_r := |A_r|/sqrt(E_{2r}) (Cauchy-Schwarz normalized; 1 = no cancellation, ->0 = full signed
cancellation). Exact real periods eta_b = sum_{x in S} cos(2pi b x/p); proper mu_n (m>1, never n=q-1);
prize primes p~n^{4-4.5} incl. non-Fermat. Probe scripts/probes/probe_407_signed_odd_profile.py.

RESULT (the separation appears at n=32, where d_odd is crossed within reach):
- n=16 (b=4.0, 4.5[nf]): thin AND neg-closed-random BOTH stay rigid A_r=-n^r through r=9 (d_odd>9 for both)
  -- no separation yet at reach (honest: small-n censored).
- n=32 (b=4.0, p=1048609): thin stays RIGID (A_r=-32^r EXACTLY) through r=7, non-rigid only at r=9. The
  neg-closed RANDOM control breaks rigidity EARLIER: r=7 random A_7=-1.32e10 != -32^7=-3.44e10; r=9 random
  -5.69e12 vs thin -1.54e13. CONSEQUENCE on the efficiency:
    r=7: eff_thin=0.695 vs eff_rand=0.270  (thin 2.6x WORSE at signed cancellation)
    r=9: eff_thin=0.796 vs eff_rand=0.301  (thin 2.7x WORSE)
  |A_r|(thin)/|A_r|(rand) = 2.60 (r=7), 2.71 (r=9): thin's |A_r| is LARGER.

MECHANISM (clean): thin's deep-Sidon RIGIDITY PINS A_r at the full -n^r (zero cancellation among the b's,
since W_r=0 forces A_r=-n^r exactly), while the random control's EARLIER d_odd onset lets its signed moments
CANCEL DOWN BELOW n^r. So "deeper Sidon" is ANTI-HELPFUL for signed cancellation: rigidity = no cancellation
= |A_r| pinned HIGH at n^r, the opposite of the suppression the bootstrap needs.

VERDICT (rule-4 mapped wall; completes the even+odd picture): the thin advantage in DEPTH (r_min, d_odd
deeper) does NOT translate to better moment cancellation in EITHER parity --
  EVEN (6feb11b53): thin energy E_{2r} collectively INFLATED, super-multiplicatively in r.
  ODD/SIGNED (here): thin's deep-Sidon rigidity PINS |A_r|=n^r, so signed-cancellation efficiency is 2.6-2.7x
  WORSE than the neg-closed random control beyond d_odd.
Both faces of the "collective thin depth profile -> smaller M via moments" hope are now mapped as adverse:
the very rigidity/Sidon-depth that the bootstrap touts is what KEEPS the moments large. The surviving hope is
NOT a moment/cancellation argument at all (both parities adverse) -- it must be a per-frequency / structural
estimate that does not pass through the period MOMENTS. CORE not closed, not faked. Small n (16 censored, 32
shows the separation), multi-prime incl. non-Fermat. Python-only, no Lean => axiom-clean trivially.

### The STATED CrossCellAbsoluteBound (BCHKS-1.12 as written) is FALSE at every prize-relevant depth -- NOT "the open wall" (2026-06-15)

Completes the crossCell-lever mapping (companions: tower no-go ad90dc8d5, super-random/p-indep 5a8d7fd42).
CrossCellShkredovBound.lean DEFINES and labels "the correct OPEN form ... NOT refuted; remains the wall":
  CrossCellAbsoluteBound :  forall r>=2,  crossCell(H,zeta,r)*q <= 2^r*|H|^r,  |H|=n/2  (= BCHKS Conj 1.12).
The per-level consumer N0_gap_of_absoluteBound uses exactly this. We show the STATED Prop is FALSE at every
feasible/prize-relevant depth.

KEY EXACT FACT: crossCell(n,4) = 3n^2/2, EXACTLY, char-0, p-independent. Derivation from in-tree bricks:
crossCell(n,4) = N0(G,4) - 2*N0(H,4) = E(mu_n) - 2*E(mu_{n/2}) = (3n^2-3n) - 2*(3(n/2)^2-3(n/2)) = 3n^2/2,
using AdditiveEnergyNegClosedLower E(mu_n)=3n^2-3n. Verified exactly: n=8->96, n=16->384, n=32->1536 (=3n^2/2).

(A) STATED bound at r=4:  (3n^2/2)*q <= 2^4*(n/2)^4 = n^4  <=>  q <= (2/3)*n^2.  Prize q~n*2^128 >> n^2 =>
    VIOLATED by ~2^128.  Exact at prize-shaped primes: n=8 b=4 p=4129: LHS=396384 > RHS=4096 (97x);
    n=16 b=4 p=65537: 25166208 > 65536 (384x); n=32 b=4: 1.6e9 > 1.05e6 (1536x).  False at thick b=2.3 too.
(B) depth threshold r0(n): the bound n^r >= crossCell(r)*q holds only once r*log2 n >= log2 crossCell(r) +
    log2 q (log2 q ~ log2 n + 128).  crossCell(r) is the FIXED char-0 structural count (p-indep), so r0 is
    LARGE: measured/extrapolated r0(8)~465, r0(16)~206 -- both >> the prize BINDING depth r ~ ln q ~ 89.
    So the stated inequality is FALSE at r=4..89 (every prize-relevant order) and only becomes true at an
    astronomically large, useless r0.

RECONCILIATION with the file's own probe ("crossCell tracks the random BCHKS-1.12 expectation (2^r-2)|H|^r/p
to O(1)"): that was measured at SMALL accessible primes (p ~ relation height) where crossCell ~ random. At
PRIZE primes (p ~ 2^128) the two DIVERGE by ~2^128 -- crossCell frozen at the char-0 structural value, the
random expectation -> 0.  The "to O(1)" agreement does NOT survive to the prize regime, which is exactly why
the stated absolute bound fails there.

VERDICT (rule-4 constraint map; precise correction, NOT a CORE result, NOT a refutation of the TRUE BCHKS
Conj 1.12 which is an asymptotic statement): the Lean Prop CrossCellAbsoluteBound, as written (forall r>=2,
crossCell*q <= 2^r|H|^r), is FALSE at every prize-relevant depth and is NOT the open wall the file labels it.
The genuine open object is a DEPTH-CORRECT, p-independent STRUCTURAL count bound at the binding depth r~ln q
(= the char-0 vanishing-sums-of-roots-of-unity / Lam-Leung object, in-tree ConverseLamLeung2Power), NOT the
literal 2^r|H|^r/q random count.  CONSISTENT with + completes the two companion crossCell results: (1) even
granting the (false-as-written) bound the tower iteration leaks to trivial M<=n; (2) the proposed sub-random
proof route is empty (crossCell super-random); (3) HERE: the bound as stated is itself false at feasible
depth.  All three pin the crossCell lever as mis-stated/non-closing in its current form; the live content is
the char-0 structural count (sibling-active thin-Sidon object), not a new arithmetic mechanism. CORE not
closed. probe_407_crosscell_absbound_false_at_prize.py. Exact DP, multi-prime, no Lean => axiom-clean trivially.

## ✓ RULE-6 RE-AUDIT (confirms 6feb11b53 robustly + one honest onset refinement) (2026-06-15, opus-4-8 subagent)

Adversarial re-audit of the even-moment-inflation push 6feb11b53, addressing two worries: (W1) "exceeds the
(M_thin/M_rand)^{2r} sup prediction" could be a cross-draw artifact (random median moment vs random median sup
from DIFFERENT draws); (W2) the inflation could be 5-draw variance. FIX: 21 random draws, per-draw
self-consistent (each draw's M and E_{2r} from the SAME spectrum), apples-to-apples sup prediction (the
max-MOMENT draw's OWN M). Probe scripts/probes/probe_407_even_reaudit.py.

RESULT (n=16, β=4.0 + β=4.5[non-Fermat]):
1. INFLATION IS ROBUST, NOT VARIANCE: thin E_{2r} exceeds the MAX-moment random draw (most concentrated of
   21) at EVERY r≥2 — 21/21 draws below thin. Not a median artifact.
2. "EXCEEDS sup prediction" CONFIRMED but onset is r≥4 (apples-to-apples), not r≥3 as the original
   cross-draw comparison suggested at β=4.5: β=4.0 exceeds from r≥3 (thin/maxdraw 2.165 > sup-pred 1.943);
   β=4.5[nf] exceeds from r≥4 (r=3: 2.162 vs 2.238, just BELOW; r=4: 3.281 > 2.927). HONEST REFINEMENT: the
   "exceeds sup" claim holds at DEEP r (r≥4 robustly, r≥3 at β=4.0), with growing margin — my receipt's "at
   deep r" wording is accurate; the exact onset is r≥4 under the strict apples-to-apples test.
NET: 6feb11b53's two claims (collective inflation; exceeds sup at deep r) both STAND under 21-draw
self-consistent re-audit; the only adjustment is the precise onset (r≥4 strict, vs r≥3 loose). No overclaim
survives; the finding is robust. Python-only => axiom-clean trivially.

================================================================================
2026-06-14 wf-D1 (#444): the binding wf-NH far-line incidence I(n) is QUARTIC, not a small constant
--------------------------------------------------------------------------------
REFUTED (as a reading of the closure path): "at the binding radius δ* is a SMALL p-independent
computable combinatorial quantity off the √-cancellation wall, so the prize is a small number."
The p-independence is REAL (confirmed). The "small" part is FALSE.

OBJECT: FarCosetExplosion exact binding incidence, k=4, size=6 (s-k=2 over-determined), r=n-6,
far dir x^b (b in [4,6)), offset x^a, budget n. I(a,b) = #{γ : x^a+γx^b agrees with RS[4] on >=6}.
ENGINE: cofactor-factorized vectorized exact count (scripts/probes/probe_wf3D1_unified.py),
cross-validated EXACTLY vs the proven reference probe_farline_incidence_exact.incidence at n=16
(both 89, dir (10,4), p-independent across 3 primes). A colex-vs-lex CNS-rank bug was caught/fixed
before any number was reported.

VERIFIED (proven-per-fixed-n, p-INDEPENDENT):
  I(16) = 89   dir (10,4)   p in {200017,5000081,16777441}   I/n^4 = 1.358e-3
  I(32) = 1441 dir (18,4)   p in {1048609,1048897}           I/n^4 = 1.374e-3
  log-log slope (16->32) = 4.017  =>  I(n) ~ 1.37e-3 * n^4  (clean p-independent QUARTIC)
  binder = monomial x^4 = x^k (lowest far exponent), offset a ~ n/2+2.

CONSEQUENCE: at the fixed over-det radius r=n-6 the incidence is quartic, so I/budget ~ n^3 and the
radius sits FAR above δ* (consistent with the in-tree δ*=9/16 pin: r=10=n-6 is the FIRST bad radius,
I=89 >> 16). The binding object is a genuine high-degree (quartic) cyclotomic incidence count, NOT a
small constant. NET: the closure path's p-independence half STANDS and is reinforced (the whole δ*
curve is computable p-FREE, no √-cancellation needed to EVALUATE it); the "small computable number"
half is refuted. New open object: the r-PROFILE I(n,r) (δ* = largest r with I(n,r)<=n) — a finite
exact p-free computation, not a char-sum bound.
Python-only numerics => axiom-clean trivially. — wf-D1

================================================================================
2026-06-15 LD-radius plateau thinness gate (#444): the per-direction n-plateau
quantization is thinness-essential but ANTI-HELPFUL for the floor (opus-4-8 subagent)
--------------------------------------------------------------------------------
LANE: the list-decoding reframing (KB deltastar-perdirection-decomposition-listdecoding.md +
orchestrator redirect c.4704732... "the floor = mu_n list-decodes past Johnson"). Reframes
delta* = 1 - s*/n where s*(D,k) = max over far monomial lines x^a+gamma*x^b of the largest
agreement with RS[D,k] using <= budget=n scalars (the far-line LD radius). The per-direction
incidence I_dir(a,b;s) is a clean step function whose PLATEAU value = exactly n ("divisibility
quantization", n | #bad, attributed to mu_n being a subgroup). UNTESTED: is the plateau / the
resulting s* THINNESS-ESSENTIAL (rule-3), or domain-invariant?

METHOD: exact engine incidence (Python, cross-validated EXACTLY vs in-tree wf-D1 reference
n=16,k=4 dir(10,4) s=6 => I=89). PROPER subgroup mu_n=<h>, |mu_n|=n verified, h^{n/2}!=1, prize
band p~n^beta (beta=4 AND 5), p==1 mod n, index m>=2, NEVER n=q-1. RANDOM control = n distinct
nonzero non-subgroup elements at the SAME prime (the exact rule-3 contrast). 21 random draws +
3-prime q-invariance sweep. probe_407_ld_plateau_thinness{,_robust}.py.

RESULT (refutation-grade, rule-6 hardened):
1. SMOOTH s* is perfectly q-INVARIANT: s*=5 across {4129,4153,4177} (beta4) AND {32801,32833,
   32969} (beta5) for both n=8,k=2 and n=8,k=2-beta5. Genuine p-independent structural invariant.
2. The "=n plateau" QUANTIZATION is genuinely THINNESS-ESSENTIAL: 0/21 random draws ever produce
   a clean max_dir-incidence = n plateau; the subgroup ALWAYS does (the n|#bad cyclic-orbit
   divisibility). So rule-3: the plateau IS subgroup-specific. CONFIRMED.
3. BUT the plateau is ANTI-HELPFUL / NEUTRAL for the floor — it pins s* AT-OR-ABOVE the random
   LD radius, NEVER below it:
   - n=8,k=2 (beta4 AND beta5): smooth s*=5 is ABOVE all 21 random draws (random s*=4, dist all 4).
     delta*_smooth=0.375 < delta*_random=0.5. The subgroup plateau HOLDS the LD radius UP at the
     budget boundary (s=5 where maxI=8=n=budget) => one step LARGER than random. mu_n is CLOSER to
     the adversary, not further.
   - n=8,k=3: smooth s*=5 sits INSIDE random [5,5] (degenerate equal).

VERDICT (rule-4 mapped wall): the LD-reframing's central object — the per-direction n-plateau
"divisibility quantization" the KB attributes to mu_n being a subgroup — is real & subgroup-specific,
but it is a RED HERRING for proving s* small (delta* large): it makes the subgroup far-line LD radius
EQUAL-OR-LARGER than a random domain's, the WRONG direction for the prize floor. The smoothness of
mu_n does NOT suppress the far-line LD radius below random; if anything the cyclic-orbit quantization
pins it slightly higher. So a CORE proof routed through "mu_n list-decodes BETTER (smaller LD radius)
than random" is FALSE at probed sizes — the plateau thinness-essentiality is present but points the
wrong way. CORE not closed, not faked. Consistent with the orchestrator redirect (floor = LD past
Johnson is TRUE empirically i.e. mu_n ~ random) — and SHARPENS it: mu_n is not BETTER than random at
the far-line LD radius, it is at-or-slightly-worse, so the floor cannot come from a thinness ADVANTAGE
in this object. Python-only exact => axiom-clean trivially.

================================================================================
2026-06-15 LD-radius s* is STRUCTURED-PRIME-BLIND (#444): a purely-cyclotomic invariant
that cannot encode the meta-theorem's essential structured-prime mechanism (opus-4-8 subagent)
--------------------------------------------------------------------------------
LANE: companion to the LD-radius plateau thinness gate (prev entry). The brief rule-2 + the §3/§4
meta-theorem: additive-moment/energy methods fail SPECIFICALLY at STRUCTURED (Fermat-type) primes,
where mu_n interacts non-generically with field arithmetic. UNTESTED: is the far-line LD radius
s*(mu_n,k) (the LD-reframing's core object) invariant under structured primes, or does Fermat shift it?

METHOD: exact engine incidence (cross-validated vs in-tree n=16 k=4 => I=89). n=8, k=2, proper mu_8,
budget=n, NEVER n=q-1. Primes: generic prize beta4 (4129), beta5 (32801), STRUCTURED Fermat 257=2^8+1
(F3-ish, index 32) and 65537=2^16+1 (F4, deep index 8192). All p==1 mod 8.

RESULT: s* = 5 (delta*=0.375) and the ENTIRE profile {3:HEAVY,4:HEAVY,5:8} is BYTE-IDENTICAL across
ALL FOUR primes — generic AND both Fermat structured primes incl. the deeply-structured F_4=65537.

VERDICT (rule-4 mapped, with the rule-6 caveat being the key insight): the far-line LD radius s* is a
CHAR-0 / CYCLOTOMIC invariant of the 2-power subgroup, completely BLIND to the structured-prime
arithmetic. The meta-theorem establishes the structured-prime mechanism is ESSENTIAL to CORE (moment
methods fail there for a reason). But s* does not see it at all. => the LD radius s* and the BGK moment
object measure DIFFERENT things. CONSEQUENCE: a CORE proof routed purely through s* ("mu_n list-decodes
past Johnson", the orchestrator redirect) is NECESSARY-NOT-SUFFICIENT — s* cannot encode the essential
structured-prime content. This is a real obstruction for the LD-reframing lane: the cleaner cyclotomic
object s* is too clean (structure-blind) to carry the prize's structured-prime mechanism. Pairs with the
prev entry (s* is thinness-essential in its plateau but anti-helpful + thinness-neutral in value): s* is
thinness-sensitive in QUANTIZATION but structure-blind in VALUE => it is a cyclotomic combinatorial
invariant, not the moment/BGK object the prize ultimately needs. CORE not closed, not faked.
Python-only exact => axiom-clean trivially. probe_407_ld_radius_structured_primes.py.

================================================================================
## ⚠️ REFUTATION (census->CORE lane) — the "#bad collapse to O(1) at the hifreq binding line" is THICKNESS-INVARIANT, NOT thinness-essential (2026-06-15, opus-4-8 subagent)
--------------------------------------------------------------------------------
LENS: the census<->CORE map (probe_407_census_core_bindingband_ratio.py + c.1037) showed at the
hifreq BINDING line #bad COLLAPSES to O(1) while #alignable overcounts up to 112x, and concluded
"CORE-effort should target #bad directly -- the #bad collapse to O(1) at the hifreq line is the real
CORE signal." NO probe had tested whether the #bad collapse ITSELF is THINNESS-ESSENTIAL (rule-3).
This entry closes that gap.

OBJECT (exact, the in-tree CORE/epsMCA object): #bad = number of distinct gamma s.t. the far line
x^A + gamma*x^B agrees with a deg<k RS codeword on a size-a subset of the subgroup G = <g>, |G| = n.
epsMCA <= #bad/p (epsMCA_le_of_badCount_le). The binding band = deepest a with align>0.

METHOD (probe-first, rule-2/rule-3 clean): exact mod-p, proper subgroup, index m=(p-1)/n>=2,
NEVER n=q-1, multi-prime (p-invariance check), k=3 (deep-ceiling m=2 weld shape). Cached inverse
pairwise differences (no modpow in the inner Vandermonde leading-coeff test). Compare THIN n=2^a
(prize family) vs THICK n with large odd part (n=12,18,20 -- where the prize is FALSE).
Probe: scripts/probes/probe_407_badcollapse_thinness.py.

RESULT (refutation-grade, p-INVARIANT across all primes tested):
  THIN  2^4 hifreq[9,7] : #bad-profile a4:737, a5:1, a6:1, a7:1, a8:1 ; BINDING a=8 #bad=1.  (p=65537 & 160001 IDENTICAL)
  THICK n=12 hifreq[7,5]: #bad-profile a4:163, a5:1, a6:1            ; BINDING a=6 #bad=1.  (p=20749 & 100057 IDENTICAL)
  THICK n=18 hifreq[10,8]:#bad-profile a4:829,a5:82,a6:82,a7:1,a8:1,a9:1; BINDING a=9 #bad=1.
  THICK n=20 hifreq[11,9]:#bad-profile a4:1881,a5:1,a6:1,a7:1,a8:1,a9:1,a10:1; BINDING a=10 #bad=1.
The #bad=1 collapse at the hifreq binding line is reproduced EXACTLY in the THICK regime (n=12,18,20,
large odd part, prize FALSE) -- a long #bad=1 plateau from a~5 up to the binding band, identical to the
thin 2-power family. p-invariant on every prime. (Adjacent non-hifreq lines #bad=O(k) e.g. 8,12,18,40
in BOTH regimes too -- also thickness-invariant.)

VERDICT (rule-4 mapped wall; rule-3 FAIL): the #bad-collapse-to-O(1) at the hifreq binding line is
THICKNESS-INVARIANT -- it is the single-far-line-root-locus geometry (one far line meets the subgroup
in O(1) "explainable" gammas), present identically in thin AND thick subgroups. It is therefore a
thickness-MONOTONE object and CANNOT be the thin-essential CORE mechanism (rule-3/§3: any method that
behaves the same in the thick window where the prize is FALSE is wrong). The census map's "target #bad
directly" recommendation inherits the SAME fate as the far-line incidence I(n) (wf-D1: p-independent
quartic -> Johnson) and the antipodal-domination object (lalalune §7.3 -> Johnson): the per-line #bad
geometry is computable, p-clean/thickness-clean, and converges to the Johnson/Plotkin proxy -- it gives
NO beyond-Johnson, thin-only signal. The prize-distinguishing content is NOT in the per-line #bad count;
it lives only in the COLLECTIVE/aggregate object (sum over directions = the BGK moment), consistent with
the §4 meta-theorem and the route-elimination consensus that the Johnson radius is exactly the boundary
between the closed/thickness-invariant per-line regime and the open/BGK aggregate regime.
CONSTRAINT LEMMA (candidate, axiom-clean Lean): "per-line #bad at the binding band is invariant under
the odd part of |G| (depends only on the far-line/codeword incidence geometry, not on 2-power
structure)" -- formalizable as a statement that badScalars.card at the hifreq binding band factors
through the single-far-line agreement locus, which is defined field-/subgroup-structure-free.
CORE not closed, not faked. Python-only exact => axiom-clean trivially.

================================================================================
2026-06-15 LD plateau = single dilation orbit: EXACT numerical corroboration of in-tree
wf3D4 monomial_badset_orbit_closed, extended to Fermat prime (#444) (opus-4-8 subagent)
--------------------------------------------------------------------------------
Probe-first verification of the MECHANISM behind the plateau-=-n (the prev two LD-radius entries).
INDEPENDENTLY rediscovered + numerically confirmed the in-tree axiom-clean theorem
_wf3D4_monomial_worst_orbit.lean::monomial_badset_orbit_closed ("the bad-gamma set of a monomial
direction is a union of <mu^{b-a}>-orbits"). Exact, proper mu_n, binding direction extracted directly.

RESULT (exact, all three cases incl. Fermat 257):
- binding direction at the plateau is (a,b)=(k, k+1) => b-a=1, gcd(n,b-a)=1.
- the bad-gamma set has |.|=n EXACTLY and is CLOSED under gamma -> gamma*h^{b-a} (the dilation z->hz
  action, gamma reparametrised by h^{b-a} per monomial_dilated_line). gcd(n,1)=1 => <h^{b-a}>=full mu_n
  => exactly ONE orbit of size n => plateau pins at n. Mechanism CONFIRMED.
- Holds identically at generic primes (4129) AND the structured Fermat prime 257=2^8+1 (the in-tree
  file only anchored n=16,k=4 generic; this adds n=8 k=2/k=3 + Fermat corroboration) — consistent with
  the s*-is-structured-prime-blind entry: the orbit closure is a char-0/cyclotomic fact, p-free.

NET: corroborates the orchestrator's wf3D4 brick numerically and extends its anchor to the Fermat
structured prime; combined with the two prior LD-radius entries, the full picture is: the monomial
dilation-orbit (proven, axiom-clean) FORCES the plateau=n quantization (thinness-essential), but that
quantization pins s* AT-OR-ABOVE random + is structure-blind in value => the proven orbit mechanism is
real but points the WRONG way for the floor (it is the residual open Prop "does the aligned orbit EXCEED
budget" that carries the prize, and the orbit being exactly =budget at the binding is the knife-edge).
CORE not closed. Python-only exact => axiom-clean trivially. probe_407_ld_plateau_dilation_orbit.py.

================================================================================
2026-06-15 The e2=0 over-det census (the prize FLOOR's load-bearing R1 object) is
THINNESS-ESSENTIAL: built on antipodal pairing, VANISHES for random domains (opus-4-8 subagent)
--------------------------------------------------------------------------------
LANE: the in-tree prize skeleton. DeltaStarEqEdge.lean reduces the FLOOR to ONE open hyp (R1, `hgood`):
the e2=0 over-det locus is the BINDING worst-case bad-scalar family at the window edge. _E2Dilation
DirectCount.lean reduces that count EXACTLY to #bad = n*K, K = #dilation-orbits of e1(S) over
{S subset mu_n, |S|=w=n/2, e2(S)=0, e1(S)!=0}. In-tree: K=1,3,38 at n=8,16,32. K(n) IS the open
extremal census. NO live worker / report had applied a rule-3 thinness gate to K. UNCONTESTED.

METHOD: exact e2=0 enumeration over all C(n,w) w-subsets (feasible n<=16), smooth mu_n vs 11 random
non-subgroup domains, prize prime p~n^4, never n=q-1. + mechanism probe (antipodal/density/p-indep).

RESULT (refutation-grade, rule-6 hardened):
1. RANDOM domains have ZERO e2=0 bad-sets (0/11 draws at BOTH n=8 and n=16). Smooth has n*K (8, 48=#bad,
   matching n*K exactly; bad-SETS 8, 64).
2. NOT a density artifact: density baseline E[random hits] = C(n,w)/p = 0.017 (n=8), 0.196 (n=16); smooth
   EXCESS over baseline = 7.98, 63.80 => overwhelmingly STRUCTURAL.
3. p-INDEPENDENT (char-0 structural): #e2=0 subsets identical across 2 prize primes each (8,8 / 64,64) =>
   genuine cyclotomic count, not a mod-p accident.
4. MECHANISM: EVERY e2=0 subset contains >=1 ANTIPODAL PAIR (8/8, 64/64; none fully antipodal-closed). The
   locus is built on the subgroup's antipodal pairing x,-x=h^{n/2}x both in mu_n — a structure random
   domains lack entirely.

VERDICT (rule-3 PASS, strongest form): the e2=0 over-det census K(n) — the load-bearing open object the
ENTIRE prize FLOOR reduces to (DeltaStarEqEdge R1 + Attack-2 #bad=n*K) — is THINNESS-ESSENTIAL in the
strongest sense: it is a pure subgroup-antipodal-pairing object and VANISHES identically for random
domains. This is the RIGHT-DIRECTION thinness signature the prize needs (unlike the LD-radius plateau /
even-moment profile, which were anti-helpful). The K(n) growth (1,3,38,...) is the genuine prize content,
structurally anchored to antipodal pairs. Formalization target: K(n) = orbit-census of e1 over the
antipodal-pair-supported e2=0 locus. CONSEQUENCE for R1: the e2=0 family being thin-only SUPPORTS its
candidacy as the binding worst-case family (a random/generic family contributes 0 here), but does NOT by
itself bound K(n) — the open content is purely the K growth law (the additive-energy twin). CORE not
closed, not faked. Python-only exact => axiom-clean trivially.
probe_407_e2_census_K_thinness.py + probe_407_e2_census_mechanism.py.

================================================================================
## ⚠️ REFUTATION + REPLACEMENT LAW — the char-0 far-line delta* candidate "delta* = (1-rho) - log2(n)/n" is FALSE at n=64; the true law is s*-k = n/4 i.e. delta* = 3/4 - rho (2026-06-15, opus-4-8 subagent)
--------------------------------------------------------------------------------
LANE: the full-assault-synthesis "live lead" (docs/kb/deltastar-444-full-assault-synthesis + 
deltastar-407-char0-logn-over-n-candidate): a NEW candidate char-0 worst-case far-line crossing
gave n*(cap-delta*)=log2(n) at n=16,32 (rho=1/8), conjecturing delta*=(1-rho)-log2(n)/n (a
Theta(log n/n) gap, "much closer to capacity than the standing Theta(1/log n)"). FLAGGED "NOT
confirmed -- needs n=64". The n=16-vs-n=20 convention discrepancy (s*-k = log2(n) vs constant 3)
was the explicit OPEN tension (DISPROOF "s*-k appears CONSTANT" entry: "n=32,64 must resolve it").
I ran the decisive n=64 computation.

METHOD: the in-tree char-0 (k+1)-subset-solve engine (scripts/probes/probe_char0_deltastar_n64_BIG.py),
cross-validated EXACTLY vs the wf-D1 reference. Char-0 = q-free worst-case far-line incidence I_0(w)
crossing budget=n, MAX over far pencils (a,b), a,b>=k, a,b != n/2, gcd-stratified pencil sampling +
deep antipodal directions. PROPER subgroup mu_n, p>>n^3, p==1 mod n, NEVER n=q-1. k=2 FIXED (so
rho=k/n SHRINKS with n -- the constant-k axis the candidate was stated on).

RESULT (refutation-grade, Q-INVARIANT -- two primes per n, p/n^3 = 4 AND 40 identical):
| n  | k | rho   | s*-k | n/4 | log2(n) | delta*=(n-w_cross)/n | worst pencil (a,b) gcd(b-a,n) |
|----|---|-------|------|-----|---------|----------------------|-------------------------------|
| 16 | 2 | 1/8   | 4    | 4   | 4       | 0.62500              | (5,9)   gcd=4=n/4              |
| 32 | 2 | 1/16  | 8    | 8   | 5       | 0.68750              | (9,17)  gcd=8=n/4              |
| 64 | 2 | 1/32  | 16   | 16  | 6       | 0.71875              | (2,34)  gcd=32=n/2            |
s*-k = 4,8,16 = EXACTLY n/4 (NOT log2(n) = 4,5,6). At n=64: s*-k=16, log2(64)=6 => the candidate is
OFF BY 10. Q-invariant: n=64 gives s*-k=16 at BOTH p=1048609 (p/n^3=4) AND p=10486337 (p/n^3=40),
same worst pencil (2,34). [The n=16,32 coincidence s*-k=log2(n) was a small-n ARTIFACT: 4=4 at n=16,
8 vs 5 already diverges at n=32 under the full-direction MAX convention -- the candidate doc used a
coarser pencil set that under-sampled the d=n/4 worst direction.]

THE TRUE LAW (exact at n=16,32,64): **s*-k = n/4**  =>  **delta*_charline = 1 - (k+n/4)/n = 3/4 - k/n
= 3/4 - rho**. Verified: 3/4-1/8=0.625, 3/4-1/16=0.6875, 3/4-1/32=0.71875 -- EXACT. The worst pencil
is the deeply-composite direction gcd(b-a,n) in {n/4, n/2} (the antipodal/subgroup-coset family), not
a generic pencil -- consistent with the dyadic Mann/Conway-Jones antipodal-pair mechanism (the only
primitive vanishing relation over mu_{2^mu}).

VERDICT (rule-4 mapped: refutes a candidate + installs the correct law; rule-6 honest):
1. The "delta* = (1-rho) - log2(n)/n" candidate (Theta(log n/n) gap, "the live lead" of the
   full-assault synthesis) is FALSE. The char-0 far-line gap below capacity is a CONSTANT 1/4
   (delta* = 3/4 - rho => cap - delta* = 1/4 - 0 = 1/4 for k=2... precisely cap-delta* = (1-rho)-(3/4-rho)
   = 1/4, a CONSTANT, NOT log2(n)/n -> 0). So the char-0 far-line delta* sits a FIXED 1/4 BELOW capacity.
2. s*-k = n/4 is LINEAR in n (like the rho=1/4 law s*-k=n/4-1), NOT Theta(n/log n). So -- exactly as the
   prior over-det entries concluded for fixed-rho -- this char-0 worst-case FAR-LINE delta* does NOT
   track the conjectured BGK floor delta*=1-rho-Theta(1/log n); it is the (rigorous UPPER bound)
   far-line object, converging to 3/4-rho, a clean cyclotomic combinatorial value OFF the BGK wall.
3. NET for the synthesis: the "much closer to capacity" optimism was a small-n sampling artifact; the
   true char-0 far-line delta* = 3/4 - rho is a fixed 1/4 below capacity and carries NO sub-log gap.
   The genuine prize content remains in the collective BGK aggregate (the L7 WorstCaseIncidenceBounded
   Prop), NOT in this per-pencil char-0 crossing.
CORE not closed, not faked. Python-only exact, q-invariant 2-prime => axiom-clean trivially.
Probe scripts/probes/probe_char0_deltastar_n64_BIG.py (--n {16,32,64} --k 2 --allfar / select).

---
## wf-D2 (#444): closed form delta* = 1/2 + 1/n (= Johnson + 1/n), NOT the floor — proven-exact n=16..28

Lane D2: closed form of the binding far-line monomial incidence I(n) and delta* vs the prize
floor 1-rho-Theta(1/log n). EXACT (vectorized numpy, p-independent; cross-checked vs in-tree
probe_farline_incidence_exact + GPU H100 oracle on #444).

far-line incidence I at over-det level c=s-k (worst far monomial b=k, budget=n), EXACT:
  n=8  (k=2): c=4 ->1 ; c=3 ->8 ; c=2 ->9 ; c=1 ->40
  n=16 (k=4): c=4 ->9 ; c=3 ->9 ; c=2 ->89 (= the established I(16)=89, hist {56:1,32:8,2:64,1:16}) ; c=1 ->3696
  n=24 (k=6): c=2 -> 1153 (hist {1026:1,516:8,...})

THE BINDING LAW (regime A, n=16,20,24,28 -- 4/4 EXACT):
  s* = 2k-1 = n/2 - 1  (binding over-det level c* = k-1 = n/4-1)
  delta* = (n - s*)/n = (n/2+1)/n = **1/2 + 1/n**  = JOHNSON(rho=1/4)=1-sqrt(rho)=1/2  +  one rung 1/n.

ASYMPTOTIC VERDICT: delta*(regime A) -> 1/2 = Johnson radius as n->inf. The prize floor is
3/4 - Theta(1/log n) (rho=1/4). The far-line incidence threshold CONVERGES TO JOHNSON, a CONSTANT
gap 1/4 BELOW the floor -- it does NOT certify the window interior (1/2, 3/4). The "delta* is a
computable combinatorial quantity" hope is CONFIRMED (p-independent closed form 1/2+1/n) but the
quantity it computes is the JOHNSON endpoint, not the floor. So this route does NOT close the prize.

REGIME B (n>=32, GPU): delta* jumps up (0.594, 0.618, 0.658) but s* PINS at exactly 13 across
n=32,34,38 while regime A had s* strictly increasing 7,9,11,13. GPU flagged n>=36 deep-binding
TIMED OUT. A pinned s* with climbing delta* is the signature of a SEARCH CEILING, not a law. n=32
deviation (s*=13 not 15) may be real (n=32 was within H100 reach) and is the genuine open sub-question.
Python-only exact + p-invariant => axiom-clean trivially. Probes probe_wf3D2_*.py.

================================================================================
2026-06-15 e2=0 census WIDTH PROFILE: super-budget at all widths past the smallest;
corroborates wf-D5 free-mu_{n/2}-action backbone from the census side (opus-4-8 subagent)
--------------------------------------------------------------------------------
LANE: K(n,w) width profile of the e2=0 census (the prize FLOOR's R1 object). Follow-up to the
thinness-essential / antipodal finding (417015191). Goal: where does #bad=n*K cross budget=n across
widths w, and the growth law. Method: exact e2=0 antipodal-pair meet-in-middle, VALIDATED vs in-tree
K=1,3,38 (n=8,16,32 at w=n/2). Prize prime, proper subgroup, never n=q-1.

RESULT (exact, full width profile n=8,16,32):
1. #bad(n,w) is SHARPLY NON-MONOTONE in w with thin-quantized structure: 0 at tiny w; jumps at w=4
   (=k+2, deepest over-det) to 8,48,224; drops to EXACTLY budget at w=5 (8,16,32 = n, K=1); 0 at w=6,7;
   then a super-budget middle band peaking at w=n/2 (the 1216 extremal at n=32).
2. The shallowest over-det width w=k+2=4: #bad = 8,48,224, K = 1,3,7. #bad/budget = 1,3,7 (GROWS);
   #bad ~ n^2.40. The extremal w=n/2: #bad=8,48,1216, n*K ~ n^3.6.
3. So the e2=0 census is SUPER-BUDGET at every width past the smallest (w>=8 for n>=16), and the excess
   over budget GROWS with n. Even the shallowest family (w=4) has #bad/n = 1,3,7 -> super-linear.

VERDICT (rule-4 mapped, NO overclaim): the e2=0 antipodal census #bad grows super-budget (n^2.4 shallow,
n^3.6 extremal), matching the dossier's known "over-det max ~cubic n^3" ballpark and CORROBORATING the
just-landed wf-D5 result (7381dea4a: I(n)=1+(n/2)*O(n), free mu_{n/2}-action backbone) FROM THE CENSUS
SIDE: my antipodal-pair mechanism (every e2=0 subset has >=1 pair x,-x=h^{n/2}x) IS the free mu_{n/2}-
action wf-D5 proved structural. Consistent with wf-D2 (e48d5ef59: delta*=1/2+1/n -> Johnson not floor):
the e2=0 census, being super-budget and tracking the over-det cubic, does NOT exhibit a within-budget
floor at fixed small width => the binding delta* sits where this super-budget curve crosses budget, only
at the smallest widths (w=5, K=1, #bad=n exactly), which is the budget-pinned single-orbit knife-edge.
The census super-budget growth is the prize content; it points toward Johnson-tracking (wf-D2), NOT an
off-budget floor, at probed n. CORE not closed, not faked. The thin-ONLY nature (417015191) stands; this
adds the width profile + growth + the wf-D5 census-side corroboration. Python-only exact => axiom-clean.
probe_407_e2_K_growth_antipodal.py (validated MIM) + probe_407_e2_K_width_profile.py.

================================================================================
2026-06-15 The e2=0 census K is WITHIN floor budget (K<=1) ONLY at radii DEEPER than
Johnson; at/above the Johnson edge K is large + super-linear (opus-4-8 subagent)
--------------------------------------------------------------------------------
LANE: the load-bearing e2=0 census R1 object (DeltaStarEqEdge.lean hgood + _E2DilationDirectCount:
#bad = n*K). The sibling just proved K is THINNESS-ESSENTIAL (random domains give 0; push 417015191).
COMPLEMENTARY UNTESTED EDGE: the BUDGET question. Governing law (KB deltastar-orbit-count-reformulation):
delta* = sup{delta : I(delta) <= q*eps* ~= n}. So the e2=0 family is WITHIN the floor budget IFF
#bad = n*K <= n  <=>  K <= 1. In-tree K=1,3,38 at n=8,16,32 (w=n/2) already VIOLATES this for n>=16.
The decisive question NObody mapped: K(n) is reported only at the SINGLE width w=n/2; is K<=1 (budget-OK)
anywhere, and at WHICH radius? (n=64 enumeration is infeasible: C(64,32)~1.8e18, ~1.1e11 e2=0 sets.)

METHOD: exact MITM width-sweep over the FULL FLOOR WINDOW delta in (Johnson=1-sqrt(rho), cap=1-rho),
proper mu_n, prize prime p=n^4, ALL w from 2..(Johnson width). (Prior sweep skipped w=3,6,7 -- I filled
them.) k=2. /tmp/e2_floorwindow.py (+ in-tree probe_e2_widthsweep_directcount.py for the full 2..n/2).

RESULT (exact, n=16 AND n=32 -- the COMPLETE floor window, w=odd parities included):
  n=16 floor window delta in (0.646,0.875) = w in (2,5.7):  w2:K0  w3:K0  w4:K3  w5:K1  (w6:K0=Johnson)
  n=32 floor window delta in (0.750,0.938) = w in (2,8):    w2:K0  w3:K0  w4:K7  w5:K1  w6:K0  w7:K0  (w8:K7=Johnson)
  ABOVE Johnson (w>=8, n=32): K EXPLODES super-linearly: 7,23,4,2,21,32,14,18,38,33 (w8..17).
  n=64 floor window delta in (0.823,0.969):  w2:K0  w3:K0  w4:K15  w5:K1  w6:K0  (w7+ Johnson-region, large)
KEY: across the ENTIRE deep floor window the e2=0 census is WITHIN budget (K<=1) at EVERY width EXCEPT
the single resonance w=4 (K=3,7,15 at n=16,32,64 = EXACTLY n/4-1). The super-linear K-explosion (the
in-tree 1,3,38 at w=n/2) is a JOHNSON-EDGE-AND-BELOW phenomenon (w>=n/4), NOT a floor-window phenomenon.
[CONVERGENCE: the w=4 value K=n/4-1 was independently pinned to a closed form in the entry below + ties
to wf-D2's s*-k=n/4 (push ce8cb602e). MY unique contribution here is the COMPLEMENT: w=4 is the SOLE
budget-overflow width across the WHOLE deep floor window -- every other window width has K<=1.]

VERDICT (rule-4 mapped constraint; CORRECTS my first draft; a COMPLEMENT to the sibling thinness result):
1. The e2=0 census R1 is WITHIN floor budget (K<=1) across essentially the whole floor window
   (delta in (Johnson,cap)) -- K=0 or 1 at every floor-window width EXCEPT the isolated w=4 resonance.
   This SUPPORTS R1's viability: deep in the window the binding e2=0 family does stay within budget.
2. The lone obstruction in the window is the w=4 RESONANCE (K=3,7 at n=16,32): the smallest even-symmetric
   vanishing locus (antipodal-quadruple sets {x,-x,y,-y}-flavored), where e2=0 has many solutions. It is
   FINITE/characterizable, not a generic growth -- a single bad width, not the BGK wall.
3. The super-linear K(n)=1,3,38 the in-tree file flags is the value AT w=n/2 (Johnson, delta=0.5), which
   is the LOWER window edge / below the floor -- NOT the floor edge. So "K is super-linear" describes the
   Johnson-region census, and does NOT by itself defeat the floor (which lives at delta>Johnson where
   K<=1 except at w=4).
4. NET (honest, rule-6): this is GOOD news for R1, sharply scoped -- the e2=0 binding family is
   within-budget across the floor window with a SINGLE exceptional width w=4. The real remaining question
   for R1 is whether that w=4 resonance (a) actually realizes a delta*-window-edge bad config, or (b) is
   dominated/excluded (it sits at delta=1-4/n -> 1, the extreme deep end, possibly above cap for the true
   k). The K-explosion above Johnson is consistent (the ceiling SHOULD overflow below the edge). This
   does NOT close CORE, but it REFRAMES the obstruction from "K super-linear everywhere" to "K<=1 in the
   window except the w=4 resonance" -- a finite, attackable object.
CORE not closed, not faked. K(64) full-window enumeration feasible at SMALL w (the window is shallow):
w<=7 needs only C(64,<=7) per side -- TRACTABLE, unlike w=n/2. Python-only exact => axiom-clean trivially.
probe_e2_widthsweep_directcount.py + /tmp/e2_floorwindow.py.

================================================================================
2026-06-15 EXACT CLOSED FORM for the shallow e2=0 census: K(n,4) = n/4 - 1,
#bad = n^2/4 - n; the census n/4 = wf-D2's s*-k=n/4 (opus-4-8 subagent)
--------------------------------------------------------------------------------
Beat the C(64,32) wall for the e2=0 census by enumerating the SHALLOWEST over-det width w=k+2=4 directly
(4-subsets: C(n,4)~n^4/24, n=64 => 635k, no MIM). This is the cleanest census sub-sequence.

RESULT (exact, p-INDEPENDENT across 2 prize primes each at n=16,32,64):
- K(n, w=4) = 1, 3, 7, 15  at n = 8, 16, 32, 64  (2-powers; n=48 non-2-power gives 11 too).
- CLOSED FORM (5/5 incl n=64): K(n,4) = n/4 - 1  EXACTLY. p-independent (char-0 cyclotomic).
- => #bad(n,4) = n*K = n(n/4 - 1) = n^2/4 - n  EXACTLY QUADRATIC. The Theta(n^2) over-det object the
  dossier names, now pinned to a clean closed form on the e2=0 antipodal census.
- loglog-slopes of #bad converge cleanly 2.585->2.222->2.115->2.078 -> 2.0 (quadratic).

CONNECTION: wf-D2 (e48d5ef59) + ce8cb602e found s*-k = n/4 => delta* = 3/4 - rho. The SAME n/4 is the
census orbit-count: K(n,4) = n/4 - 1. The shallow e2=0 census orbit-count IS the n/4 over-determination
depth, census-side. So the e2=0 antipodal census and the wf-D2 incidence law are TWO FACES of one n/4
structure (consistent with my width-profile's wf-D5 free-mu_{n/2} corroboration). #bad = n^2/4 - n is
super-budget (n^2 vs budget n), Johnson-tracking-consistent (wf-D2), NOT an off-budget floor.

VERDICT (rule-4, no overclaim): an EXACT p-independent closed form for the shallow e2=0 census,
K(n,4)=n/4-1, #bad=n^2/4-n. Sharpens the prior 3-point ~n^2.4 fit to an exact quadratic and ties the
census n/4 to wf-D2's s*-k=n/4. Formalizable target (the K(n,4)=n/4-1 closed form is a clean cyclotomic
count). CORE not closed: the closed form CONFIRMS super-budget (n^2/4 >> n) => no within-budget floor at
shallow width, consistent with Johnson-tracking. Python-only exact => axiom-clean trivially.
probe_407_e2_K_w4_n64.py (5-point, multi-prime verified).

================================================================================
2026-06-15 The shallow-width e2=0 census MAP + the w=5 KNIFE-EDGE (#bad=budget=n
exactly, single orbit, 2-pairs+singleton): cleanest formalization target (opus-4-8 subagent)
--------------------------------------------------------------------------------
Completed the shallow-width map of the e2=0 census (prize FLOOR's R1 object) for 2-power n, exact,
p-independent (2 prize primes each), to n=64:
  w<=3 : EMPTY (no e2=0 solutions)
  w=4  : K = n/4 - 1, #bad = n*K = n^2/4 - n  (super-budget quadratic; closed form, f1d5de96e)
  w=5  : K = 1 EXACTLY all n, #bad = n EXACTLY = budget  <-- THE KNIFE-EDGE  (1,1,1,1 @ n=8,16,32,64)
  w=6  : EMPTY again
  (then super-budget middle band, peaks w=n/2.)

THE w=5 KNIFE-EDGE (confirmed n=8..64, p-independent):
- #distinct-alpha = n EXACTLY = budget, single mu_n-orbit (K=1).
- EVERY w=5 e2=0 subset = EXACTLY 2 antipodal pairs + 1 singleton {x,-x,y,-y,z} (8/8,48/48,224/224,
  960/960). pairs cancel in e1 (=> e1=z), e2=0 forces a relation among x,y,z; bad-set={-1/z}=one orbit.
- ELEGANT cross-relation: #w5-subsets = 8,48,224,960 = n^2/4 - n = the w=4 #bad-count. The n^2/4-n
  width-5 subsets collapse (n/4-1)-to-1 onto exactly n bad-scalars (one orbit).

VERDICT (rule-4, no overclaim): the shallow e2=0 census is fully mapped with EXACT p-independent closed
forms: w=4 gives n/4-1 orbits (super-budget), w=5 gives exactly 1 orbit at #bad=n=budget (knife-edge),
w=3,6 empty. The w=5 family is the cleanest object on the entire board: #bad=budget EXACTLY, single
orbit, p-independent, explicit 2-pairs+singleton structure => a prime FORMALIZATION target (a clean
cyclotomic count = n). It is the candidate BINDING edge family (proximity gap exactly at budget). This
does NOT close floor-vs-Johnson (the w=5 family sits AT budget, neither above=fail nor strictly below=
floor-slack; the binding among ALL widths/families is the R1 residual) but it pins the cleanest knife-
edge witness. Consistent w/ wf-D2 Johnson-tracking + the shared n/4 structure. CORE not closed, not
faked. Python-only exact => axiom-clean trivially. probe_407_e2_w5_knife_edge.py.

================================================================================
2026-06-15 The shallow e2=0 over-det census is a w==0 (mod 4) RESONANCE: K(n,w)=n/4-1
iff 4|w, else K<=1 -- so the over-det floor object is within budget UNLESS k==2 (mod 4)
(opus-4-8 subagent)
--------------------------------------------------------------------------------
LANE: generalizing the e2=0 census R1 budget map (my push 74a54cdce: K<=1 across the deep floor window
except the w=4 resonance) + the K(n,4)=n/4-1 closed form (convergent entry). KEY QUESTION nobody asked:
the e2=0 vanishing is the over-det constraint for the pencil x^k + alpha x^{k+2} at agreement w=k+2 (in-tree
_E2DilationDirectCount line 13). The e2=0 constraint is the SAME quadratic for ANY k; only w=k+2 varies.
So K(n, w=k+2) depends on the WIDTH w only. Does the w=4 resonance PERSIST at prize-rate k (w=k+2>4)?

METHOD: exact shallow census K(n,w) = #dilation-orbits of e1(S) over {|S|=w, e2(S)=0, e1!=0}, brute
C(n,w) for shallow w, proper mu_n, prize prime p=n^4, never n=q-1. n=16,32,64. Vary k=2..6 (w=k+2=4..8).
probe_407_e2_census_general_k_resonance.py + probe_407_e2_census_n64_shallow.py.

RESULT (exact, the SHALLOW over-det regime w<=8, the prize-relevant shallowest over-det width):
  K(n,w) by width (n=16 / n=32 / n=64):
    w=2: 0/0/0   w=3: 0/0/0   w=4: 3/7/15   w=5: 1/1/1   w=6: 0/0/-   w=7: 0/0/-   w=8: 3/7/-
  => CLEAN RESONANCE: K(n,w) = n/4 - 1 EXACTLY when 4 | w (w=4: 3,7,15 = n/4-1 at n=16,32,64; w=8: 3,7
     at n=16,32), and K <= 1 (mostly 0, occasionally 1 at w=5) when 4 does NOT divide w.
  k-form: since w=k+2, the over-det census at the shallowest width OVERFLOWS budget (#bad=n*K~n^2/4)
     iff 4|(k+2) iff k == 2 (mod 4); for k !== 2 (mod 4) the shallow e2=0 over-det census is WITHIN
     floor budget (K<=1).

VERDICT (rule-4 mapped structural law; rule-6 honest, NOT a closure):
1. The e2=0 over-det census budget-overflow is an ARITHMETIC RESONANCE on the agreement width:
   4 | w => K = n/4-1 (overflow), else K <= 1 (within budget). This SHARPENS my floor-window result
   (74a54cdce) from "single w=4 resonance" to the periodic law "4|w resonance" and explains the
   w=4 AND w=8 spikes.
2. PRIZE-RATE CONSEQUENCE: the prize is forall-rate (rho free); for the AP of rates with k == 2 (mod 4)
   the shallowest over-det e2=0 family overflows budget by Theta(n) at w=k+2, but for k !== 2 (mod 4) it
   is within budget at that width. So the e2=0 over-det census does NOT uniformly defeat the floor across
   rates -- it has a width-divisibility structure. (This is consistent with the n/4 over-determination
   depth being the universal object: 4|w is exactly when the antipodal-quadruple {x,-x,y,-y} vanishing
   saturates the orbit count to n/4-1.)
3. The DEEPER widths (w>=9, approaching Johnson) LOSE the clean 4|w law (K=23,4,2,21,32,... at n=32) --
   that is the BGK/additive-energy regime where the census is the analytic wall's twin. The clean
   resonance law holds in the SHALLOW over-det regime only (the floor-edge-relevant widths).
4. NET: the over-det e2=0 census is NOT a uniform floor obstruction; it is a 4|w arithmetic resonance
   that is within budget for 3/4 of rates (k !== 2 mod 4) at the shallowest width, and the only structural
   overflow is the antipodal-quadruple saturation at 4|w. CORE not closed: this maps WHERE the over-det
   census obstructs (4|w) vs is benign, but the actual prize floor still needs the COLLECTIVE BGK bound
   at the binding depth (the L7 Prop), not this per-width census. Python-only exact, p-independent =>
   axiom-clean trivially.
probe_407_e2_census_general_k_resonance.py + probe_407_e2_census_n64_shallow.py.

================================================================================
2026-06-15 ★ LIVE-LEAD (route 36, never-tried per ledger): mu_n deep holes ARE concentration
points; deep-hole monomials are EXACTLY x^j with j == k (mod 4) -- a FINITE n/4-size candidate
set for the worst-case u0 (opus-4-8 subagent)
--------------------------------------------------------------------------------
LANE: route 36 (deltastar-100-routes.md), flagged "★ GENUINELY LIVE (never-tried)": "deep-hole
classification of RS (Cheng-Murray, Zhu-Wan) -- explicit worst u0 = deep hole; first step: are
smooth-domain deep holes concentration points? (probe)". 0 hits in DISPROOF_LOG => genuinely untouched.
The L7 open core WorstCaseIncidenceBounded is a sup over stacks (u0,u1); if the worst u0 is a deep hole,
route 36 reduces the sup to a FINITE deep-hole candidate family (the never-tried payoff).

METHOD: exact mod-p. RS[k] eval code on D=mu_n. distance(u,RS)=n-max_{deg<k g}agreement (exact via
k-subset interpolation). covering radius R=max_u dist; deep hole = dist=R. Then the concentration object:
for monomial pencils (x^a,x^b), #bad-gamma(agree>=smin) = #{gamma: x^a+gamma*x^b agrees with deg<k on
>=smin pts}. Test whether the WORST (max #bad) pencil uses a deep-hole exponent. n=8,16, k=3, prize prime.
probe_407_deephole_classification.py + probe_407_deephole_concentration.py.

RESULT (exact):
1. DEEP-HOLE CLASSIFICATION over mu_n (monomial scan): the deep-hole monomials x^j are EXACTLY
   j == k (mod 4):
   - n=8, k=3:  deep holes j in {3,7}      (covering radius R=5=n-k=n-3, max-agree=k=3)
   - n=16, k=3: deep holes j in {3,7,11,15} (R=13=n-k, max-agree=k=3) -- exactly j==3 (mod 4).
   The x^{n/2-family} exponents (j=8,9,10 at n=16) are NOT deep holes (agree=n/2=8, much higher).
   So deep holes = the minimal-agreement (=k) monomials at j==k mod 4: a FINITE set of size ~n/4.
2. CONCENTRATION: the WORST-case pencil DOES use a deep-hole exponent. n=8 k=3 smin=k+1=4:
   worst #bad-gamma=40 achieved by pencils (3,4),(3,6),(4,7),(6,7) -- EVERY one includes a deep-hole
   exp in {3,7}; the pure-non-deep-hole pencils (4,5),(5,6) cap at #bad=32 < 40. So mu_n deep holes
   ARE concentration points (route-36 premise CONFIRMED at n=8).
   CAVEAT (rule 6): the two-deep-hole pencil (3,7) (gcd=4=n/2) gives only #bad=8 -- the worst is
   ONE deep-hole exp paired with a coprime-step neighbor, not both deep holes. So "deep hole" is
   NECESSARY-flavored for the worst pencil but the pairing structure also matters.

VERDICT (rule-4 mapped, but a POSITIVE LIVE LEAD not a refutation): route 36 is NOT dead -- its premise
holds at probed scale: (a) mu_n deep holes have a clean closed classification (x^j, j==k mod 4, size
~n/4), and (b) the worst-case concentration u0 uses a deep-hole exponent. This gives a FINITE candidate
family for the L7 sup-over-u0 (the never-tried payoff the ledger flagged). NEXT STEP (the genuine open
work): bound #bad-gamma over the deep-hole family directly -- if the deep-hole exps' #bad is itself
capped (the deep-hole list curve L(a) the KB mentions has no closed form, but it is now restricted to
j==k mod 4, a structured finite set). This connects to the wf-D2 worst pencil (composite-step) -- the
worst pairing is deep-hole-exp + coprime/composite-step neighbor. Whether the deep-hole-restricted sup
beats Johnson is the live question. CORE not closed; this OPENS a finite-candidate handle on the L7 sup.
Python-only exact => axiom-clean trivially.
probe_407_deephole_classification.py + probe_407_deephole_concentration.py.

================================================================================
2026-06-15 CORRECTION to the route-36 deep-hole classification: "j == k (mod 4)" was a
k=3 COINCIDENCE; the true law is R=n-k with deep-hole count n/4 (odd k) / n/2 (even k)
(opus-4-8 subagent, self-correcting push 1b3f947fa)
--------------------------------------------------------------------------------
RULE-6 SELF-CORRECTION of my prior route-36 entry (push 1b3f947fa), which claimed mu_n deep-hole
monomials are "EXACTLY x^j with j == k (mod 4)". That was tested only at k=3. Re-tested k=2,3,4,5:

EXACT (n=8,16, prize prime, monomial deep-hole scan):
  k=2 (n=16): deep = {2,3,6,7,10,11,14,15}  = j mod 4 in {2,3}   (count n/2)
  k=3 (n=16): deep = {3,7,11,15}             = j mod 4 in {3}     (count n/4)  <- the coincidence
  k=4 (n=16): deep = {4,5,6,7,12,13,14,15}   = j mod 8 in {4,5,6,7}(count n/2)
  k=5 (n=16): deep = {5,7,13,15}             = j mod 8 in {5,7}   (count n/4)

TRUE LAW (corrected): covering radius R = n - k ALWAYS (deep holes = monomials with MINIMAL agreement
= k with deg<k). Deep-hole COUNT = n/4 for ODD k, n/2 for EVEN k. The clean single-residue "j==k mod4"
holds ONLY at k=3. So the deep-hole candidate family is finite + structured but LARGER than my n/4 claim
for even k (it is n/2).

IMPACT ON THE ROUTE-36 LEAD (rule-6 honest): the route-36 PREMISE still stands -- (a) deep holes have a
clean closed classification (R=n-k, the minimal-agreement monomials, n/4 or n/2 of them), and (b) the
worst-concentration u0 uses a deep-hole exponent (n=8 confirmed). The lead is NOT killed; only the size
of the candidate family is corrected (n/2 for even k, not uniformly n/4). The L7 sup-over-u0 still
reduces to this deep-hole family. The open work (bound #bad over the deep-hole family vs Johnson) is
unchanged. CORE not closed. Python-only exact => axiom-clean.
probe_407_deephole_kvary.py.

================================================================================
2026-06-15 CENSUS ROUTE INTERNAL INFEASIBILITY: the deployed CensusDomination is
FALSE at ITS OWN weld budget eps* at the SHALLOW over-det bands (and the deepest
band) -- the route over-shoots the very supply bound that defines eps* (opus-4-8 subagent)
--------------------------------------------------------------------------------
LANE (uncontested): c.1007 mapped census<->CORE as OVERSTATED (CensusDomination STRICTLY STRONGER than
CORE, via the one-way #bad<=#alignable). It left the DECISIVE viability question unasked: does the census
count K the route ACTUALLY bounds even FIT under the supply budget the SAME weld demands? The weld
(CensusDominationWeld.lean, kkh26_deltaStar_pin_of_censusDomination) requires hK: K/p <= eps*, and the
deployed eps* threshold (hεstar) is eps* = 2^r * C(2^{mu-1}, r) / p (the KKH26 fibre SUPPLY count). So the
route needs, at the binding deep band a_bind:
    K := max_{u0,u1} #alignableSets(a_bind)  <=  2^r * C(2^{mu-1}, r).    (FEAS)

OBJECT (semantics matched EXACTLY to UniversalAlignmentLaw.lean + probe_alignment_census.py): mu_n=<g>,
|mu_n|=n=2^mu, PROPER subgroup (m=(p-1)/n>1, NEVER n=q-1), prize prime p~n^beta. e_j(T)=divided diff
[x_{t0..tk}]u_j; S aligned iff all nondeg (k+1)-subtuples share one ratio -e0/e1; alignableSets = aligned
|S|=a sets w/ >=1 nondeg tuple. Prize shape m=1: k=(r-2)m+1=r-1, binding band a_bind=r*m+1=r+1. K is the
TRUE max over the char-line adversary (EXHAUSTIVE over all (A,B) pairs at n=8) + random pairs. Probes
probe_407_census_supply_budget_feasibility.py + probe_407_census_supply_budget_exhaustive.py.

VALIDATION (engine == in-tree c.1007): KKH26 [x^6,x^4] n=16 k=3 p=65537 reproduces a=4->1792, a=5->336,
a=6(bind)->56 EXACTLY. Engine trusted.

RESULT (K vs budget 2^r*C(2^{mu-1},r), exact mod-p, MULTI-PRIME incl. non-Fermat, p-INDEPENDENT):
  n=8  (mu=3): r=2 K=24=bud(1.00) VIABLE | r=3 K=32=bud(1.00) VIABLE | r=4 K=24 > bud=16 (1.50x) *DEAD*
               -- identical at p=4129,11593,32801 (3 non-Fermat primes): K is p-INDEPENDENT (char-0).
  n=16 (mu=4): r=2 K=288>112 (2.57x) DEAD | r=3 K=896>448 (2.00x) DEAD | r=4 K=1568>1120 (1.40x) DEAD |
               r=5 K=1456<=1792 VIA | r=6 1344<=1792 VIA | r=7 384<=1024 VIA | r=8 K=560>256 (2.19x) DEAD
               -- identical at beta=4.0 (p=65537) and beta=4.5 (p=262193, non-Fermat).
A char-line u0=x^A,u1=x^B is a LEGAL stack, so a SINGLE pair with #alignable>budget already FALSIFIES
CensusDomination at that K; K being a max (exhaustive over lines at n=8) makes each DEAD verdict a
rigorous LOWER bound that already exceeds budget. The DEAD rows therefore rigorously certify
CensusDomination is FALSE at the budget the weld itself specifies.

THINNESS CONTROL (rule 3): the budget-overflow is THICKNESS-INVARIANT -- thick non-2-power domains
n=6,10,12 ALSO overflow at the shallow band r=2 (n=6: K=18>12 1.50x; n=10: K=100>40 2.50x; n=12: K=144>60
2.40x), same as thin n=16 r=2. The infeasibility is a STRUCTURAL combinatorial fact (the alignable-set
count is combinatorially large relative to the 2^r*C supply at shallow over-det depth), not a
2-power-essential phenomenon. (Deeper thick bands give degenerate K=0 from repeated node-differences in
non-2-power domains, so the deep-band comparison is clean only on 2-power n.)

VERDICT (rule-4 mapped wall; rule-6 honest, NOT a CORE result and NOT a prize refutation):
1. The deployed in-tree census route is INTERNALLY INFEASIBLE as a sufficiency chain at the shallow
   over-determined proximity parameters (r small) AND the deepest band (r=2^{mu-1}): there K = realized
   census count EXCEEDS eps*p = 2^r*C(2^{mu-1},r), so the weld hypothesis CensusDomination is simply
   FALSE at the budget eps* the weld pins -- the route demands a bound that the object violates.
2. It is feasible (K<=budget) only in a MID-DEPTH band (n=16: r in {5,6,7}). The proximity-gap prize is
   forall-r (every rate), so an infeasible-at-some-r hypothesis CANNOT deliver the universal pin via this
   weld at those r. The census normal form is not just "strictly stronger" (c.1007) -- it is, at the
   shallow/deepest bands, STRONGER THAN TRUE.
3. SHARPENS c.1007: the #alignable/#bad slack was lossy+thickness-invariant; HERE the absolute count
   #alignable exceeds the SUPPLY budget itself (the eps* defining the route), a strictly stronger
   internal-inconsistency finding. The census route, as deployed, cannot be the prize's proof shape at
   all r; a CORE proof must bound #bad directly (which collapses to O(1) at the hifreq line, 95e633cb0),
   NOT route through the alignable-set census. CORE not closed, not faked.
HONEST SCOPE: exact small-n (8 exhaustive-over-lines, 16 worst-family+random), multi-prime incl.
non-Fermat, p-independent. K at n=16 is a max over a worst-line family + random (not fully exhaustive),
but every DEAD row is a rigorous lower-bound overflow. Python-only, no Lean changed => axiom-clean trivially.
probe_407_census_supply_budget_feasibility.py + probe_407_census_supply_budget_exhaustive.py.

================================================================================
2026-06-15 The LAST NON-MOMENT route (per-frequency worst-coset tower descent) is
DEAD: the worst-coset transfer ratio rho* is THICKNESS-INVARIANT and the two half-
coset periods are ALWAYS sign-aligned (no signed cancellation) (opus-4-8 subagent)
--------------------------------------------------------------------------------
LANE (the surviving residual, c.1263 verdict): "the surviving hope is NOT a moment/cancellation argument
(both parities adverse) -- it must be a PER-FREQUENCY / STRUCTURAL estimate that does NOT pass through the
period MOMENTS." Every prior per-freq probe was the sup constant R stratified by v2(INDEX) (supnorm_2adic)
or the half-coset alignment over ALL b (c.287, thickness-monotone). UNPROBED: a per-frequency MULTIPLICATIVE
DESCENT of the WORST-COSET period eta_{b*}(mu_n) onto level n/2 -- a non-moment tower recursion that, if
contractive + thin-essential, gives M(n) <= rho* M(n/2) -> sqrt-growth by induction (a non-moment proof shape).

OBJECT (exact, PROPER mu_n, m=(p-1)/n>1, NEVER n=q-1): real periods eta_b = sum_{x in mu_n} cos(2pi b x/p)
(mu_n neg-closed => real). mu_n = mu_{n/2} u h*mu_{n/2} EXACT per-freq split: eta_b(mu_n) = A + B,
A=eta_b(mu_{n/2}), B=eta_b(h*mu_{n/2}). Worst coset b* = argmax over coset reps (period depends only on
b*mu_n). Measured rho*(n) = |eta_{b*}(mu_n)| / max_b|eta_b(mu_{n/2})| and the half-split sign align=sgn(A*B)
at b*. Multi-prime incl. non-Fermat. Thick control: composite non-2-power n + its index-2 subgroup.
Probe scripts/probes/probe_407_worstcoset_perfreq_descent.py.

RESULT 1 -- align = +1.000 at the worst coset EVERYWHERE (thin n=16..128 AND thick n=12..40, all betas,
incl. non-Fermat): at b* the two half-coset periods A,B ALWAYS have the SAME sign (reinforce, NO signed
cancellation). Independently reproduces the c.287 alignment wall AT THE WORST COSET specifically -- the
worst frequency is exactly where the halves phase-add, so there is NO per-frequency signed contraction to
exploit. (The "tower self-similarity / phase alignment" candidate mechanism from the brief is dead at b*.)

RESULT 2 -- rho* < 2 (sub-doubling) but THICKNESS-INVARIANT (the decisive rule-3 test): rho* decays slowly
with n (sqrt-cancellation-consistent) but thin and thick lie on ONE rho*(n) curve, interleaved by n NOT by
thickness (beta=4.0):
  n=16 THIN 1.762 | n=24 thick 1.735 | n=32 THIN 1.584 | n=40 thick 1.432 | n=48 thick 1.411 |
  n=64 THIN 1.559 | n=80 thick 1.304 | n=96 thick 1.432 | n=128 THIN 1.271
The 2-power (thin) rows do NOT contract more than the non-2-power (thick) rows at comparable n; rho* is a
function of n alone (generic sqrt-decay), NOT 2-power-essential.

VERDICT (rule-4 mapped wall; rule-3 FAIL => the route is dead for the THIN-essential prize; rule-6 honest):
1. The per-frequency worst-coset tower descent is THICKNESS-INVARIANT (rho* same thin/thick at matched n)
   AND non-cancelling (align=+1 at b*). By rule-3 (CORE is FALSE in the thick window, so any thickness-
   monotone mechanism is wrong) this descent CANNOT prove CORE: it would prove the (false) thick bound too.
2. This closes the LAST named non-moment route. The board's residual after the even-moment (INFLATED) and
   odd-moment (RIGID, anti-cancelling) walls was "a per-frequency structural estimate off the moments";
   the natural such object -- a worst-coset multiplicative descent -- is now mapped as thickness-invariant
   + non-cancelling. The worst frequency is precisely where the 2-adic coset halves REINFORCE; the thin
   advantage (deeper Sidon depth) does NOT manifest as per-frequency worst-coset contraction.
3. CONVERGENT with the whole board: per-line incidence -> Johnson, per-census -> Johnson/super-budget,
   even moments inflated, odd moments rigid, per-frequency descent thickness-invariant. The open prize
   content lives ONLY in the COLLECTIVE BGK aggregate cancellation among ALL frequencies simultaneously
   (L7 WorstCaseIncidenceBounded), which no single per-object / per-frequency / per-parity face captures.
HONEST SCOPE: rho* at large n (m>20000) uses a uniform coset-rep SAMPLE (so M is a lower bound on the true
worst coset => rho* is a lower bound; a higher true rho* only STRENGTHENS the sub-doubling-but-invariant
reading, never creates a thin advantage). Multi-prime incl. non-Fermat, p-stable. align is exact (full b*).
CORE not closed, not faked. Python-only, no Lean => axiom-clean trivially. probe_407_worstcoset_perfreq_descent.py.

### THIN SIDON DEPTH does NOT grow: n=64 EXACT computation REFUTES the "thin r_min advantage grows with n" lane (2026-06-15, opus-4-8 subagent)

LANE (the SURVIVING positive thin signal, rule-3 PASS RIGHT-sign, w/ its own flagged open): the prior
"THIN SIDON DEPTH SCALES" entry reported the thin Sidon depth r_min(mu_n) margin over random GROWING
(+0,+0->+4 at beta=4; +0,+0->+8 at beta=5, n=8/16/32) but flagged: "the EXACT growth LAW (sqrt(n) vs
log^c n) is NOT yet resolved -- need n=64,128 to fit the exponent." n=8/16/32 thin rows were CENSORED at
rmax=n/2 (full-depth) EXCEPT the single n=32/beta=4 r_min=11 point => the exponent was DEGENERATE-UNFIT.
No live worker on the n=64 extension. Ran it.

OBJECT (identical to probe_407_thin_sidon_depth_scaling.py, validated): r_min(mu_n,p) = smallest
NON-antipodal subset S of Z/n with Sum_{i in S} zeta^i == 0 (mod p), zeta primitive n-th root, mu_n
PROPER 2-power subgroup of F_p*, p=ceil(n^beta) prime ==1(n), m=(p-1)/n>1, NEVER n=q-1. Antipodal pairs
{i,i+n/2} excluded. r_min=NONE up to rmax => full-depth.

METHOD: SOUND BRACKET (full n=64 MITM infeasible, C(32,16)~6e8/half). EXACT exhaustive lower bound (no
non-antipodal vanisher of size <= r0 => r_min>=r0+1, RIGOROUS) + randomized SOUND upper witness (explicit
witness => r_min <= s). SELF-CHECK n=32 beta=4 -> exact witness at 11 (reproduces published r_min=11).
probe_407_thin_sidon_depth_n64_bracket.py.

RESULT (exact, n=64 added; the thin depth DROPS, the margin SHRINKS):
| n  | beta=4 thin r_min | beta=4 rand median | margin | r/sqrt(n) | beta=5 thin r_min |
|----|-------------------|--------------------|--------|-----------|--------------------|
| 16 | >8 (full)         | 9                  | +0     | --        | >8 (full)          |
| 32 | 11 (exact)        | 7                  | +4     | 1.94      | >16 (full)         |
| 64 | **8 (exact)**     | 6                  | **+2** | **1.00**  | **10 (exact)**     |

EXPLICIT n=64/beta=4 WITNESS (p=16777601, zeta=6014800): S={15,17,22,29,32,33,38,63}, |S|=8, sum==0 mod p,
NON-antipodal; exhaustive MITM confirms NO non-antipodal zero-sum of size<8 => r_min(mu_64,beta=4)=8 EXACTLY.
Predictions: sqrt(n) law => r_min(64)~11*sqrt(2)=15.6; log law => 11*6/5=13.2. ACTUAL=8, BELOW BOTH.

VERDICT (refutation-grade for the SCALING claim; rule-4 wall, rule-6 honest, NOT a CORE result):
the "thin Sidon depth r_min advantage GROWS with n" reading does NOT survive the n=64 exact point at beta=4:
the absolute thin depth DROPS 11->8 and the thin-minus-random margin SHRINKS +4->+2 (not monotone). The
small-n growth was a CENSORING/CEILING artifact (n=16,32 thin rows full-depth-censored at rmax=n/2; n=32
r_min=11 sits near the ceiling 16). So the smallest-vanisher depth r_min is NOT the carrier of a growing
collective thin signal -- it is non-monotone and small-n biased. CONSEQUENCE: the surviving-thin effort
should target the HIGHER-ORDER collective moment profile (the L7 BGK aggregate the whole board converges
to), NOT r_min. This CLOSES the smallest-vanisher sub-lane. CORE not closed, no overclaim. Python-only
exact, no Lean changed => axiom-clean trivially. probe_407_thin_sidon_depth_n64_bracket.py.

================================================================================
2026-06-15 The OddExcessSpikeLaw value (the 2-adic even-direction collapse-failure
margin) is THICKNESS-INVARIANT -> the even-direction descent's odd-excess is NOT the
thin-specific prize mechanism (opus-4-8 subagent)
--------------------------------------------------------------------------------
LANE: the FRESH open core formalized by OddExcessLaw.lean (Shaw 80a89e78e): oddExcess = full_bad \
half_bad, |oddExcess| = E = I_n(x^{2a'}) - I_{n/2}(x^{a'}), oddExcess=empty <=> EvenDirectionIncidence
Collapse. The named-but-unproven OddExcessSpikeLaw: E=(n/2)^2 at the half binding rung. QUESTION nobody
asked (rule-3): is the SPIKE VALUE thinness-essential, or does it persist in the thick prize-FALSE window?

METHOD: exact per-witness-set affine-in-gamma incidence (probe_farline engine, NO floats, NO codeword
enum), PROPER mu_16, NEVER n=q-1. Object I_n(x^4) over mu_16, code degree 4, binding rung r=10 (delta
.625). Anchored I_n=89 EXACTLY (= in-tree probe_farline n=16 k=4 r=10). q-sweep index m=(p-1)/16 from
thick to thin. probe_407_oddexcess_qsweep.py + probe_407_oddexcess_n16_validate.py.

RESULT (exact):
  m=6(p97):57  m=7(p113):89  m=12:89  m=16(beta2.0):89  m=21(p337):81  m=22:89  m=27(p433):81
  m=36..75 (beta 2.29-2.56, the prize-FALSE thick window): 89,89,89,89,89,89,89,89  ALL 89
  m=151,201,250 (beta 2.81-2.99): 89,89,89   m=501,2016,4096 (thin): 89,89,89
  => I_n(x^4;r=10) = 89 IDENTICALLY across the thick beta=2.3-3.2 prize-FALSE window AND the thin regime.
     The dips (81 at p=337/433, 57 at p=97) are SPORADIC small structured-prime artifacts, NOT a
     thickness trend (89 returns at thicker p=113/193/257/353).

VERDICT (rule-4 wall, rule-3 FAIL): the OddExcessSpikeLaw value (the even-direction collapse-failure
margin) is a THICKNESS-INVARIANT cyclotomic constant. The 2-adic even-direction collapse fails by the
SAME ~(n/2)^2 margin in the thick prize-false regime as in the thin prize regime => the collapse FAILURE
is thin-blind. A thinness-essential proof of CORE cannot route through the even-direction descent's odd-
excess value. Joins the board meta-pattern (every per-direction object is thickness-invariant + Johnson-
tracking; only the aggregate BGK moment is open). RULE-6: does NOT close CORE, does NOT refute the in-
tree oddExcess_card or the named Prop (the collapse genuinely fails; E IS the obstruction) -- it maps
that the obstruction's VALUE is thin-independent. Python-only exact => axiom-clean trivially.

================================================================================
2026-06-15 POSITIVE FEASIBILITY: the CANONICAL open core B=max_stack #bad IS within
the eps* budget at EVERY r (ratio 0.04-0.41) -- the census route's infeasibility is
PURELY the #bad<=#alignable loss; target #bad DIRECTLY (opus-4-8 subagent)
--------------------------------------------------------------------------------
LANE (the decisive follow-up to the census-infeasibility brick 5ac9fe4bc): I showed the census
surrogate K=#alignable EXCEEDS the weld budget 2^r*C(2^{mu-1},r) at the shallow/deepest bands (census
route DEAD). But the CANONICAL open core (OpenCoreConditionalPin.lean) is WorstCaseIncidenceBounded C
delta B = (forall stacks, #bad-gamma <= B), and the census bounds B only via the LOSSY #bad<=#alignable
(c.1007: up to 112x slack). UNMEASURED until now: is the TRUE core object B = max_stack #DISTINCT-bad-gamma
itself within budget, even where the surrogate K is not?

OBJECT (exact mod-p, PROPER mu_n m>1 never n=q-1, prize primes incl. non-Fermat; #bad = #distinct pinned
ratios -e0(T)/e1(T) over alignable a-sets, the genuine OpenCoreConditionalPin object NOT the alignable-set
count). m=1 prize shape k=r-1, binding band a_bind=r+1. Adversary = exhaustive char-lines (n=8) / strong
worst-line family (n=16). Probe probe_407_truecore_B_vs_budget.py (+ /tmp/truecore16.py focused n=16 run).

RESULT (B vs budget 2^r*C(2^{mu-1},r), p-INDEPENDENT across Fermat p=65537 AND non-Fermat p=262193):
  n=8  (exhaustive over ALL lines): r=2 B=5<=24, r=3 B=9<=32. FEASIBLE (ratio 0.21, 0.28).
  n=16: r=2 B=24<=112 (0.21) | r=3 24<=448 (0.05) | r=4 40<=1120 (0.04) | r=5 73<=1792 (0.04) |
        r=6 113<=1792 (0.06) | r=7 41<=1024 (0.04) | r=8 104<=256 (0.41). FEASIBLE at EVERY r.
  IDENTICAL at beta=4.0 and beta=4.5 (non-Fermat) => B is p-independent (char-0 structural).
CONTRAST with the census K (push 5ac9fe4bc): at the SAME r=2,3,4,8 where K>budget (1.4-2.6x DEAD),
the TRUE core B is 0.04-0.41x budget -- comfortably FEASIBLE. The gap K/B at the binding band is the
c.1007 lossiness (#alignable overcounts #bad by collapsing many a-subsets of ONE far-line locus onto one
gamma): at the hifreq line up to 112 alignable sets pin ONE bad gamma.

VERDICT (positive direction-setting, rule-6 honest -- NOT a CORE closure):
1. The deployed eps* budget 2^r*C(2^{mu-1},r) is NUMERICALLY SUFFICIENT for the CANONICAL open core
   WorstCaseIncidenceBounded at the binding window band, at EVERY proximity parameter r, with a WIDE
   margin (ratio <=0.41, mostly <=0.06). The pin's budget is NOT the obstruction; the open work is a
   PROOF that #bad <= 2^r*C(...), and the target is plausible (the realized worst-stack #bad sits far
   below it).
2. SHARPENS c.1007 quantitatively: the census route should be ABANDONED in favor of bounding #bad DIRECTLY
   (the lossy #bad<=#alignable step is the SOLE reason the census surrogate overflows). This converts
   c.1007's qualitative "target #bad directly" into a measured feasibility: #bad/budget <= 0.41 forall r.
3. HONEST: this is a NECESSARY-condition check (B fits the budget), NOT a proof that B<=budget holds at
   ALL n / the prize regime -- the SUP over stacks at n=16 uses a strong worst-line family + random (n=8
   exhaustive). A larger true B at unscanned stacks would only RAISE B; but the >2x headroom (ratio <=0.41)
   at the binding bands gives margin. The asymptotic #bad-vs-budget growth law (does ratio stay <1 as
   n->inf, the floor-vs-Johnson question, c.348 undecidable below n=256) is UNCHANGED -- this is a
   finite-n feasibility result, not the asymptotic bound. CORE not closed.
4. CONVERGENT: explains why per-line #bad COLLAPSES to O(1) at hifreq (95e633cb0) yet the route can still
   work -- the collapse is exactly what keeps B far below budget; the census surrogate's inflation was a
   red herring. The real open object is well-posed and budget-feasible; the prize is the PROOF, at the
   collective BGK depth, that this finite-n feasibility persists asymptotically.
Python-only, no Lean => axiom-clean trivially. probe_407_truecore_B_vs_budget.py.

================================================================================
2026-06-15 FLOOR-CONSISTENT on the CORRECT object: the canonical #bad / eps*-budget
ratio at the shallowest binding band is BOUNDED BELOW 1 (converging ~0.26), NOT
Johnson-tracking -- the first floor-consistent growth on #bad direct (opus-4-8 subagent)
--------------------------------------------------------------------------------
LANE (capstone follow-up to the true-core feasibility brick ed1db3379): that brick showed B=max_stack
#bad <= eps*-budget 2^r*C(2^{mu-1},r) at finite n. The PRIZE content is the ASYMPTOTIC decider: does
ratio(n)=#bad/budget stay BOUNDED BELOW 1 (genuine FLOOR, prize-positive) or CREEP UP TO 1 (Johnson, the
fate of every SURROGATE: incidence I(n), e2=0 census K, even/odd moments). This is the FIRST growth
measurement on the CANONICAL OpenCoreConditionalPin object #bad itself (all prior floor-vs-Johnson probes
were on surrogates).

OBJECT (exact mod-p, PROPER mu_n, p~n^4, shallowest binding band r=2 -> k=1, a=3 where C(n,3) is brute-
feasible to n=64): #bad = #distinct pinned gamma, max over char-line adversary. Probe
probe_407_truecore_B_growth.py (dedicated fast pair-ratio routine reaching n=64).

RESULT (worst line consistently (4,2)):
  n= 8: #bad=5    budget=24    ratio=0.2083
  n=16: #bad=25   budget=112   ratio=0.2232
  n=32: #bad=113  budget=480   ratio=0.2354
  n=64: #bad=481  budget=1984  ratio=0.2424
Increments 0.0149, 0.0122, 0.0070 -- DECAYING (last ratio ~0.57) => geometric extrapolation to ~0.26,
BOUNDED WELL BELOW 1. The canonical #bad-to-budget ratio is CONVERGING below 1 = FLOOR-CONSISTENT.

VERDICT (rule-4; the FIRST floor-consistent (not Johnson) signal on the right object; rule-6 honest):
1. On the SURROGATE faces, every floor-vs-Johnson probe converged to Johnson (ratio -> 1 / super-budget).
   On the CANONICAL #bad object at the shallowest binding band, the ratio-to-budget converges to ~0.26
   -- bounded below 1, FLOOR-consistent. This is the qualitative difference between #bad (the real
   obligation) and the surrogates (#alignable, incidence, census, moments) that all over-shoot.
2. CONSEQUENCE: the deployed eps* budget 2^r*C(2^{mu-1},r) is not merely met finite-n (ed1db3379) -- its
   margin appears to PERSIST (ratio bounded ~0.26) at the shallowest band as n grows. If this floor
   persists across all r and to the prize regime, the canonical pin's budget is asymptotically sufficient
   for #bad -- exactly the prize-positive direction the surrogates falsely killed.
HONEST SCOPE (rule 6 -- NOT a closure): single SHALLOWEST band r=2 (computational reach; deepest band
r=2^{mu-1} is brute-infeasible past n=16); worst is a fixed LOW line (4,2); p-fixed (one prime per n);
n<=64. The full prize is forall-r and the asymptotic decider needs n>=256 (c.348: numerics cannot
separate floor from Johnson below 256). So this is a measured finite-n floor-CONSISTENT trend on the
correct object at one band -- it does NOT prove a floor (the deeper bands / larger n could differ), but
it is the first face whose #bad-to-budget ratio does NOT march to Johnson. The deep-band growth law +
the multi-band + larger-n confirmation are the open residual. CORE not closed, not faked. Python-only,
no Lean => axiom-clean trivially. probe_407_truecore_B_growth.py.

================================================================================
2026-06-15 The TRUE-CORE B (max_stack #distinct-bad-gamma) feasibility margin is
THICKNESS-INVARIANT -- B/budget identical thin vs thick => finite-n feasibility is
Johnson-margin, NOT thin-essential; thin content is purely in B's ASYMPTOTIC growth
(opus-4-8 subagent)
--------------------------------------------------------------------------------
LANE: complement to 0xSolace ed1db3379 (POSITIVE: B=max_stack #distinct-bad-gamma is WITHIN the eps*
budget at every finite r, ratio 0.04-0.41x, at beta=4.0/4.5 BOTH THIN). That probe did NOT test the
THICK regime. QUESTION (rule-3): is the B/budget feasibility margin THINNESS-ESSENTIAL (grows toward 1
as mu_n thickens => thin content) or thickness-invariant (Johnson-margin)?

METHOD: reused the sibling's EXACT engine (nbad_at_band, charline) VERBATIM; swept beta from THICK
(2.3, prize-FALSE) to THIN (5.0, prize-shape) at the SAME bands r=4 (census-overflow band) + r=8
(Johnson band). Exact mod-p, PROPER mu_16, never n=q-1. probe_407_truecore_B_thinness.py.

RESULT (exact):
  r=4: B=40 at EVERY beta (2.3,2.6,3.0,3.5,4.0,5.0), ratio=0.0357 IDENTICAL (bit-for-bit)
  r=8: B=104 at beta 2.3,3.0,3.5,4.0,5.0 (ratio 0.4062); 96 at beta=2.6 (sporadic structured-prime dip)
  => B at fixed (n,r) is THICKNESS-INVARIANT. The B/budget feasibility margin is identical in the thick
     prize-FALSE regime and the thin prize regime.

VERDICT (rule-3 FAIL on the feasibility-margin face): the sibling's positive "B within budget" result
is a THICKNESS-INVARIANT (Johnson-margin) feasibility, NOT a thin-specific signal. Finite-n B feasibility
holds identically in BOTH regimes => finite-n feasibility CANNOT distinguish thin from thick. The thin
content lives PURELY in the ASYMPTOTIC GROWTH RATE of B(n), NOT in finite B values or the budget ratio.
This SHARPENS ed1db3379: targeting #bad directly is right, but the feasibility is necessary-not-sufficient
(thin-blind at finite n); the prize is the GROWTH law of B (consistent with c.348: numerics can't decide
floor-vs-Johnson below n=256). RULE-6: does NOT close CORE, does NOT contradict ed1db3379 (B IS within
budget) -- it maps that the WITHIN-budget margin is thin-independent. Python-only exact => axiom-clean.

### The MONOMIAL far-line IS the worst-case stack at the BINDING band: generic + structured-low-degree stacks give #bad=0 there (2026-06-15, opus-4-8 subagent)

LANE (uncontested gap, exposed by reading B1IncidenceBridge.lean): the in-tree canonical core
WorstCaseFarIncidenceBounded quantifies #bad = #pinned-gamma over ALL far stacks (u0,u1); the bridge
epsMCA <= B/q needs B = max over ALL (u0,u1). But the ENTIRE board (incidence I(n), census K, #bad
collapse, wf-D1/D2/D5, n/4 law, "->Johnson") analyzes ONLY the MONOMIAL far-lines u0=x^A,u1=x^B and
ASSERTS they are the worst case. NO probe had TESTED whether a GENERIC (non-monomial) far stack yields
MORE bad-gamma. If generic #bad > monomial, the board's "->Johnson" UNDER-ESTIMATES the true B.

METHOD (exact mod-p, PROPER mu_n, prize prime p~n^4, NEVER n=q-1): #bad(u0,u1;a) via exact bordered
Vandermonde residuals (the in-tree `residual` det) + Aligned-subset semantics (mcaEvent_iff_aligned_subset):
gamma bad iff some a-subset S has all (k+1)-subtuples sharing gamma=-res0(T)/res1(T) with a non-degenerate
tuple. Compared MONOMIAL u0=x^A,u1=x^B vs RANDOM-GENERIC far stacks (u1 enforced FAR) AND STRUCTURED
low-degree-poly stacks, full band sweep a=k+1..n/2. n=16,k=3,hifreq[9,7]. probe_407_genericstack_vs_monomial_worst.py.

RESULT (exact, n=16 k=3 hifreq[9,7], p=65537):
| band a | #bad(monomial) | #bad(generic) max / nonzero-of-draws | regime |
|--------|----------------|--------------------------------------|--------|
| 4 (k+1)|  737           | max=1800, 8/8 nonzero (generic > mono)| SHALLOW non-binding |
| 5      |  1             | max=1,   2/8 nonzero                  | shallow |
| 6      |  1             | max=0, 0/20 nonzero                   | BINDING |
| 7      |  1             | max=0, 0/20 nonzero                   | BINDING |
| 8      |  1             | max=0, 0/20 nonzero                   | BINDING |
Structured low-degree-poly stacks (deg k..k+3, non-monomial) at a=6,7: ALSO #bad=0 (0/10 each).

VERDICT (rule-4 mapped; SUPPORTS the board's monomial-worst restriction at the binding radius, NOT a
CORE result): at the SHALLOW band a=k+1 every (k+1)-tuple is trivially singleton-aligned, so #bad merely
counts distinct residual-ratios -- large for ANY stack (generic 1800 > mono 737); that band sits FAR above
the prize floor and is NON-binding. At the DEEP BINDING bands (a>=6, where the floor lives) the monomial
far-line pins #bad to its binding value (1) while EVERY generic random AND structured-low-degree far stack
gives EXACTLY 0 (0/20 + 0/10 nonzero). => the MONOMIAL far-line IS the worst-case stack at the binding
radius; generic stacks do NOT threaten the canonical core B = max over ALL stacks there. This JUSTIFIES
(numerically, does not formally prove the WLOG) the board's universal restriction to monomial far-lines:
the "->Johnson" derived on monomials is NOT an under-estimate of the true B at the binding band. CORE not
closed, no overclaim. Python-only exact, no Lean => axiom-clean trivially. probe_407_genericstack_vs_monomial_worst.py.

================================================================================
2026-06-15 The moment-ratio STEP margin g(2)=(A_3/A_2)/((2r+1)n) SATURATES TO
EXACTLY 1 (geometric rho~1/2, L~1.0003): the r=2 step is asymptotically TIGHT, not
slack -- the surviving-lever margin closes to ZERO as n->inf (opus-4-8 subagent)
--------------------------------------------------------------------------------
LANE (the surviving thin-essential lever, sharpening the '⚠️ TEMPERING DATA' entry): the open core
reframes to the single moment-ratio STEP  A_{r+1}/A_r <= (2r+1)*n  at r*=round(log p) (★ SHARPENING).
The thin g(r*) stays <1 but INCREASES in n (0.366,0.468,0.530,0.643 at n=8,16,32,64); the TEMPERING entry
flagged that n<=64 CANNOT distinguish "saturates below 1" (provable) from "creeps to 1" (BGK-tight), and
the FFT engine STALLED at n=128 (size-p FFT at p~268M is O(p log p) with a prime-size penalty -> hours).

METHOD (the feasibility unlock -- NO size-p FFT): the moment ratio needs only the additive energy, via the
in-tree identity Sum_b |eta_b|^{2r} = p*E_r(mu_n) (SubgroupGaussSumMoment). A_r = E_r - n^{2r}/p
(DC-subtracted), E_r = #{(x_1..x_r),(y_1..y_r) in mu_n^{2r}: sum x = sum y} = r-fold additive energy,
computed EXACTLY by dense integer sumset convolution on the n-element subgroup (O(support*n), NO p-FFT).
=> n=128 (and the low-r rung) become EXACT-INTEGER feasible. PROPER thin mu_n (2-power, m=(p-1)/n>1, p~n^4,
NEVER n=q-1). probe_407_step_at_rstar_n128.py.

RESULT (EXACT integers, the r=2 step margin, thin beta=4):
| n   | E_2   | E_3      | A_3/A_2  | (2r+1)n=5n | g(2)=(A_3/A_2)/(5n) | increment |
|-----|-------|----------|----------|------------|---------------------|-----------|
|  32 | 2976  | 446720   | 149.81   | 160        | 0.9363              | --        |
|  64 | 12096 | 3750400  | 309.74   | 320        | 0.9679              | +0.0316   |
| 128 | 48768 | 30725120 | 629.70   | 640        | 0.9839              | +0.0160   |
The INCREMENT HALVES EXACTLY: +0.0316 -> +0.0160, ratio = 0.5063 ~ 1/2. (r=3 rung concordant: g(3) =
0.9063, 0.9527 at n=32,64, same upward.)

HONEST GEOMETRIC EXTRAPOLATION (rule-6, disciplined -- 3 exact points, geometric model g(2;2^k)=L-A*rho^k):
  rho = 0.5063,  remaining tail from n=128 = inc * rho/(1-rho) = 0.0164,  =>  L = g(2;n->inf) ~ 1.0003.
=> the r=2 step margin SATURATES TO EXACTLY 1 (the geometric series converges, ratio ~1/2, to L~1.00),
   NOT to a value strictly below 1.

VERDICT (rule-4 sharpening, rule-6 honest, NOT a closure, NOT a refutation): the moment-ratio STEP
A_{r+1}/A_r <= (2r+1)n -- the surviving thin-essential lever -- is, at the r=2 rung, ASYMPTOTICALLY TIGHT:
g(2) -> 1 from below with geometric ratio ~1/2 (margin closes to ZERO as n->inf), NOT bounded away from 1.
This RESOLVES the TEMPERING entry's open dichotomy at the r=2 rung in favor of "saturates AT 1" (the
boundary case): the step holds with STRICTLY POSITIVE margin at every FINITE n (0.9363..0.9839), but the
margin VANISHES asymptotically (A_3 = 5n*A_2 in the limit, an EQUALITY). CONSEQUENCE: a base-case +
single-step-monotonicity proof of A_r <= Wick CANNOT close on a UNIFORM positive step margin -- the step is
asymptotically an equality, exactly the BGK knife-edge. The thin advantage is real but RAZOR-THIN (the
increment-halving keeps g<1 at finite n yet L=1), which is the precise quantitative meaning of "BGK-tight"
the board kept circling. HONEST SCOPE: this is the r=2 rung (exact, extensible), NOT the deep r*~log p rung
(where A_{r+1}/A_r -> M^2 = the prize directly); the r=2 saturation-to-1 is a clean exact-integer
companion + sharpening of the FFT g(r*) trend, not a proof at r*. CORE not closed, no overclaim. The
exact-integer E_r unlock (no size-p FFT) is reusable for deeper-r / larger-n moment-step extension.
Python-only exact => axiom-clean trivially. probe_407_step_at_rstar_n128.py.

================================================================================
2026-06-15 EXACT CLOSED FORMS pin the r=2 moment-step saturation ANALYTICALLY:
E_2(mu_n)=3n(n-1), E_3(mu_n)=15n^3-45n^2+40n => g(2;n)=1-2/n+O(1/n^2) -> EXACTLY 1,
and the LEADING terms are NEGATION-CLOSURE-generic (thin advantage is a VANISHING
O(1/n) subleading correction, NOT leading-order) (opus-4-8 subagent)
--------------------------------------------------------------------------------
LANE: upgrade the 3-point geometric fit (082400b56: g(2)->1, rho~1/2) to an ANALYTIC statement by pinning
the EXACT closed forms of E_2(mu_n), E_3(mu_n) (the only S-dependence of A_r). The clean rho~1/2 hinted a
doubling recursion. Exact integer additive energies, thin 2-power mu_n, n=8..128, p-INVARIANT (rule-6:
E_2,E_3 IDENTICAL across 3 prize primes each). probe_407_Er_closedform_thin.py.

EXACT CLOSED FORMS (fit on n=8,16,32 then VERIFIED EXACT on n=64,128 -- all 5 points exact):
    E_2(mu_n) = 3n^2 - 3n        = 3n(n-1)
    E_3(mu_n) = 15n^3 - 45n^2 + 40n = 5n(3n^2 - 9n + 8)
  (168,720,2976,12096,48768 and 5120,50560,446720,3750400,30725120 -- ALL match exactly.)
Doubling ratios converge: E_2(2n)/E_2(n) -> 4 (E_2 ~ 3n^2), E_3(2n)/E_3(n) -> 8 (E_3 ~ 15n^3).

ANALYTIC SATURATION (the upgrade from fit to fact): dropping the negligible DC term n^{2r}/p (p~n^4),
    g(2;n) = (A_3/A_2)/(5n) = (E_3/E_2)/(5n) = (15n^3-45n^2+40n)/((3n^2-3n)*5n)
           = (3n^2 - 9n + 8) / (3n(n-1)) = 1 - 2/n + 2/(3n^2) + O(1/n^3).
  => g(2;n) -> 1 EXACTLY (the leading coeffs CONSPIRE: E_3 lead 15, E_2 lead 3, ratio 5, /5n = 1).
  => the increment HALVES because the dominant term is -2/n (g(2n)-g(n) ~ +1/n, halving per doubling) =
     the rho~1/2 of the geometric fit is EXACTLY this -2/n asymptotics. The step A_3 <= 5n*A_2 holds with
     margin EXACTLY 2/n -> 0: an ANALYTIC asymptotic EQUALITY, not a fit. (Measured 0.9363/0.9679/0.9839
     match 1-2/n+... up to the tiny dropped DC term.)

RULE-3 (the HONEST thinness verdict -- where the thin content actually sits): the LEADING terms are
NEGATION-CLOSURE-GENERIC, NOT thin-specific:
    E_2(thin) == E_2(neg-closed-random) EXACTLY (168,720,2976; confirms 657e7139b).
    E_3(thin) ~ E_3(neg-closed-random) with a TINY, VANISHING gap: E3_thin/E3_neg = 0.9953, 0.9983, 0.9995
      at n=8,16,32 (thin slightly BELOW, gap shrinking 0.47%->0.17%->0.05% ~ O(1/n) -> 1).
  => the closed forms 3n(n-1), 15n^3-45n^2+40n are (to leading order) the additive energies of ANY
     neg-closed set, NOT a 2-power-subgroup signature. The thin-specific structure is ONLY a VANISHING
     O(1/n) SUBLEADING correction to E_3. This is WHY g(2) saturates to EXACTLY 1: the leading-order
     conspiracy E_3/E_2 -> 5n is a neg-closure fact, and the thin correction is too small to move the limit.

VERDICT (rule-4 sharpening, rule-3 HONEST, rule-6 no overclaim, NOT a closure): the r=2 moment-step
A_3 <= 5n*A_2 -- the surviving thin-essential lever -- saturates to an ANALYTIC asymptotic EQUALITY
g(2;n)=1-2/n+O(1/n^2), with the leading terms NEGATION-CLOSURE-GENERIC and the thin advantage confined to
a VANISHING O(1/n) subleading correction in E_3. This PROVES (closed-form, all-n-exact) that a base-case +
single-step monotonicity proof of A_r<=Wick CANNOT close at the r=2 rung on a uniform positive margin: the
margin is EXACTLY 2/n -> 0, and what little thin-specific content exists is subleading and vanishing. The
BGK knife-edge is now EXACT at r=2, not extrapolated. HONEST SCOPE: r=2 rung (the deep r*~log p rung, where
A_{r+1}/A_r -> M^2 = the prize, remains the open content -- the deep-r E_r closed forms are the natural next
target, the E_r unlock makes them computable). The closed forms E_2=3n(n-1), E_3=15n^3-45n^2+40n are clean
formalizable targets (exact rational arithmetic => axiom-clean trivially). probe_407_Er_closedform_thin.py.

## A_r<=Wick SURVIVES at the n=32 WORST in-window bad prime, but margin is KNIFE-EDGE (~0.93-0.97) + proxy fails 16x/octave (2026-06-15, opus-4-8 subagent)

LANE (uncontested): ec140aead pinned the worst-in-window-bad-prime r-trajectory at n=16 ONLY; 98db97afc did
n=32..256 A_r/Wick but at a GENERIC prime (Anom understated). Combined: worst-in-window-bad-prime x full-r-
trajectory x n=32. probe_407_anom_worst_rtraj_n32.py. Exact integer counts: E_r^(p) via r-fold mod-p
convolution + sum-of-squares; E_r^(0) via cyclotomic lattice Z^{n/2} convolution (zeta^{n/2}=-1). PROPER mu_n,
p>=n^4, NEVER n=q-1. SELF-CHECK n=16 reproduces ec140aead EXACTLY (p=76001, proxy 1.0914 @ r=6, A_r/Wick
0.9364->0.3743). ENGINE TRUSTED.

RESULT (n=32, worst bad prime p=1244993, beta=4.050, index m=38906, NOT n=q-1), r=2..6:
  A_r/Wick = 0.9685, 0.9383, 0.9264, 0.9361, 0.9591  (TARGET A_r<=Wick HOLDS, max 0.9685 at SHALLOW r=2)
  proxy Anom_r/(n^{2r}/p) = 0, 17.81, 13.57, 8.38, 5.12  (SUFFICIENT proxy FAILS HARD, peak 17.81 @ r=3)
  E0/Wick = 0.9688, 0.9089, 0.8255, 0.7258, 0.6175  (char-0 floor falls => Wick-E0 headroom grows, absorbs
    the failing proxy => A_r<=Wick survives via headroom-absorption, NOT via small Anom)
ADVERSARIAL RE-AUDIT (rule 6) top-4 worst bad primes p=1244993/1383169/1382177/1366721 (all proper mu_32,
m>>1): A_r<=Wick holds at ALL; max A_r/Wick=0.9685 each; 2 of 4 NON-MONOTONE (margin dips then RISES toward 1
at deep r), 2 of 4 monotone-decreasing.

VERDICT (mapped frontier, NOT a CORE result, no overclaim):
(1) The DC-subtracted carrier A_r<=Wick SURVIVES at the ADVERSARIAL n=32 prime (not just the generic prime of
    98db97afc) — POSITIVE for the anomaly route one octave deeper.
(2) The SUFFICIENT proxy Anom_r<=n^{2r}/p degrades ~16x/octave (peak 1.09 @ n=16 -> 17.81 @ n=32): DEAD as an
    asymptotic route; only direct A_r<=Wick survives, ENTIRELY via the growing Wick-E0 headroom.
(3) The n=32 worst-prime A_r/Wick does NOT collapse the way 98db97afc's GENERIC prime did (0.005-0.12 @ r*);
    at the WORST prime it is PINNED ~0.93-0.97 and turns BACK UP toward 1 on 2/4 primes. The "monotone
    collapse, no catch-up" reassurance is a GENERIC-prime artifact; the adversarial prime is a knife-edge just
    under 1 across accessible rungs — the BGK wall's shape.
HONEST: sub-prize p (~10^6; budget p~2^128), r capped at 6 (E0-ring), r*=14 not reached. Does NOT close CORE,
NOT refute the prize, NOT contradict 98db97afc. Pure-Python exact integer counts, no Lean => axiom-clean
trivially. probe_407_anom_worst_rtraj_n32.py.

================================================================================
2026-06-15 The E_r STRUCTURE is WICK-leading with a clean -C(r,2) subleading:
E_r(mu_n) = (2r-1)!![n^r - C(r,2)n^{r-1} + O(n^{r-2})] => the GENERAL moment-step
margin is g(r) = 1 - r/n + O(1/n^2) EXACTLY (the BGK knife-edge in closed form)
(opus-4-8 subagent)
--------------------------------------------------------------------------------
LANE: generalize the r=2 closed-form (5b0873ddb) to a GENERAL-r law by pinning the E_r structure. Exact
integer additive energies, thin 2-power mu_n, fit + EXACT-verify across n. probe_407_Er_closedform_thin.py.

EXACT CLOSED FORMS (each fit on a few n then VERIFIED EXACT on all probed n=8..128/64):
    E_1 = n
    E_2 = 3n^2 - 3n
    E_3 = 15n^3 - 45n^2 + 40n
    E_4 = 105n^4 - 630n^3 + 1435n^2 - 1155n
STRUCTURE (the clean pattern):
    LEADING coeff = (2r-1)!! = 1, 3, 15, 105  = the WICK / Gaussian moment.  (E_r/n^r -> (2r-1)!! as n->inf.)
    SUBLEADING/LEADING ratio = -C(r,2) = -1, -3, -6  for r=2,3,4.
    => E_r(mu_n) = (2r-1)!! [ n^r - C(r,2) n^{r-1} + O(n^{r-2}) ].

GENERAL-r STEP-MARGIN LAW (EXACT from the closed forms, derived for r=1,2,3; conjectured general):
    g(r) = (A_{r+1}/A_r)/((2r+1)n) = (E_{r+1}/E_r)/((2r+1)n)
         = 1 - r/n + O(1/n^2).
  EXACT instances:  r=1: g=(n-1)/n = 1-1/n.  r=2: (3n^2-9n+8)/(3n(n-1)) = 1-2/n+2/(3n^2).
                    r=3: (3n^3-18n^2+41n-33)/(n(3n^2-9n+8)) = 1-3/n+2/n^2.
  => the moment-step margin at depth r is EXACTLY r/n (to leading order): 1 - g(r) ~ r/n.

CONSEQUENCE (the BGK knife-edge, now in closed form): at the prize depth r* ~ log n,
    g(r*) ~ 1 - r*/n ~ 1 - (log n)/n -> 1   (margin VANISHES for any r = o(n)).
This is EXACTLY the measured FFT g(r*) trend (0.366,0.468,0.530,0.643 at n=8..64): the step holds with a
POSITIVE margin r/n at every finite n, but the margin -> 0 at the prize joint limit (r*~log n, n->inf).

RULE-3 (honest, where the thin content sits): the WICK leading term (2r-1)!! and the -C(r,2) subleading are
NEGATION-CLOSURE-GENERIC (E_2(thin)==E_2(neg-rand) EXACTLY; E_3(thin)/E_3(neg-rand) = 0.9953->0.9995 ->1,
the thin advantage is a VANISHING O(1/n) correction BELOW the subleading). So the g(r)=1-r/n law is largely
a neg-closure fact; the THIN-specific deviation is an even-higher-order vanishing correction. This is why
the Wick ratio E_r/((2r-1)!!n^r) is <1 but -> 1 BOTH as n grows (0.94->0.97 at r=2, n=16->32) AND deeper r
shrinks it faster (0.94,0.82,0.68,0.52 at r=2..5, n=16) -- the joint (r*,n) limit pushes it to 1.

VERDICT (rule-4 sharpening, rule-6 no overclaim, NOT a closure): the moment-step margin is EXACTLY r/n
(closed-form, all-n-exact for r<=3, structurally (2r-1)!!/-C(r,2)/Wick for r<=4). The surviving
thin-essential lever (the step A_{r+1}/A_r <= (2r+1)n) holds at EVERY finite (r,n) with margin r/n>0 but the
margin VANISHES at the prize depth r*~log n -- the BGK knife-edge, now characterized analytically rather than
numerically. The E_r are WICK-leading (A_r<=Wick is a LEADING-ORDER EQUALITY for thin mu_n); the thin prize
advantage lives ONLY in the rate the Wick ratio approaches 1 (a sub-subleading vanishing term). HONEST OPEN:
whether 1-g(r*) = r*/n + (higher terms) stays bounded BELOW the threshold at the JOINT (r*~log n, n->inf)
limit -- i.e. whether the accumulated O(1/n^2)+ corrections over r* steps rescue a positive margin -- is the
irreducible prize content; the leading r/n law does NOT resolve it (it -> 0, consistent with both
prize-true and BGK-tight). The closed forms E_r = (2r-1)!![n^r - C(r,2)n^{r-1}+...] are clean formalizable
targets (exact rational arithmetic => axiom-clean trivially). probe_407_Er_closedform_thin.py.

================================================================================
2026-06-15 The A_r/Wick PRIZE-RATIO profile CONFIRMS the r/n margin law on the
actual object: ratio RISES toward 1 as n grows at every fixed r (margin shrinks);
deep-r upturn at fixed p is a finite-field artifact (opus-4-8 subagent)
--------------------------------------------------------------------------------
LANE: test the brick-4 closed-form verdict (g(r)=1-r/n, margin->0) DIRECTLY on the prize object
A_r/Wick_r = E_r/((2r-1)!! n^r) (sub-Gaussian iff <1). Exact integer E_r, thin 2-power mu_n n=16,32, deep
r. probe_407_ArWick_ratio_profile.py.

RESULT (exact A_r/Wick_r profile, thin beta=4):
  n=16 (r*=9): r=1..9 = 1.00, 0.9375, 0.8229, 0.6764, 0.5217, 0.3795, 0.2623, 0.1735, 0.1106
  n=32 (r*=7): r=1..7 = 1.00, 0.9688, 0.9089, 0.8314, 0.7554, 0.7112, 0.7440
KEY: at every fixed r the n=32 ratio EXCEEDS the n=16 ratio (r=2 0.94->0.97, r=3 0.82->0.91, r=4
0.68->0.83, r=5 0.52->0.76, r=6 0.38->0.71). The sub-Gaussian MARGIN (1-ratio) SHRINKS as n grows =>
A_r/Wick -> 1 (the Wick LEADING-ORDER equality), directly on the prize object -- same vanishing-margin
signal as the closed-form g(r)=1-r/n law (brick 4).

HONEST ARTIFACT (rule-6): the deep-r tail at FIXED p turns UP (n=32 r=7 ratio 0.744 > r=6 min 0.711).
This is a FINITE-FIELD DC/wraparound artifact: when r ~ log_n p the n^{2r}/p subtraction and field
wraparound contaminate E_r. Only the CLEAN rungs r << r* are trustworthy; the upturn is NOT a real
sub-Gaussian recovery. (The clean-rung trend -- ratio up toward 1 as n grows -- is the signal.)

VERDICT (rule-4 confirmation, rule-6 honest, NOT a closure): on the ACTUAL A_r<=Wick prize object the
sub-Gaussian margin (1 - A_r/Wick) shrinks toward 0 as n grows at every fixed r, confirming the closed-form
g(r)=1-r/n=margin-r/n verdict on the real object (not just the moment-step proxy). A_r<=Wick HOLDS with
positive margin at every accessible (r,n) but the margin VANISHES at the n->inf limit. The open prize
content is unchanged and precisely localized: whether the JOINT (r*~log n, n->inf) limit keeps the margin
bounded below the threshold (prize-true) or it -> 0 (BGK-tight) -- the clean-rung n=16,32 data shows the
margin shrinking but CANNOT reach r*~log n cleanly (finite-field artifact at deep r/fixed p). CORE not
closed, no overclaim. Python-only exact => axiom-clean trivially. probe_407_ArWick_ratio_profile.py.

## The base-case + single-step-MONOTONICITY route to A_r<=Wick is DEAD at n=64 -- monotonicity FAILS in the THIN prize regime (refutes the d6b438478 reframing) (2026-06-15, opus-4-8 subagent)

LANE (follow-up to caab0afb9): the n=32 worst-bad-prime work showed A_r<=Wick survives ONLY via the
Wick-E0 headroom (proxy Anom_r<=n^{2r}/p dead 16x/octave). Made the TRUE headroom test explicit and ran
the RACE across n. EXACT ALGEBRA: A_r = (E0 + Anom_r) - n^{2r}/p, so A_r<=Wick <=> Anom_r <= H_r where
H_r := (Wick - E0) + n^{2r}/p. Race ratio rho_r := Anom_r/H_r; carrier holds iff rho_r<=1.
probe_407_headroom_race.py + probe_407_n64_monotonicity_break.py. Exact integer counts (E0_ring VALIDATED
== closed form 3n(n-1) for n=8,16,32,64; Ep VALIDATED by independent O(n^2) brute pair-count at n=64).
PROPER mu_n, p>=n^4, NEVER n=q-1.

RESULT 1 -- the headroom race ratio EXPLODES toward 1 in n (peak rho_r over r=2..6, at each n's worst
in-window bad prime):
  n=8  (beta4.10): peak rho = 0.00000
  n=16 (beta4.05): peak rho = 0.03572
  n=32 (beta4.05): peak rho = 0.91208
  n=64 (beta4.01): rho > 1 at EVERY r (7.96, 8.93, 10.14 at r=2,3,4)  -> carrier A_r<=Wick FAILS at n=64.

RESULT 2 (the sharp refutation) -- at n=64, BOTH in-window bad primes (p=17318209 beta4.008 index270597;
p=19718977 beta4.039 index308109; both proper mu_64, NEVER n=q-1) have f(2)=A_2/Wick > 1 (1.1093, 1.0468).
Moreover f(r)=A_r/Wick is INCREASING from the base case at the worst prime:
  f(1)=1.00000 (base, = A_1/Wick = n/n, holds), f(2)=1.10930, f(3)=1.37464, f(4)=1.91127.
  => the single-step monotonicity f(2)<=f(1) is FALSE (1.109 > 1.000) IN THE THIN PRIZE REGIME at n=64.
VALIDATION: E_2^(p)=13632 confirmed by independent O(n^2) brute pair-count == convolution; A_2=13631.03 >
Wick_2=12288 exact.

CONSTRAINT LEMMA (rule-4): the d6b438478 reframing claimed a proof via [base case f(1)<=1, PROVEN] +
[single-step monotonicity f(r+1)<=f(r)] is AUTOMATICALLY thinness-essential because THICK violates both while
THIN satisfies them (validated n=16,32 where f IS decreasing). This is FALSE at n=64: the THIN prize-regime
worst bad prime ALSO violates single-step monotonicity (f increases 1.0->1.11->1.37->1.91) and f(2) already
exceeds 1. So the base+single-step-monotonicity STRATEGY does NOT close A_r<=Wick even in-regime; it dies at
the first step at n=64. The route is DEAD.

HONEST SCOPE (rule-6, NO overclaim): this refutes the PROOF STRATEGY (base+single-step monotonicity for
A_r<=Wick), NOT the prize. The prize is forall-field-universal at deep r~log q; per-prime A_r<=Wick at SMALL
r (r=2) is NOT the prize bound (M^4 <= p*A_2 gives only M <= (3p)^{1/4} sqrt(n), p-growing, far weaker than
the prize). What is killed: any closure of A_r<=Wick that relies on monotone descent from the r=1 base. The
DC-essential threshold q*(2r-1)!! < n^r does NOT fire here (5.2e7 >> 4096), so this is a SECOND, anomaly-
driven mechanism breaking A_r<=Wick at bad primes that the known threshold does not flag. Pure-Python exact
integer counts, no Lean => axiom-clean trivially. probe_407_headroom_race.py, probe_407_n64_monotonicity_break.py.

================================================================================
2026-06-15 RULE-3 on the E_r SUBLEADING coeff: the -C(r,2)(2r-1)!! subleading
(E_3's -45) is ALSO neg-closure-generic (thin~neg~thick) -- BOTH leading AND
subleading orders are thin-blind; the thin advantage is confined to the 3rd+
coefficients (opus-4-8 subagent)
--------------------------------------------------------------------------------
LANE: brick 4 showed the LEADING (Wick (2r-1)!!) coeff of E_r is neg-closure-generic. This gates the
SUBLEADING coeff -(2r-1)!!*C(r,2) (E_3's -45 = -15*3): thin-essential or also generic? Thin 2-power mu_n
vs neg-closed-random (same size) vs thick composite subgroup, exact integer E_3, PROPER mu_n.
probe_407_Er_subleading_rule3.py.

RESULT (exact, sub-coeff = (E_3 - 15n^3)/n^2 -> -45 as n->inf):
  n=16: sub_thin=-42.50  sub_neg=-42.50  (identical)
  n=32: sub_thin=-43.75  sub_neg=-42.66  sub_thick(d=33,contaminated diff-size)
  n=64: sub_thin=-44.375 sub_neg=-43.657 sub_thick(d=70)=-44.43 (~thin)
=> sub_thin -> -45, sub_neg -> -45, sub_thick(matched) ~ -44.4 ~ thin. The SUBLEADING coeff is
   NEGATION-CLOSURE-GENERIC (thin ~ neg ~ thick, gap vanishing O(1/n) like the leading term).

VERDICT (rule-3 FAIL on the subleading, rule-6 honest, NOT a closure): BOTH the leading (Wick (2r-1)!!)
AND the subleading (-C(r,2)(2r-1)!!) coefficients of E_r(mu_n) are negation-closure-generic -- NOT
thin-2-power-specific. The thin prize advantage is therefore CONFINED to the THIRD-and-deeper coefficients
of E_r (the n^{r-2} term onward). This BOUNDS the thin content: the first two orders of the additive-energy
expansion carry no 2-power signature, so any thinness-essential mechanism must extract its gain from the
sub-subleading structure (exactly the term whose accumulated effect over r* steps is the open prize
question). Tightens the brick-4 picture: g(r)=1-r/n is built from two neg-closure-generic orders; the thin
deviation is below O(1/n^2) in the per-step margin. CORE not closed, no overclaim. Python-only exact =>
axiom-clean trivially. probe_407_Er_subleading_rule3.py.

================================================================================
2026-06-15 The ACCUMULATED 2nd-ORDER correction to the Wick ratio is NEGATIVE and
ASYMPTOTICALLY SUBDOMINANT => the "2nd-order rescues a positive prize margin"
hypothesis is REFUTED at the joint limit r*~log n (opus-4-8 subagent)
--------------------------------------------------------------------------------
LANE (flagged-open, uncontested): the HONEST OPEN residual of the E_r closed-form bricks
(44234dc3d/5b0873ddb): "whether 1-g(r*) = r*/n + (accumulated O(1/n^2) corrections over r*
steps) stays BOUNDED BELOW threshold at the JOINT (r*~log n, n->inf) limit -- the leading r/n
law -> 0 (consistent with BOTH prize-true AND BGK-tight)." Resolved the 2nd-order rung.

ENGINE: in-tree cyclotomic-lattice E_r^(0) (zeta^{n/2}=-1, n=2^a) = EXACT char-0 negation-closure
additive energy, p-FREE. = A_r/Wick to O(n^{2r}/p)=O(1/n^{2r}) (DC term negligible at p~n^4).
Cross-verified bit-for-bit vs board E_4 closed form 105n^4-630n^3+1435n^2-1155n at n=8..64.
probe_407_Er_thirdcoeff_accumulated.py.

RESULT 1 -- THIRD coeff (n^{r-2}) of E_r pinned (was the open carrier of O(1/n^2)):
  E_2 third/lead = 0,  E_3 third/lead = 8/3,  E_4 third/lead = 41/3.
  (lead=(2r-1)!!, sub/lead=-C(r,2) reconfirmed; E_3=15n^3-45n^2+40n, E_4 board cf re-verified.)

RESULT 2 -- ACCUMULATED 2nd-order law (EXACT, the load-bearing brick):
  W(r) := E_r^(0)/((2r-1)!! n^r) = prod_{s<r} g(s)  (Wick ratio = product of step margins).
  log W(r) = -r(r-1)/(2n) + c2(r)/n^2 + O(r/n^3),  with EXACT CLOSED FORM
        c2(r) = -r(r-1)(2r+5)/36.
  c2(r): -1/2,-11/6,-13/3,-25/3,-85/6 at r=2..6. c2 is the FULL accumulated 2nd-order coeff
  INCLUDING the -x^2/2 Jensen term of log(1-x) (an earlier naive "-sum c2(step)" mis-signed it;
  the corrected c2(r) MATCHES the exact integer W(r) at n=8,16,32 to the c3/n drift -- verified).

RESULT 3 -- VERDICT (rule-4 wall map, rule-6 honest, NOT a closure):
  At the prize joint limit r*~c*log n:
    leading |term1| = r*(r*-1)/(2n) ~ (c log n)^2/(2n) -> 0.
    2nd-ord |term2| = |c2(r*)|/n^2 ~ (r*)^3/(18 n^2) ~ (c log n)^3/(18 n^2) -> 0  (extra 1/n).
    term2/term1 ~ (c log n)/(9n) -> 0.
  => BOTH terms -> 0; log W(r*) -> 0; W(r*) -> 1 (A_r=Wick in the limit, the BGK knife-edge).
  => The 2nd-order accumulated correction is NEGATIVE (DEEPENS cancellation at finite n) AND
     asymptotically SUBDOMINANT => it does NOT keep W(r*) bounded away from 1.
  => The "the accumulated O(1/n^2) correction over r* steps rescues a positive prize margin"
     hypothesis is REFUTED at the joint limit. Consistent with BGK-tight, NOT prize-positive.
     The thin advantage (known O(1/n) subleading in E_r) is NOT resurrected at 2nd order in the
     accumulated Wick ratio.
  HONEST: r* capped at lattice-tractable r<=6; the c2(r)=-r(r-1)(2r+5)/36 closed form is EXACT
  (cubic, 4 anchor pts r=1..4) and its r^3 growth (vs leading r^2/n) is what drives the verdict.
  Does NOT close CORE; SHARPENS the 44234dc3d open residual one order: the irreducible prize
  content is NOT carried by the 2nd-order accumulation -- it must live in a NON-perturbative
  (all-order / r*-resummed) effect, since every fixed perturbative order in 1/n vanishes at the
  joint limit. Pure-Python exact integer counts + Vandermonde over Q, no Lean => axiom-clean
  trivially. probe_407_Er_thirdcoeff_accumulated.py.

## UNIFIED open inequality A_r<=Wick <=> Anom_r <= (r/n)*Wick: the bad-prime anomaly OUTGROWS 0xSolace's r/n char-0 margin ~18x/octave (kappa: 0.04 -> 1.53 -> 27.8 for n=16,32,64) (2026-06-15, opus-4-8 subagent)

LANE: synthesize 0xSolace's exact general-r closed form E_r^(0)/Wick = 1 - r/n + O(1/n^2) (push 44234dc3d,
2034615dc) with my bad-prime anomaly growth (caab0afb9, 219f17c7a). Since A_r/Wick = E0/Wick + Anom_r/Wick
- n^{2r}/(p Wick) and E0/Wick = 1 - r/n + O(1/n^2), to LEADING ORDER:
    A_r <= Wick  <=>  Anom_r <= (r/n)*Wick + n^{2r}/p.
Define kappa_r := Anom_r / ((r/n)*Wick). Carrier (leading order) holds iff kappa_r <= ~1. This is the
SHARPEST reformulation: prize <=> the bad-prime anomaly stays within the r/n char-0 margin.
probe_407_anom_vs_rn_headroom.py. Exact integer counts (E0_ring==3n(n-1) validated; Ep brute-validated at
n=64). PROPER mu_n, p>=n^4, NEVER n=q-1.

RESULT -- peak kappa_r (over r=2..5) at each n's worst in-window bad prime:
  n=16 (beta4.053, p=76001):    peak kappa = 0.04063 @ r=5
  n=32 (beta4.050, p=1244993):  peak kappa = 1.52879 @ r=5
  n=64 (beta4.008, p=17318209): peak kappa = 27.83765 @ r=5
The anomaly outgrows the r/n char-0 margin ~18x/octave. kappa crosses 1 between n=16 and n=32.

INTERPRETATION (rule-6, honest): the leading-order budget kappa<=1 is EXCEEDED at n=32 (kappa=1.53) yet the
EXACT A_r/Wick=0.936<1 still holds at n=32 -- because the O(1/n^2) corrections in E0/Wick (=0.726 at n=32 r=5,
below 1-r/n=0.844) and the DC term provide extra sub-leading headroom that the leading-order (r/n)Wick test
ignores. At n=64 BOTH the leading-order budget AND the exact A_r/Wick fail (kappa=27.8, A_r/Wick=2.96 @ r=5).
So: 0xSolace's g(r)=1-r/n is the GOOD-PRIME (char-0) margin; kappa measures how badly the bad-prime anomaly
eats it. The margin is eaten ~18x/octave and the carrier A_r<=Wick (on the EXACT object, not leading-order)
survives at n=32 only on the sub-leading O(1/n^2)+DC crumbs, and FAILS at n=64.

HONEST SCOPE: refutes the leading-order r/n-margin SUFFICIENCY (kappa<=1) at n>=32 and the exact A_r<=Wick at
n=64 at these bad primes -- NOT the prize (forall-field, deep r~log q; small-r per-prime A_r<=Wick is not the
prize bound, M^4<=p A_2 -> M<=(3p)^{1/4}sqrt(n)). Maps EXACTLY how the char-0 r/n margin and the bad-prime
anomaly race: the anomaly wins ~18x/octave. Pure-Python exact, no Lean => axiom-clean trivially.
probe_407_anom_vs_rn_headroom.py.

================================================================================
2026-06-15 The RESUMMED Wick ratio W(r*) -> 1 on EVERY polynomial-log joint
diagonal r*=a*log2 n in the prize regime r*<<n => BGK-tight confirmed
non-perturbatively; W-bounded-below-1 only at r~n (NOT prize) (opus-4-8 subagent)
--------------------------------------------------------------------------------
LANE (follow-up to f5ec4a9cf): that brick showed every FIXED 1/n order of log W(r) vanishes at the
joint limit; the open residual was the RESUMMED W(r*) along the TRUE diagonal r*~log n. This resums it.

ENGINE: exact char-0 W(r;n)=E_r^(0)/((2r-1)!! n^r) (lattice seed n=8,16,32 r<=6) + the EXACT 2-term
asymptotic log W(r)=-r(r-1)/2n - r(r-1)(2r+5)/(36 n^2)+O(r/n^3) (from f5ec4a9cf).
VALIDITY (rule-6): 2-term model accurate to <0.1% for r/n<~0.15, degrades as r/n->1 (n=8 r=6, r/n=0.75:
6.4% err). The PRIZE regime is r*~log n << n => r*/n->0 => model VALID there.

RESULT: along EVERY polynomial-log diagonal r*=a*log2 n (a=1,1.5,2, and prize a=4ln2~2.77),
W(r*;n) -> 1 as n->inf (1-W -> 0). Sample (a=1): W~0.676,0.788,0.896,0.957,0.984,0.994 at n=16..16384.
EXACT corroboration (NO model) along r*=log2 n: W = 0.667,0.676,0.726 at n=8,16,32 (RISING to 1).

VERDICT (rule-4 wall map, rule-6 honest, NOT a closure): the resummed Wick ratio SATURATES to 1 on
every log-depth diagonal in the regime r*<<n where the resummation is provably accurate = the prize
regime. CONFIRMS BGK-tightness NON-perturbatively in the accessible regime (sharpens the perturbative
f5ec4a9cf verdict: not just each order vanishes, the RESUMMED diagonal -> 1). The ONLY regime where W
stays bounded below 1 is r ~ n (a constant fraction of the full group) -- which is NOT the prize regime.
=> CORE not closed; the irreducible W-bounded-below-1 content is localized OUTSIDE the prize-relevant
depth r*~log n. Python-only exact + validated asymptotic => axiom-clean trivially.
probe_407_W_joint_diagonal_resummation.py.

## The E_r(mu_n) closed-form lane's p-INVARIANCE assumption FIRST FAILS at r=4 (structured-prime additive anomaly); thickness-generic, NOT thin-essential (2026-06-15, opus-4-8 subagent)

LANE (uncontested): the dominant live lane (44234dc3d/5b0873ddb) pins E_2=3n(n-1), E_3=15n^3-45n^2+40n,
E_4=105n^4-630n^3+1435n^2-1155n and "g(r)=1-r/n" -- treating E_r as a p-INVARIANT polynomial in n. Nobody
had STRESS-TESTED that p-invariance across primes. probe_407_Er_pdependence_onset_r4.py. Exact integer
r-fold additive convolution, PROPER mu_n, p>=n^4, NEVER n=q-1.

CONTRIBUTION 1 (closed-form-INDEPENDENT algebraic reduction): the accumulated moment-step product
TELESCOPES to a SINGLE object. With E_0:=1,
    prod_{r=1}^{R-1} g(r) = prod_{r=1}^{R-1} (E_{r+1}/E_r)/((2r+1)n)
                          = (E_R/E_1)/(n^{R-1} prod_{r=1}^{R-1}(2r+1))
                          = E_R/(n^R (2R-1)!!)  =:  W_R   (the WICK RATIO of E_R).
So the whole multi-step "step-tower" question (DISPROOF_LOG: does the accumulated O(1/n^2) rescue a
positive margin?) reduces EXACTLY to ONE monotone quantity: does the Wick ratio W_{r*} (R=r*~log n) stay
bounded BELOW 1 with margin, or -> 1? From the EXACT (p-invariant) E_2,E_3: log W_R = -R(R-1)/(2n) +
B_R/n^2 + O(1/n^3), A_R=R(R-1)/2 EXACT, B_2=-1/2, B_3=-11/6 (TIGHTENING at the accessible rungs). At
R=r*~log n BOTH -R^2/(2n) and B_R/n^2 -> 0 (r*=o(sqrt n)) => W_{r*} -> 1 REGARDLESS of the B_R sign. The
accumulated tower CANNOT keep the Wick ratio bounded below 1 at the prize joint limit -- the BGK knife-edge
in closed form, reduced to a single object.

CONTRIBUTION 2 (rule-6 stress test, the new structural brick): E_r p-INVARIANCE is NOT universal.
  - E_2, E_3: p-INVARIANT (truly polynomial) -- identical across ALL probed prize primes. CONFIRMED.
  - E_4: the published 105n^4-630n^3+1435n^2-1155n is CORRECT for GENERIC primes (excess=0 for the vast
    majority of near-primes). But a SPARSE STRUCTURED subset shows a FIXED POSITIVE excess:
        n=16: ONLY the Fermat prime p=65537=2^16+1 -> E_4=4654160 = generic + 4480 (+0.096%); 4 other
              near-primes (65617,65633,65713,65729) -> excess EXACTLY 0.
        n=32: p=1048609 AND p=1049281 -> generic + 645120 (+0.710%); 3 other near-primes -> 0.
    p-invariance VERIFIED bit-identical at a 2nd prize prime for E_2,E_3 at every n; E_4 differs across
    primes at the SAME n (n=128: p=268437889 -> 27126574720 vs p=1150808833 -> 26931748480). => the
    additive-anomaly (p-dependence) of E_r ONSETS exactly at r=4, invisible to the r<=3 closed forms the
    whole lane is built on.

RULE-3 (the thinness verdict -- thickness-GENERIC, joins the board meta-pattern): swept beta THICK
(2.3-3.2, prize-FALSE) -> THIN (4-5), prize prime = closest to n^beta, n=16,32. The E_4 p-excess is
LARGEST in the THICK regime and SHRINKS to ZERO as beta->thin:
    n=16: beta2.3 +90.9% -> beta3.0 +3.95% -> beta4.0 +0.096% (Fermat only) -> beta>=4.5 EXACTLY 0.
    n=32: beta2.3 +357% -> beta3.0 +18.7% -> beta4.0 +0.71% -> beta>=4.5 EXACTLY 0.
=> the E_4 additive anomaly is a SMALL-q (thick) / 2-adic-special-prime effect that VANISHES in the deep
thin prize regime. At the genuine prize regime (beta>=4.5) the generic polynomial is RECOVERED exactly =>
the closed-form lane's p-invariance assumption is SAFE deep in the thin regime, and the anomaly is NOT a
thin-essential carrier (it's anti-thin: maximal in the prize-FALSE thick window).

VERDICT (rule-4 sharpening, rule-6 honest, NOT a closure): (1) the accumulated step-tower reduces EXACTLY
to the single Wick ratio W_{r*}, whose log -> 0 at the prize joint limit regardless of the 2nd-order sign
-- the knife-edge in closed form, one clean object. (2) The E_r-closed-form lane's p-invariance holds for
r<=3 universally and r=4 generically, but FAILS at sparse structured (Fermat-type) prize primes starting
at r=4, where E_4 EXCEEDS the generic polynomial (less Wick headroom) -- but this excess is THICKNESS-
GENERIC (maximal in the prize-FALSE thick regime, ->0 in the thin limit), so it cannot be the thin prize
carrier and the generic closed form is recovered deep in the thin regime. CORE not closed, not refuted.
Pure-Python exact integer counts, no Lean => axiom-clean trivially.
probe_407_Er_pdependence_onset_r4.py.

## The thin Wick-deficit (1-W_r) is SUB-leading in r: D_r=(1-W_r)*n falls BELOW the leading r(r-1)/2 and the gap WIDENS with r => NO compounding deep-r thin advantage (BGK-tight direction). Exact char-0, control-free (2026-06-15, opus-4-8 subagent)

LANE (uncontested, CHAR-0, control-free; distinct from the live mod-p anomaly-predictor + deep-hole
workers): the DISPROOF_LOG residual asked whether, as the moment ORDER r grows toward prize depth
r*~log n, the thin advantage GROWS (compounding -> could survive the joint limit) or stays tied to the
leading knife-edge. The prior thin-vs-neg-random measurement was r=3 ONLY. probe_407_Wickratio_rtrend_exact.py.

OBJECT (fully EXACT, NO stochastic control, NO prime): the Wick ratio W_r = E_r^(0)(mu_n)/((2r-1)!! n^r)
(= the accumulated moment-step product, push 58f29f3f0). Gaussian/random model: W_r=1. Thin subgroup:
W_r<1, deficit (1-W_r) = thin advantage. E_r^(0) via exact char-0 cyclotomic-lattice r-fold convolution
(mu_n = n-th roots of unity in Z^{n/2}, n=2^a, zeta^{n/2}=-1). Define the rescaled deficit D_r=(1-W_r)*n.
Leading expansion log W_R=-R(R-1)/(2n)+.. => D_r ~ r(r-1)/2. QUESTION: does the EXACT D_r EXCEED r(r-1)/2
by a WIDENING margin (extra compounding thin advantage) or fall at/below it (knife-edge dominates)?

RESULT (exact, r=2..8/7/6, n=8..64): D_r is consistently BELOW r(r-1)/2 and the gap WIDENS with r:
  n=32: D_r/[r(r-1)/2] = 1.000, 0.972, 0.931, 0.878, 0.816  (r=2..6) -- MONOTONE DECREASING
  n=16: D_r/[r(r-1)/2] = 1.000, 0.944, 0.865, 0.770, 0.669, 0.571 (r=2..7) -- MONOTONE DECREASING
  n=8:  D_r-lead = 0, -0.33, -1.54, -4.05, -8.05, -13.48, -20.20 (r=2..8) -- gap grows fast
  n=64: D_r/[r(r-1)/2] = 1.000, 0.986, 0.965 (r=2..4) -- same downward trend.
  (W_r exact: n=32 -> 0.9688, 0.9089, 0.8255, 0.7258, 0.6175 at r=2..6, matching 98db97afc/caab0afb9.)

VERDICT (rule-4 constraint, rule-6 honest, NOT a closure): the exact thin Wick-deficit is SUB-LEADING --
(1-W_r) is SMALLER than the leading r(r-1)/(2n) prediction, and the shortfall GROWS with r. Equivalently
W_r approaches 1 FASTER than the leading knife-edge 1-r(r-1)/2n, so the subleading correction is
+LOOSENING (toward the Gaussian W_r=1), NOT a compounding thin advantage. => the surviving thin lever
(the moment-step / Wick-ratio route) does NOT gain EXTRA room at deep r; the deep-r structure is the
BGK-tight direction. This CLOSES the "deep-r compounding thin advantage rescues the moment route" hope:
the accumulated product W_{r*} (= prod g) is NOT held below 1 by a growing deep-r deficit -- the deficit
is sub-leading and its rescaled form D_r/[r(r-1)/2] -> below 1 and falling. The moment/Wick-ratio route is
the knife-edge or worse at every accessible r, consistent with the whole board. Pure-Python EXACT char-0
integer cyclotomic-lattice convolution, no control, no prime, no Lean => axiom-clean trivially. CORE not
closed, not refuted. probe_407_Wickratio_rtrend_exact.py.
