# Are the two square-root boundaries the same phenomenon?
Working notes, 2026-06-12. Read-only analysis of /home/nubs/Git/ArkLib-232.

## SIDE A — the swarm's sharp band law (commits 0a741dfe1, 8081d3b7b, 3c96d7464)

File: ArkLib/Data/CodingTheory/ProximityGap/KKH26DimGeneralSharpPin.lean (+ InterleavedPin for the wall test).

Objects and parameters (canonical m = 1):
- Domain = the multiplicative subgroup ⟨g⟩ ⊆ F_p^× of order n_A = 2^μ (domain IS the subgroup).
- Code = evalCode g n (r−2): degree ≤ r−2 polynomials evaluated on ⟨g⟩ (very low rate (r−1)/n).
- BAD SCALARS (KKH26WitnessSpread.lean / kkh26_lemma1 in KKH26SumsOfRootsOfUnity.lean):
  λ_T = −Σ_{x∈T} x = −e₁(T) for r-subsets T of ⟨g⟩. The count ≥ 2^r·C(2^{μ−1}, r) is the
  number of ANTIPODAL-FREE r-subsets (S ∩ (−S) = ∅): choose r of the h = 2^{μ−1} antipodal
  classes {x,−x} and a sign each; distinctness of their e₁ values = injectivity of the signed-sum
  map sVal on sigData(h,r), from Φ_{2^μ} = X^h + 1 linear independence above p > s^{s/2}
  (the swarm's docstrings call the subgroup order s = 2^μ).
- The BAND: ε* ∈ [ (C(n,r)/r)/p , (2^r·C(2^{μ−1},r))/p ). Lower endpoint = sharp subset-OWNERSHIP
  upper bound on bad scalars of ARBITRARY stacks (each bad scalar owns ≥ r non-fit r-subsets,
  disjointly ⇒ #bad ≤ C(n,r)/r). Upper endpoint = the explicit family mass. In the band,
  δ* is pinned EXACTLY: mcaDeltaStar = 1 − r/2^μ (kkh26_dimGeneralSharp_deltaStar_pin_canonical).
- dimGeneralSharp_band_nonempty (THE band law): r ≥ 2 ∧ r² < 2^μ ⟹ C(2^μ,r)/r < 2^r·C(2^{μ−1},r).
  Pure binomial inequality; proven via falling-factorial induction; SUFFICIENT, NOT SHARP for the
  band (8081d3b7b honesty fix: general theorem = r < √n; √(n·ln n) is heuristic only).
- μ=4 wall test (3c96d7464): band truth at n=16 is r ≤ 6 (C(16,6)/6 = 1334 < 1792 = 2⁶·C(8,6)),
  closes at r = 7 (1634 ≥ 1024). Note 5,6 are PAST the proven criterion (25,36 ≥ 16).

Exact band walls computed (first failing r): μ=3→4, μ=4→7, μ=5→11, μ=6→17, μ=7→27, μ=8→41,
μ=9→62. So A's true wall grows like √(n ln n); the proven criterion r<√n covers only its bottom.

## SIDE B — the census sharp activation law (scripts/probes/genlaw/exclusion/REPORT.md)

- Scale s = 2^j, evaluation domain μ_n with n_B = 2s, code RS degree < s (rate 1/2),
  word w = X^{s+2} − z*·X^s. N_r(s) = # feasible (O, m, B): r O-fibers in Z_s with sign lifts
  (m₁ = 0 quotients global negation), b = (s+1−r)/2 B-fibers, the multiset
  {a_i+a_j}_{i<j} ⊎ {2o_i} ⊎ {2f: f∈B} ⊎ {3s/2} antipodally balanced in Z_n (Lam–Leung).
  N_r(s) > 0 ⟺ the agreement-(s+1) marginal layer has pattern-(b,r) codewords.
- LAW (CONJECTURED, 26/26): N_r(s) > 0 ⟺ r² ≤ s+1 ⟺ C(r,2) ≤ b. Proven skeleton: T1 parity
  purity (all scales; N_r(s)=0 for r > s/2), T3 doubling monotonicity, T4 s=32 closure,
  29 certificates (N_11(128)>0 … N_19(512)>0). s=8 tight: N_3(8)=8 with 9 ≤ 9, b = C(3,2) = 3.
- Boundary derivation: T' = C(r,2)+r+1 non-B terms, absorption X+F ≥ T'−b (r5tax DERIVED-99512 §2
  general form); law boundary ⟺ "required absorption ≤ r+1". Measured kill is per-axis capacity
  (REPORT §3.4 explicitly REFUTES the aggregate budget as mechanism).

## THE DICTIONARY (pinned exactly)

Two candidate matchings; the structural one is D2:

D2 (substrate match): **A's 2^μ = B's s** (A's order-2^μ subgroup ⟨g⟩ ↔ B's order-s subgroup
μ_s = squares of the 2s-point evaluation domain); hence A's h = 2^{μ−1} antipodal classes
= B's s/2 axes; **A's r = B's r** (cardinality of the signed subset).
- LITERAL object identity: B's pure (O,m)-config = r lifted points ±ζ_s^k over r distinct
  same-parity fibers = an antipodal-free r-subset of μ_s = exactly A's elemSet(sigData(h,r)).
  Counts: B pure(s,r) = 2·C(s/2,r)·2^{r−1} = 2^r·C(s/2,r) = A's family count.
  Verified: pure(16,5)=1792=2⁵C(8,5); pure(16,7)=1024=2⁷C(8,7); pure(32,7)=1,464,320=2⁷C(16,7);
  pure(32,5)=139,776; pure(8,3)=32. The numbers 1792/1024 in A's μ=4 wall test ARE the sizes of
  B's (16,r) pure config spaces.
- LITERAL quantity identity: A's bad scalar λ_T = −e₁(T) = B's ξ = −Σx_i (the L4 quantity).
- Shared proven bedrock: Lam–Leung 2-power antipodal decomposition — the SAME in-tree bricks
  (LamLeungTwoPow.vanishing_iff_antipodal_coeffs, LamLeungMultisetAntipodal.multiset_antipodal_iff);
  RESULTS-GENERAL-LAW §6 records the census's own brick as redundant against the swarm's.

D1 (domain match, 2^μ = 2s): same index identity without purity; REJECTED as the law-comparison
frame because the boundaries then differ by √2 and matched points give counterexamples (below).

## THE OFF-BY-ONE (exact, in B's budget coordinates, under D2)

For odd r, 2-power s, b = (s+1−r)/2:
- A's strict criterion r² < 2^μ = s  ⟺  r² ≤ s−1  ⟺  **C(r,2) ≤ b − 1**.
- B's law r² ≤ s+1  ⟺  **C(r,2) ≤ b**.
Truth sets on the whole 2-power lattice are IDENTICAL except where r² ∈ {s, s+1}: r² = s is
impossible (parity), and r² = s+1 ⟺ (r−1)(r+1) = 2^j ⟺ (s,r) = (8,3) — THE UNIQUE tight point,
exactly the census's boundary-tight anomaly (N_3(8) = 8, budget exactly saturated, C(3,2)=3=b).
At (8,3) A's strict criterion misses (9 < 8 false) but A's band TRUTH is still nonempty
(C(8,3)/3 = 18 < 32 = 2³C(4,3)) — the strict form is just not tight there.
Ladder check (D2): A-crit odd-r reach per s: 8→(1), 16→3, 32→5, 64→7, 128→11, 256→15, 512→21
= the census's predicted r_max ladder exactly (incl. the open (512,21): both say ON; and
(64,9), (128,13), (256,17), (512,23): both say OFF).

## WHY THEY ARE NOT THE SAME FACT (the decisive checks)

1. Different quantities. A's law: a CARDINALITY COMPARISON (#all r-subsets)/r < #antipodal-free
   r-subsets — equivalently the antipodal-birthday deficit ∏_{i<r}(1 − i/(n−i)) > 1/r. Nothing is
   constrained; every T is bad. B's law: NONEMPTINESS of the balance-CONSTRAINED stratum (the
   e₂-layer: pairwise sums must antipodally cancel against b B-doubles). A is about e₁-spectrum
   size; B is about e₂-multiset balance, on the same objects.
2. The true boundaries of the two quantities diverge. A-band truth at μ=4 (= D2 s=16): r ≤ 6.
   Census truth at s=16: r ≤ 3 (N_5(16) = 0 PROVEN by 3-way enumeration). So "A's quantity" and
   "B's quantity" have different walls at the same dictionary point; only A's NON-SHARP proven
   criterion coincides with B's conjectured-SHARP law.
3. Matched-domain (D1) counterexamples: (μ=5,r=5): band nonempty (40,275 < 139,776, and proven
   since 25 < 32) yet N_5(16) = 0 PROVEN. (μ=6,r=7): band nonempty (proven, 49 < 64) yet
   N_7(32) = 0 PROVEN (215,414,784-config full sweep).
4. Asymptotics differ: A's true band wall ~ √(n ln n) (walls 6,10,16,26,40,61 at μ=4..9);
   B's law is sharp at r ~ √s. Same √ shape, different constants and growth.
5. Mechanisms differ even at the proof level: A's inequality is a falling-factorial/birthday
   ratio bound; B's boundary algebra is the absorption budget C(r,2) ≤ b, and B's own report
   REFUTES the aggregate budget as the operative kill (it's per-axis capacity |d_c| ≤ 1).

## TRANSFER AUDIT (what would be NEW if unified)

- A's proven band theorem ⇒ any cell of B's law? NO. It is a binomial inequality about counts of
  unconstrained objects; it asserts nothing about existence of balanced configs. It does not even
  mention B's code (and no parameter choice makes the codes equal: A needs degree r−2 with
  r ≤ 2^{μ−1}; B's degree s−1 would need r = s+1).
- B's T1/T3/certificates ⇒ anything A lists as open? NO. A's open item (√(n ln n) general band
  asymptotic) is pure binomial analysis. The Lam–Leung foundation B uses is ALREADY the swarm's
  in-tree brick (B's was redundant — the one genuine unification already happened, at the
  foundation layer, documented in RESULTS-GENERAL-LAW §6).
- What IS real and worth recording: the substrate identity (same signed r-subsets, same λ_T = ξ
  = −e₁ quantity, same Lam–Leung bedrock) and the exact ±1-budget correspondence of the two
  boundary inequalities with the unique (8,3) divergence. This is a conjecture-shaping
  cross-reference (it explains why both lanes independently hit "r² vs scale": both count
  C(r,2) pairwise interactions against ~scale/2 antipodal classes of linear capacity), not a
  theorem transfer. NOT paperworthy as unification; valuable as a warning against conflating
  the two r²-walls (they sit at different constants for the same dictionary point).

## VERDICT
RELATED-BUT-DISTINCT. Same combinatorial substrate and literally shared Lean foundation; the two
square-root boundaries are different theorems about different quantities whose truth values
provably diverge at matched parameters; the striking exact agreement is between A's non-sharp
SUFFICIENT criterion and B's conjectured SHARP law (C(r,2) ≤ b−1 vs ≤ b, sole 2-power divergence
(8,3)) — a coincidence of proof-reach with truth, not one phenomenon.
