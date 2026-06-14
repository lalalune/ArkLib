# The agreement-spectrum moments channel: hypothesis ledger (pre-registered)

Issue #334, moments lane (O120/O122 successor). Written BEFORE the probes ran; every
hypothesis below carries its falsifier. Notation: `C = {p : deg p < k}` on a domain
`D ⊆ F_q`, `|D| = n`; agreement spectrum `a_j(u) = #{p ∈ C : |{x ∈ D : p(x) = u(x)}| = j}`;
`M_r` = the r-th moment tensor `Σ_u a_{j_1}(u)···a_{j_r}(u)`. Known (O120/O122): M1 is a
Lean theorem and M2 a probe-verified closed form, both domain-independent.

## The reduction this lane runs on (to be re-derived + cross-validated, H4)

Translation `v = u − p_r` collapses M3 to ordered codeword pairs:
`M3_{j1,j2,j3} = q^k · Σ_{(c,c') ∈ C²} N_{j1,j2,j3}(profile(c,c'))`, where the profile is the
per-coordinate 5-type census
(A: c=c'=0 · B: c=0≠c' · C: c'=0≠c · D: c=c'≠0 · E: both ≠0, distinct), and N is the
`[z1^{j1} z2^{j2} z3^{j3}]` coefficient of `Ā^a B̄^b C̄^c D̄^d Ē^e` with per-type factors

    Ā = z1z2z3 + (q−1)        B̄ = z1z3 + z2 + (q−2)     C̄ = z2z3 + z1 + (q−2)
    D̄ = z1z2 + z3 + (q−2)     Ē = z1 + z2 + z3 + (q−3)

Independent pairs organize by the 2-dim subcode `V` (dual point φ for k=3): with fiber
multiset `{m_P}_{P∈P¹}` of the basis map `x ↦ [c(x):c'(x)]`, ordered bases ↔ ordered
distinct triples `(P1,P2,P3)` with multiplicity `q−1` (PGL₂ sharp 3-transitivity), so
`Σ_{bases} = (q−1)·Σ_{triples} N(|A|, m_{P1}, m_{P2}, m_{P3}, s − Σm_{P_i})`.

For k=3 the fibers of the φ-pencil are the orbits of the Möbius involution
`x ~ y ⟺ φ₀xy − φ₁(x+y) + φ₂ = 0`, i.e. `(x−a)(y−a) = a²−b` after normalizing
`(a,b) = (φ₁/φ₀, φ₂/φ₀)` — so `m_P ∈ {1,2}`, and the whole profile distribution is the
statistic `φ ↦ (s(φ), t₂(φ), |A(φ)|)` with `t₂` = #σ_φ-orbit pairs inside D.

## Known-math hypotheses

**H1 (the central one). M3 at k=3 separates smooth subgroup domains from random domains.**
Constraints: M1/M2 are domain-independent, so any separation must enter through the pair
profiles that MDS distance data does not pin — exactly the `t₂` statistic. Mechanism: the
N-functional is cubic in `t₂` at fixed `(s,|A|)` (triple sums hit power sums p₂, p₃ of the
fiber multiset = `s + 2t₂`, `s + 6t₂`), so M3 sees `Σ_φ t₂²,  Σ_φ t₂³` — the pencil/involution
energy. For `D = H ≤ F_q*` the pencils `a = 0, −b ∈ H` give `σ(x) = −b/x` mapping H→H:
`t₂ ≈ n/2` on ~n pencils; random D has `t₂ ~ Bin(n²/2, 1/q)`-thin everywhere. Why nobody has
done it: the proximity-gaps literature works above the pair level (BCIKS/CS25-style second
moments); the joint-enumerator literature (MacWilliams–Mallows–Sloane biweight) does not
treat RS evaluation-domain dependence (lit-gate pending, see LIT). Novelty: the first
moment-level smooth/random distinction, with mechanism. Falsifier: exact probe equality of
M3 tensors at (q,n,k=3), subgroup vs random.

**H2. M3 at k=2 is domain-independent** (and the probe must confirm it exactly).
Reasoning: at k=2 every independent pair embeds D into P¹ injectively (the 2×2 determinant
identity `c(x)c'(y) − c(y)c'(x) = (y−x)(ad'−a'd)`), all fibers are singletons, `t₂ ≡ 0`,
and the three special points are rigid under sharp 3-transitivity — no moduli, no domain
dependence. Theorem-grade target after probe confirmation. Falsifier: any k=2 probe diff.

**H3. M2 + Chebyshev lands in Lean** on the in-tree substrate (RSWeightEnumerator + the
AgreementMomentOne pattern): `Σ_u a_j(u)² = Σ_d B_d·N_j(d)` and the first machine-checked
nontrivial max-list bound `max_u ℓ ≤ mean + √(q^n·Var)`-shaped. Known math; brick value is
the formal pin "domain-dependence cannot appear before M2" from the other side.
Falsifier: a missing MDS distance-distribution closed form in-tree makes this a 2-brick job.

**H4. The reduction above is exactly correct.** Pure double counting; the probe enforces
it as `brute force == decomposition`, exact integers, at ≥3 setups including k=2 and k=3
and a non-smooth domain. Falsifier: any mismatch (then the formulas above are wrong and
get fixed or withdrawn — the ledger keeps the diff).

**H5. First-moment pinning of t₂:** `Σ_φ t₂(φ) = C(n,2)·(q+1) − (coincidence corrections)`
— each pair {x,y} solves a 2-dim space of φ-conditions, a dual line. Consequence: any M3
difference comes from t₂-*variance* (energy), never the mean — the conceptual reason
M1/M2 stay blind. Provable by double counting; falsifier: probe sum mismatch.

## Advanced hypotheses

**A1 (the moduli law).** Domain-dependence of `M_r` at degree k turns on exactly when the
special-point configuration acquires moduli: `(k, r) = (2, ≤3)` and `(≥2, ≤2)` rigid
(3-transitivity), `(3, 3)` dependent via pencil energy (H1), and **`(2, 4)` dependent via
cross-ratio energy** — at k=2, M4's triples of codewords see 4 special points whose
cross-ratio is Möbius-invariant; AP domains concentrate (4-term APs have CR = 4/3),
GP domains concentrate per-ratio, random domains don't. Why new: this organizes
"derandomization sees nothing below moment 3" (O120's empirical toy verdict) into a
boundary LAW with the geometric mechanism (configuration moduli), testable at every cell.
Falsifier: M4(k=2) probe equality between AP and random, or any rigid-cell inequality.

**A2 (the exact ΔM3 formula).** ΔM3 between two domains with matched (q,n,k=3) is an
explicit cubic functional of their `(s, t₂, |A|)`-distributions over φ; the subgroup's
leading term is computable from the spiking pencils alone. Target: closed-form ΔM3 +
a proven asymptotic lower bound (the first *theorem* that a fixed moment distinguishes
smooth from generic). Falsifier: probe ΔM3 disagrees with the formula's prediction.

**A3 (δ*-relevance audit, honest).** The M3 excess, fed through third-moment tail
machinery, changes max-list bounds in the band by o(1) at prize parameters — i.e. the
separation is real but δ*-IRRELEVANT at scale. Expected outcome is a precise negative
(the excess is poly(n)·q^{-Θ(1)} against tails that need q^{-128} resolution); that pin —
"moment-3 information cannot move δ* because of magnitude, not blindness" — is the
honest deliverable. Falsifier: the excess feeds a tail improvement that survives scaling.

**A4 (the moment fingerprint).** The *sign pattern* of pencil-energy deviation classifies
the domain's arithmetic: multiplicative pencils `(x−a)(y−a)=c` spike ⟺ D has multiplicative
structure; additive pencils `x+y=c` (the `φ₀=0` family) spike ⟺ additive structure (APs);
both thin ⟺ pseudo-random. M3 restricted to pencil families = an Elekes–Szabó-type
degeneracy detector built from a code moment. Falsifier: AP domains failing to spike the
additive family, or subgroup spiking the additive one (beyond the forced `x+y=0` pencil
when −1 ∈ H).

**A5 (the torus-normalizer count).** The subgroup's spiking pencils are EXACTLY the
involutions in the normalizer of the split torus fixing H: maps `x ↦ c/x` with `c ∈ H`
(n pencils, t₂ = n/2 − O(1), the −1-eigenpoint corrections exact), plus nothing else
beyond Shkredov-bounded noise. Gives the exact leading coefficient in A2's formula.
Falsifier: probe finds spiking pencils outside the normalizer family (then the
classification is wrong and the extra family is itself a finding).

## LIT (gate complete, 2026-06-10)

* **MDS support weight distributions ARE parameter-determined** — Jurrius–Pellikaan (WCC
  2009), Thm 2: `A_w^(i)` closed form for MDS, all i ≤ k, via Tutte polynomial = uniform
  matroid; lineage Kløve 1992, Wei 1991, Tsfasman–Vladut 1995. Consequence: the domain
  question provably lives ABOVE the matroid level — in the internal pencil refinement.
  Their own boundary note: matroid invariants do not pin coset-leader enumerator/covering
  radius — consistent with M3 living higher.
* **MDS biweight determination: open both ways.** MMS72 defines the biweight enumerator;
  Kaplan (arXiv:1205.1277) has equal-weight-enumerator counterexamples (binary, NOT MDS);
  no theorem/counterexample found for MDS. The coarse 4-type profile (wt c, wt c',
  |supp∩supp'|) looks folklore-pinned for MDS via shortening — worth proving in-house
  (label folklore). The genuinely open refinement is the 5th type = the triangle
  distribution (wt c, wt c', wt(c−c')) — exactly this lane's object. Supporting:
  Brakensiek–Gopi–Makam (STOC'23): higher intersection invariants genuinely vary among
  equal-parameter MDS codes.
* **Third-order: nothing found.** Closest: Gao–Li arXiv:2205.02277 Thm 5 (factorial
  moments of the agreement count, FIXED word, random codeword — the transpose object;
  universal for m ≤ k) — position against it explicitly. CS25 (eprint 2025/2046) Lemma 2
  and DG25 (eprint 2025/2010) are second-order and implicitly domain-blind (MDS-only
  inputs); M1/M2 domain-independence should be framed as implicit in that line.
* **Mechanism asymptotics known**: Macourt–Shkredov–Shparlinski (Canad. J. Math 2018)
  Cor 4.1 — `E^×(G+λ) − |G|⁴/p` anomaly bounds = exactly the (x−a)(y−a)=c pair counts of
  H1/A5; Heath-Brown–Konyagin/Shkredov subgroup energy line. Cite, don't rediscover.
* **Phenomenon anticipated, statistic not**: BKR 2010 (subspace domains break Johnson);
  BCHKS 2025/2055 §1.4.1/§1.4.3 engineer structured domains (incl. multiplicative
  subgroups, conditional) for negative results; ABF26 explicitly hopes smooth-prime
  domains still behave. NO prior closed-form computable statistic separating smooth from
  random at fixed (n,k,q), and no indistinguishability theorem for a statistic class.
  Claim scope accordingly: (a) M3 pair-profile decomposition new in assembly; (b) k=3
  conic-pencil reduction new (dictionary classical — Dickson 1908, Lavrauw–Popiel–Sheekey
  nets of conics); (c) separation-as-computable-statistic new, phenomenon not.
  Risk flag: KK25 (Krachun–Kazanin) is unpublished personal communication in ABF26 —
  unauditable; do not assume its scope.

## Verdicts (2026-06-11 — appended after the probe run; pre-registration above unchanged)

H4 ✓ (7/7 exact cross-validations) · H2 ✓ (k=2 tensors exactly equal) · H1 ✓ (k=3
subgroup outside the random cloud at every cell, same sign, argmax always (2,2,2)) ·
H5 ✓ (asserted every run) · A5 ✓ for n ≥ 10 exactly, refined at n=8 (extra t₂=3
noise-band spikes) · A4 partial (AP separates at n=16 via additive pencils, not at
n=8; gpset never) · A2 established computationally (engine = the formula) · A1/A3
open (M4-at-k=2 cell and tail quantification = next cycle). Unplanned finds: exact
coset/affine invariance of all moments; the t₂ spectral gap {4,5,6} = ∅ for subgroup
domains at n=16. Full discussion: RESULTS-M3.md.

**Appended 2026-06-14 (D1 / #407, `probe_m3_prize_regime_excess.py`):** A3 now QUANTIFIED
at prize shape (proper 2-power μ_n, p ~ n^β). (a) Rigidity is sharper than H5: BOTH Σ_φ t₂
AND **Σ_φ t₂²** are exactly domain-independent — separation enters ONLY at Σ_φ t₂³. (b) The
absolute third-moment excess D3 = Σt₂³(μ_n) − E_rand is q-INDEPENDENT and → n⁴/8 (the
torus-normalizer involution-energy, verified n ≤ 128); the relative excess decays only
POLYNOMIALLY in q (q^{−0.14…−0.58}), NOT the raw-tensor q⁻⁴. Transfer verdict: smooth M3
> random ALWAYS (smooth measurably worse, transfer fails as a moment inequality), but the
signal is polynomial and BGK-INDEPENDENT (a Weil-pencil count, not a char sum).

## Probe protocol (exact arithmetic, no sampling on any claimed verdict)

1. `probe_agreement_m3_bruteforce.py` — full enumeration over all q^n received words,
   M3 tensor + M1/M2 re-verification. Ground truth at tiny scale.
2. `probe_agreement_m3_decomp.py` — the reduction engine (dual-point pencils at k=3,
   degenerate-pair closed forms, N-cache); MUST match (1) exactly on every shared setup,
   plus internal identities (pair-count partition `q^{2k} = 1 + 2(q^k−1) + (q^k−1)(q−1) +
   [k≥3]·(q²+q+1)(q²−1)(q²−q)/…`, tensor S₃-symmetry, H5 sum).
3. `probe_agreement_m3_experiment.py` — the separation matrix: k=3, q ∈ {41, 113, 257},
   D ∈ {subgroup, subgroup coset, 5× random, AP, random-multiplicative-non-subgroup},
   compare profile distributions AND M3 tensors; k=2 control (H2); per-pencil spike
   census (A4/A5). Verdicts in RESULTS-M3.md next to this file.
