# The reciprocal branch — parameterization, maximizer check, extended census (ArkLib#371)

Follow-up to RESULTS-CHAR0.md / RESULTS-CHAR0-RIGOR.md / RESULTS-COUNT6-CLASSES.md and
DISPROOF_LOG O155/O156.  Scripts: `probe_reciprocal_param.py` (tasks 1–2, artifacts in
`results_reciprocal_param.json`) and `probe_reciprocal_census.py` (task 3, artifacts in
`results_reciprocal_census.json`).  Exact integer arithmetic throughout (negacyclic ring
Z[x]/(x^m+1), m = n/2, n a power of two); mod-p work at split primes p ≡ 1 (mod n),
p > 2^28.  Definition used VERBATIM (Beukers–Smyth 2002): f is RECIPROCAL iff f is
equivalent — up to a monomial·scalar factor — to f̄(x^{-1}, y^{-1}), where bar is complex
conjugation, acting on cyclotomic data as ζ → ζ^{-1}.

Notation as before: surface points P(i,j) = (ζ^{i+j}, ζ^j, ζ^i, 1), hyperplane normal
u = (u0,u1,u2,u3) read as (c, d, −a, −b); the attached (1,1)-curve is
f(x,y) = c·xy + d·y − a·x − b = u0·xy + u1·y + u2·x + u3  (x = ζ^i, y = ζ^j).

## 1. Task 1 — the conjugate-reciprocal condition, derived and machine-verified

Each step below is verified by a named check in `probe_reciprocal_param.py` (all checks
ran clean; counts in `results_reciprocal_param.json`).

**D1 (coefficient extraction — V1, 200 random u at each n ∈ {8,16,32}, 0 failures).**
f̄(1/x,1/y) = ū0/(xy) + ū1/y + ū2/x + ū3; multiplying by the monomial xy gives, in the
basis (xy, y, x, 1), the coefficient vector rev(ū) = (ū3, ū2, ū1, ū0): conjugate then
REVERSE.

**D2 (the monomial factor xy is forced — V1b, exhaustive over all 15 supports).**
x^A y^B·f̄(1/x,1/y) has support (A,B) − supp(f); support matching forces (A,B) = (1,1)
when all four coefficients are nonzero, and admits NO integer solution when exactly one
coefficient vanishes (size-3 supports) — such curves are never reciprocal.  (For the
maximizers this is moot: every count-6 class has all four coefficients nonzero —
verified, §2; indeed the spanning identity D6 forces the zero-pattern to be
reversal-symmetric, and non-normalizer-ness then excludes any zero at all.)

**D3 (the four coefficient relations — V1).**  f reciprocal ⟺ ∃ λ ∈ K*:
rev(ū) = λ·u, i.e.

    ū_k = λ · u_{3−k}   (k = 0,1,2,3)        — conjugation = reversal × λ,

equivalently in (a,b,c,d) letters:

    c̄ = −λ·b ,   d̄ = −λ·a ,   ā = −λ·d ,   b̄ = −λ·c .

(λ ∈ ℂ adds nothing: both sides are K-vectors, so proportionality forces λ ∈ K.)

**D4 (consistency ⟹ λλ̄ = 1 — V2, 100 random constructions per n, fit found and
unique every time; one-coefficient perturbations never fit).**  Conjugating ū_k = λu_{3−k}
and substituting the partner relation gives (1 − λλ̄)·u_k = 0 for every k; u ≠ 0 in the
integral domain Z[ζ] (Φ_n irreducible) forces λλ̄ = 1.

**D5 (normalization caveat — the prompt's "λ = ±ζ^t by unit structure" is NOT automatic;
V3).**  λλ̄ = 1 does not by itself place λ in {±ζ^t}: λ0 = (3+4i)/5 with i = ζ^{n/4}
satisfies λ0·λ̄0 = 1 (verified integrally: (3+4i)(3−4i) = 25) and is not ±ζ^t (verified:
5ζ^T ≠ 3+4i for every T); an explicit INTEGRAL reciprocal normal with λ = λ0 was
constructed (relations verified integrally as 5·Ū_k = (3+4i)·U_{3−k}) and fits NO root of
unity.  Scaling u ↦ μu transforms λ ↦ λ·μ̄/μ, so λ is only a class invariant in
K*/{μ̄/μ}; by Hilbert 90 every λ with λλ̄ = 1 is of the form μ/μ̄, so up to K-scaling one
may always normalize λ = 1.  What restores ±ζ^t for concrete representatives:
- *primitivity*: if u is integral with content (1), then (λ) = content(ū)/content(u) =
  (1), so λ is an algebraic-integer unit with |σ(λ)| = 1 at every embedding (λλ̄ = 1 and
  bar commutes with embeddings of the abelian field K), hence a root of unity by
  Kronecker, hence λ ∈ μ(K) = ⟨ζ⟩ = {±ζ^t, 0 ≤ t < m} (paper argument; checked on the
  data through D6 rather than assumed);
- *cross-product representatives*: λ is an explicit power of ζ — next item.

**D6 (THE SPANNING IDENTITY: reciprocity is automatic, with explicit λ — V4, exhaustive
at n = 8 over all C(63,2) = 1953 triples, random at n = 16/32/64/128/256, 0 failures;
plus a 2000-sample mod-p spot check inside every census run).**  Let J be coordinate
reversal (x0,x1,x2,x3) ↦ (x3,x2,x1,x0).  Then det J = +1, J^{−T} = J, and
J·P(i,j) = ζ^{i+j}·P(−i,−j).  The generalized cross product obeys
cross(JA,JB,JC) = det(J)·J^{−T}·cross(A,B,C), so for any surface triple
(P(0,0), P(i1,j1), P(i2,j2)) with v = cross(...) and Σ = i1+j1+i2+j2 (mod n):

    rev(v) = ζ^Σ · v̄        i.e.        v̄_k = ζ^{−Σ} · v_{3−k} .

**Every hyperplane spanned by a rank-3 triple of surface points is conjugate-reciprocal
with λ = ζ^{−Σ}** (sign absorbed: ζ^m = −1, so ζ^T realizes ±ζ^t, t < m).  Torus
translation by (s,t) preserves this with λ ↦ λ·ζ^{−(s+t)}, so "through P(0,0)" is WLOG.
Consequences:
- The BS dichotomy is decided wholesale here: any plane whose incidence set has K-rank 3
  (in particular every census plane with count ≥ 3, and a fortiori every count-6
  maximizer) is reciprocal — the BS non-reciprocal ≤ 4V branch never competes.
  Sharper, exactly: an invertible non-normalizer NON-reciprocal plane has **≤ 2** surface
  points (3 points are either rank 3 ⟹ reciprocal, or rank 2 ⟹ on a coordinate-line
  flat — census-verified to be the only flats — ⟹ ≥ 2 points on a coordinate line ⟹
  singular, RESULTS-CHAR0-RIGOR §1b).
- The ≤6-for-all-n question lives ENTIRELY inside the λ-parameterized reciprocal family,
  as O156 framed it; no separate non-reciprocal case remains.

**D7 (family dimension: half — V5, exact mod-p rank for every λ = ζ^T at
n ∈ {8,16,32}).**  Fix λ with λλ̄ = 1.  The relations leave (u0, u1) ∈ K² free and
determine u2 = λ̄·ū1, u3 = λ̄·ū0.  The constraints are K⁺-linear (K⁺ = maximal real
subfield), not K-linear: the family is a K⁺-subspace of K⁴ of K⁺-dimension 4 = HALF of 8
("roughly half the full 3-dim projective space", as expected).  Verified exactly at a
split prime in the two-evaluation model (u(z_p), u(z_p^{-1})) ∈ F_p^8, where conjugation
is the slot swap: the 8×8 relation system has rank exactly 4 (nullity 4) for every
λ = ζ^T, every T ∈ [0, n).  Moreover the projection of the solution space onto the
single-evaluation slot is ALL of F_p^4 — **the reciprocity filter is invisible to
one-embedding mod-p data** (it constrains the pair of conjugate evaluations, not either
one alone).  This kills any "enumerate reciprocal normals directly mod p" shortcut and is
why the extended census (task 3) enumerates spanned planes, where reciprocity is
automatic by D6.

**Explicit parameterization of reciprocal normals (summary).**  Given λ = ±ζ^t (the
form every primitive-integral or cross-product representative takes; general K-scalings
reach any λ with λλ̄ = 1, normalizable to λ = 1 by Hilbert 90):

    u = ( u0 , u1 , λ̄·ū1 , λ̄·ū0 ) ,   (u0, u1) ∈ K² free,

subject for census admissibility to: non-normalizer (u0,u3) ≠ (0,0) ∧ (u1,u2) ≠ (0,0)
(under reciprocity, equivalent to u ≠ 0 having NO zero coordinate, since the zero
pattern must be reversal-symmetric), and invertibility u0u3 − u1u2 ≠ 0.  Free
K⁺-dimension 4 of 8; one K-projective parameter pair after scaling.

## 2. Task 2 — maximizer check (the falsifier): ALL count-6 classes are reciprocal

Pipeline per class (every count-6 symmetry class in `results_count6_classes.json`):
mod-p reconstruction first (6×4 matrix of reduced points at the class's split prime
~2^28; rank verified = 3; 1-dim nullspace normal), then EXACT reconstruction in
Z[x]/(x^m+1) (cross product of the first rank-3 triple through (0,0), à la
`char0_witness_check.py`), consistency of the two (exact normal reduces mod p to a
scalar multiple of the mod-p nullspace), CHAR-0 RE-VERIFICATION (all six incidences
vanish identically in the ring; non-normalizer; det ≠ 0; full exact incidence count
over (Z/n)² equals 6), then the reciprocity scan: all λ = ζ^T, T ∈ [0, n) (this
enumerates ±ζ^t, t < m, since ζ^m = −1), testing ū_k = λ·u_{3−k} exactly.

| n | p | classes | rank-3 + exact-count-6 re-proven | reciprocal | λ = ζ^{−Σ} hit | λ unique | all 4 coeffs ≠ 0 |
|---|---|---------|----------------------------------|------------|----------------|----------|------------------|
| 16 | 268435537 | 34 | 34/34 | **34/34** | 34/34 | yes | yes |
| 32 | 268435649 | 210 | 210/210 | **210/210** | 210/210 | yes | yes |

**maximizers_all_reciprocal = TRUE.**  No failing class — BS is consistent with the
census and, by D6, necessarily so: the only way a class could have failed is an error in
the census/anchor data itself, and the exact re-verification independently excludes that
(each of the 244 class representatives is now PROVEN to be a char-0 count-6 plane: the
single-prime classification data is upgraded to characteristic zero).  Every class fits
exactly one λ = ζ^T, always the predicted T ≡ −Σ (mod n) for its spanning triple; the
exponents are spread (14 distinct values at n=16, 31 at n=32; parity balanced), so λ is
a genuine per-class invariant, not a constant.

Witness family S(n) = {(0,0),(1,1),(2,3),(4,m+2),(m−1,n−3),(n−2,n−1)} (cross product of
(P(0,0), P(1,1), P(2,3)), Σ = 7): exact count 6 and reciprocity with the predicted
λ = ζ^{−7} verified at **n = 8, 16, 32, 64, 128, 256** — T = 1, 9, 25, 57, 121, 249
respectively, all ≡ −7 (mod n).  This also extends the exact char-0 anchor:
**M(128) ≥ 6 and M(256) ≥ 6 are PROVEN** (no mod-p reduction involved).

## 3. Task 3 — extended census within the reciprocal family at n = 128

By D6 the "filter to reciprocal planes" passes every plane spanned by surface points
(and by V5 no one-embedding mod-p enumeration could see the filter anyway): the honest
reciprocal census IS the spanned-plane census.  `probe_reciprocal_census.py` is an
independent reimplementation of the dedupe + recount paths (addressing the O156
census-debt note): streamed gzip key emission from 6 worker processes (nothing
key-shaped materialized in RAM — the previous in-RAM probe OOM'd), external disk sort
with compressed temps for exact multiplicities, and a NEW exact recount algorithm —
Möbius O(n) per plane (z^j = −(v2 z^i + v3)/(v0 z^i + v1) must land in ⟨z⟩; batched
modular inversion; den = 0 ⟹ num ≠ 0 asserted, else the plane would be singular) —
validated in-run against the brute O(n²) counter on 200 planes per run.

**Gates (same smallest split prime as the original census): bit-identical histogram
reproduction** at n = 32, p = 268435649 ({3:326472, 4:28056, 5:260, 6:1932}) and at
n = 64, p = 268435649 ({3:6778728, 4:249368, 5:580, 6:9420}); rank-2 triple counts equal
the (n−1)(n−2) coordinate-line prediction; flats are exactly the two coordinate lines.

### n = 128 runs (two smallest split primes > 2^28)

| p | z | distinct planes thru P00 | histogram {count: planes} | M_p | count-6 | planes > 6 | wall |
|---|---|--------------------------|---------------------------|-----|---------|------------|------|
| 268437889 | 262205760 | 123 518 480 | {3: 121 416 072, 4: 2 059 896, 5: 1220, 6: 41 292} | **6** | **41 292** | **0** | 332 s |
| 268438657 | 1265863 | 123 516 112 | {3: 121 412 520, 4: 2 061 080, 5: 1220, 6: 41 292} | **6** | **41 292** | **0** | 341 s |

- **M_p(128) = 6 at both primes; not a single plane above 6.**  With the exact lower
  bound (§2), the constant-6 law extends to n = 128 at two-prime-evidence strength:
  **M(128) = 6 modulo the invisibility caveat** (§4.1).  S(128) is a verified member of
  the count-6 family (exact, §2); the per-prime "top" sets listed in the JSON are
  hex-key-ordered samples of the 41292-member tie, not a canonical argmax.
- **First mod-p surplus ever observed in this program** — and it is confined BELOW
  count 5: the two primes disagree slightly in the count-3/count-4 buckets
  (Δcount3 = 3552, Δcount4 = −1184, Δdistinct = 2368) while count-5, count-6, and the
  maximum are bit-identical.  At n ≤ 64 all ladder histograms were fully identical;
  at n = 128 the fixed cyclotomic resultants begin to capture primes of size ~2^28, as
  the height analysis predicts.  The surplus direction is exactly the safe one: it can
  only inflate mod-p counts, never hide a char-0 plane that stays admissible.
- Engine integrity per run: rank-2 triple count = (n−1)(n−2) = 16002 exactly (the two
  coordinate-line flats, identically-singular pencils); pair enumeration complete
  (134 193 153); spanning-identity spot check 0 failures; Möbius recount validated
  against the brute counter on 200 planes per run.

### Char-0 certificates for every count-5 / count-6 plane (mode `verify6`)

For a cross-product normal v of a surface triple, |σ(v_k)| ≤ 3√3 (RESULTS-CHAR0-RIGOR
§1c), so every incidence value ξ = v·P(i,j) has |σ(ξ)| ≤ 12√3 and N(ξ)² ≤ 432^m; by the
norm/divisibility lemma, vanishing at k distinct split primes with (∏p_i)² > 432^m
forces ξ = 0 EXACTLY.  Fixing ONE char-0 rank-3 triple per plane and intersecting its
mod-p incidence sets over such a ladder therefore computes the EXACT char-0 incidence
set.  Ladders used: k = 2/3/4/7/12 primes at n = 8/16/32/64/128 (each one more than the
exact integer requirement; zero degenerate reductions encountered).  Results
(`results_count56_verify.json`): **every single count-5 and count-6 mod-p plane is a
true char-0 plane of the same count — 0 failures**:

| n | count-6 mod-p | count-6 char-0 PROVEN | count-5 mod-p | count-5 char-0 PROVEN |
|---|---------------|----------------------|---------------|----------------------|
| 8 | 12 | 12 | 20 | 20 |
| 16 | 300 | 300 | 100 | 100 |
| 32 | 1932 | 1932 | 260 | 260 |
| 64 | 9420 | 9420 | 580 | 580 |
| 128 | 41 292 | **41 292** | 1220 | **1220** |

So the char-0 count-6 tally at n = 128 is ≥ 41292 PROVEN (and = 41292 at two-prime
evidence strength); same for 1220 count-5 planes.  The mod-p surplus at n = 128 touched
only the 3/4 buckets, exactly as the cross-prime agreement suggested.

### Growth law (the 12 / 300 / 1932 / 9420 sequence)

Exact rational fits (no rounding):

- **count-6(n) = (n − 4)(11n − 76)/4** — the quadratic through (16, 300), (32, 1932),
  (64, 9420) back-predicts n = 8 (12) exactly and FORWARD-PREDICTED n = 128 as 41292
  before the census ran; the census returned exactly 41292 at both primes (and the
  char-0 certificates prove ≥).  Five-for-five exact.
- **count-5(n) = 10(n − 6)** — the line through (16, 100), (32, 260) hits all five
  measured n exactly (20, 100, 260, 580, 1220).
- count-4 and count-3 follow NO low-degree polynomial law: the cubic through
  n = 16..128 misses n = 8 badly (−363/2 vs 88, resp. −1287951/2 vs 336), and at
  n = 128 these two buckets are the ones carrying mod-p surplus, so their values are
  prime-dependent there anyway.

Status of the two laws: exact theorems-by-census at n = 8..64 in both directions
(mod-p tallies + char-0 certificates + clean rigor ladders for the max), proven lower
bounds + two-prime-exact-match at n = 128.  A closed-form derivation (e.g. via the
λ-parameterized reciprocal family of §1) is the natural next brick; note
count-6(n) ~ (11/4)n² while planes-through-P00 grow ~ n⁴/2 — the maximizers are a
vanishing fraction with a clean quadratic law, strong structure for the ≤6-for-all-n
mechanism hunt.

## 4. Honest caveats

1. **Direction of the single-prime evidence, stated carefully.**  Reduction at a split
   prime preserves char-0 incidences, so for any char-0 plane that stays admissible
   mod p, its mod-p count ≥ its char-0 count: surplus inflates, never deflates.  This
   makes each mod-p histogram an upper-bound ladder rung for the planes VISIBLE at p —
   but it is NOT by itself decisive for M(128) ≤ 6, because a hypothetical char-0
   7-incidence plane can be INVISIBLE at p when p divides one of its three fixed case
   integers (normalizer-collapse norms D_bc, D_ad ≤ 3^{3m/2} or determinant norm
   D_det ≤ 54^m — the invisibility trichotomy of RESULTS-CHAR0-RIGOR).  Rigor at
   n = 128 needs a clean ladder of k(128) = 2·cap(3^96) + cap(54^64) + 1 = 2·5 + 13 + 1
   = **24 distinct clean split primes** (> 2^28); at n = 256, k(256) = 2·10 + 26 + 1 =
   **47**.  The runs here are evidence (strong, and two-prime agreement strengthens it),
   not a proof of the upper bound; the lower bound M(128) ≥ 6, M(256) ≥ 6 IS proven
   (exact, §2).
2. **Kronecker/primitivity step (D5) is a paper argument at the general level**: machine
   verification covers the counterexample (norm-1 ≠ root of unity), every concrete
   class representative (each fits a unique λ = ζ^T), and the spanning identity, but no
   general "content of ū = λ·content(u)" computation over Z[ζ] was run.  Nothing
   downstream depends on the general statement: all data-level claims use D6 directly.
3. **BS applicability**: BS 2002 is about irreducible curves; here f = c·xy+dy−ax−b is
   reducible ⟺ ad − bc = 0 (it factors as c^{-1}(cx+d)(cy−a) exactly when ad = bc), so
   census admissibility (invertibility) = irreducibility, and V = 1 for bidegree (1,1).
   The consistency claim "count-6 ⟹ must be reciprocal" used BS as motivation; the
   verification here (D6 + per-class scans) is self-contained and does not lean on BS.
4. **Scope of "reciprocal census = spanned census"**: planes with ≤ 2 surface points
   (including all non-reciprocal invertible ones, by §1-D6) are invisible to a
   triple-spanned enumeration — irrelevant for maxima (6 ≥ 3) and for the count-≥3
   histogram, which is what M(n) and the count-6 tally are about.
5. **n = 256 census was NOT run** (honest budget call): the streamed key volume is
   ~2.1·10^9 pairs ≈ 35 GB gzipped vs 8 GB free disk; a 16-pass sharded recomputation
   would cost ~10 h. The 256 lower bound (≥ 6) is proven; the upper bound at 256 is open
   evidence-wise here.  Cheap follow-ups: run the ladder at n = 128 (24 primes ×
   ~7 min ≈ 3 h to make M(128) ≤ 6 rigorous); a sharded or C-accelerated pass for
   n = 256.
6. Class representatives at n = 16/32 come from ONE split prime each
   (`results_count6_classes.json`); their char-0 validity is no longer an assumption —
   re-proven exactly per class (§2) — but the CLASS COUNTS (34/210) and completeness of
   the orbit decomposition still rest on that single-prime census pass (mitigated by the
   bit-identical two-prime histograms on record and the n=32 gate reproduction here).

## 5. Verdict

- **Task 1**: conjugate-reciprocity for u = (c,d,−a,−b) is exactly ū_k = λ·u_{3−k}
  (c̄ = −λb, d̄ = −λa, ā = −λd, b̄ = −λc), λλ̄ = 1 forced; λ = ±ζ^t holds for primitive
  integral representatives and is EXPLICIT (λ = ζ^{−Σ}) for cross-product normals via
  the new spanning identity rev(v) = ζ^Σ·v̄; the family is half-dimensional (K⁺-dim 4
  of 8, rank-verified), with free pair (u0,u1) and (u2,u3) = λ̄·(ū1,ū0).
- **Task 2**: **maximizers_all_reciprocal = TRUE** — 34/34 (n=16) and 210/210 (n=32)
  count-6 classes verified conjugate-reciprocal in exact arithmetic, each with unique
  λ = ζ^{−Σ}; all 244 classes re-proven count-6 in char 0.
- **Task 3**: M_p(128) = 6 at both split primes with ZERO planes above 6 — the
  constant-6 law extends to n = 128 (two-prime evidence for ≤, exact proof for ≥;
  M(256) ≥ 6 also proven exactly; the 256 census is out of disk budget).  The count-6
  tally obeys the exact law **count-6(n) = (n−4)(11n−76)/4** (41292 at n = 128,
  forward-predicted before the run; five-for-five), count-5 obeys 10(n−6); all
  count-5/6 planes at every n ∈ {8,...,128} carry exact char-0 certificates (0
  failures), so both laws are proven as char-0 lower bounds everywhere measured.  The
  first mod-p surplus of the program appeared at n = 128 — confined to the count-3/4
  buckets, never touching the maximum.
