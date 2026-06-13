# Char-0 rigor — exact invisibility bound + prime ladder: M(n) <= 6 (ArkLib#371)

Goal: upgrade the census upper bound **M(n) <= 6** from "two-prime evidence" to
**rigorous** at n = 32 and n = 64 (n = 8, 16 are re-derived in the same framework).
Companion to `RESULTS-CHAR0.md` (census) and `RESULTS-CHAR0-ANCHOR.md` (char-0 lower
bound M(n) >= 6, proven by exact arithmetic).  Produced by `probe_char0_rigor.py`;
machine results in `results_char0_rigor.json`.

Notation: n in {8,16,32,64}, m = n/2, K = Q(zeta), zeta = zeta_n, Phi_n(x) = x^m + 1,
Z[zeta] = Z[x]/(x^m + 1).  Surface points P(i,j) = (zeta^{i+j}, zeta^j, zeta^i, 1),
(i,j) in (Z/n)^2.  A hyperplane normal u = (u0,u1,u2,u3) is read as (c, d, -a, -b);
non-normalizer means (u0,u3) != (0,0) AND (u1,u2) != (0,0); invertible means
det_u := u0*u3 - u1*u2 != 0 (this equals ad - bc).  For a split prime p == 1 (mod n)
fix z_p in F_p* of exact order n; then z_p^m = -1, so
phi_p : Z[zeta] -> F_p, zeta |-> z_p is a well-defined ring homomorphism.  The census
at p enumerates EVERY plane spanned by a rank-3 triple (P00, Q, R) of reduced surface
points (all points distinct mod p — asserted in every run), skips exactly the rank-2 /
normalizer-pattern / singular cases, dedupes by projective normal, and records every
survivor's EXACT full incidence count (multiplicity-1 keys are count-3 by the proven
in-source lemma; every multiplicity >= 2 key was recounted — `recount_capped` is False
in every run used here).

## 1. The hypothetical plane and its cross-product normal

Suppose M(n) >= 7: some hyperplane h (normal u over K — or over C; see 1b) is
non-normalizer, invertible, and contains a set S of c0 >= 7 surface points.

**(1a) WLOG P(0,0) in S.**  The torus translation (i,j) -> (i+s, j+t) permutes the
surface points and acts on normals by u -> (u0 z^{s+t}, u1 z^t, u2 z^s, u3): the
coordinate zero-pattern is preserved (so non-normalizer-ness is), det_u is multiplied
by the unit z^{s+t} (so invertibility is), and every |sigma(.)| is unchanged.

**(1b) rank_K(span S) = 3.**  If rank <= 2, all difference vectors Q - P00
(Q in S\{P00}) are pairwise K-proportional, i.e. all 2x2 minors vanish in Z[zeta];
phi_p preserves this, and the reduced differences are nonzero (points distinct mod p),
so the >= 6 reduced non-P00 points of S land in ONE direction bucket of the census.
Every ladder run verified: the only buckets of size >= 2 are EXACTLY the two
coordinate lines {P(0,j)} and {P(i,0)} (point sets checked, not just sizes).  Since
reduction is a bijection on surface points, S itself lies on a coordinate line in
char 0.  But a hyperplane through >= 2 distinct points of a coordinate line is
singular in char 0:
- line {i=0}: u.P(0,j) = (u0+u1) zeta^j + (u2+u3) = 0 at two distinct j forces
  u0+u1 = 0 and u2+u3 = 0 (zeta^j are distinct), whence
  det_u = u0*u3 - u1*u2 = u0*(-u2) - (-u0)*u2 = 0;
- line {j=0}: u.P(i,0) = (u0+u2) zeta^i + (u1+u3) = 0 forces u0+u2 = 0 = u1+u3,
  whence det_u = u0*(-u1) - u1*(-u0) = 0.
Contradiction with invertibility.  So rank(span S) = 3, and since the C-solution
space of {x.P = 0 : P in S} is then 1-dimensional and defined over K, the normal u
is K-proportional to a K-vector — C-hyperplanes are covered automatically.

**(1c) Cross-product normal and exact heights.**  Pick (greedy basis extension) a
K-rank-3 triple T = (P00, Q, R) inside S and let v in Z[zeta]^4 be its generalized
cross product, v_k := (-1)^k det(3x3 minor of [P00; Q; R] dropping column k).
Then v != 0, v is K-proportional to u (both span the 1-dim annihilator of
span S = h), so v inherits the non-normalizer zero-pattern and det_v := v0*v3 - v1*v2
= lambda^2 * det_u != 0.  Each v_k is a 3x3 determinant whose 9 entries are powers of
zeta (first row (1,1,1)): the Leibniz expansion is a sum of exactly 6 signed monomials
+-zeta^e, and reduction mod zeta^m = -1 sends each to +-zeta^{e mod m}.  Hence
  ||v_k||_1 <= 6   (sum of |coefficients| over the power basis),
and for every complex embedding sigma (sigma(zeta) = a primitive n-th root of unity;
there are m embeddings):
  |sigma(v_k)| <= 3*sqrt(3)   [Hadamard: |det| <= prod of row 2-norms = (sqrt 3)^3
                               for a 3x3 matrix of unit-modulus entries]
  (the L1 route gives the cruder |sigma(v_k)| <= 6), and
  |sigma(det_v)| = |sigma(v0)sigma(v3) - sigma(v1)sigma(v2)| <= 27 + 27 = 54
  (cruder: <= 72).
(The census formula `cross_normal` equals this minor form coordinatewise — proven by
exact symbolic expansion in the script's self-check, not by sampling.)

**(1d) Norms and the three case-integers.**  For x = g(zeta), deg g < m, define
N(x) := det(multiplication-by-g on Z[x]/(x^m+1)) — an ordinary integer, computable
exactly.  Over C this map has eigenvalues g(omega) over the m complex roots omega of
x^m + 1, i.e. the conjugates sigma(x); hence N(x) = prod_sigma sigma(x), so x != 0
implies N(x) != 0, and |N(x)| <= (per-embedding bound)^m.  Attach to h the integers
  D_bc  := |N(v0)| if v0 != 0 else |N(v3)|   (one is nonzero: non-normalizer),
  D_ad  := |N(v1)| if v1 != 0 else |N(v2)|,
  D_det := |N(det_v)|.
All three are FIXED nonzero positive integers (independent of any prime), with
  0 < D_bc, D_ad <= (3*sqrt(3))^m = 3^(3m/2) =: B_coord(n)   [integer: m is even]
  0 < D_det <= 54^m =: B_det(n).

**Divisibility lemma.**  If x in Z[zeta], x != 0 and phi_p(x) = 0, then p | N(x).
Proof: reducing the integer multiplication matrix mod p, N(x) == det(mult-by-g on
A) (mod p) with A := F_p[x]/(x^m+1).  Since 2m = n | p - 1 and F_p* is cyclic,
x^m + 1 has exactly m roots in F_p (the solutions of y^m = -1), all distinct, one of
which is z_p; by CRT A ~ F_p^m and det(mult-by-g) = prod_{y^m=-1} g(y).  The factor
at y = z_p is phi_p(x) = 0, so N(x) == 0 (mod p).  (Elementary — no algebraic
number theory needed.)

## 2. Invisibility trichotomy at a split prime

**Claim.**  Let p == 1 (mod n) be a split prime at which the census reports no plane
of count >= 7 (with: recount uncapped; the bucket fact of (1b); all points distinct).
Then  p | D_bc  or  p | D_ad  or  p | D_det.

Proof.  Case I: phi_p(v) = 0 (all four coordinates).  Then phi_p kills the
char-0-nonzero element among {v0, v3}, so p | D_bc by the lemma.  Case II:
phi_p(v) != 0.  The cross product is a polynomial formula with integer coefficients
in the point entries, so the cross product of the reduced triple T-bar equals
phi_p(v) != 0; hence T-bar is rank 3 over F_p and census pass 1, visiting the pair
{Q-bar, R-bar}, computes exactly +-phi_p(v) (global sign depending on index order —
irrelevant: the skip predicates and the projective dedupe key are sign-invariant).
All c0 >= 7 reduced points of S satisfy phi_p(v).P-bar = 0 (reduce the char-0
incidences) and are distinct, so the plane's true mod-p incidence count is >= 7.
Its dedupe key has triple-multiplicity >= 2: its >= 6 non-P00 points fall into >= 2
direction buckets (Q-bar, R-bar are non-parallel), giving >= 5 cross-bucket pairs,
each a rank-3 triple of the SAME plane (same projective normal, same key).  So the
key is recounted EXACTLY (recount uncapped) and a histogram entry >= 7 appears —
contradicting the observed maximum 6 — unless pass 1 SKIPPED the triple:
  - normalizer-pattern skip: phi_p(v0) = phi_p(v3) = 0  ==>  p | D_bc (lemma applied
    to the char-0-nonzero one), or phi_p(v1) = phi_p(v2) = 0  ==>  p | D_ad;
  - singular skip: phi_p(det_v) = 0 with det_v != 0  ==>  p | D_det.
No other skip exists (rank-2 is impossible here: the cross product is nonzero).  QED.

## 3. Capacity pigeonhole — the exact ladder length k(n)

If a positive integer D <= B is divisible by t DISTINCT primes each > 2^28, then
D >= (their product) > 2^(28 t), so 2^(28 t) < B.  Define (exact integer comparisons)
  cap(B) := max { t >= 0 : 2^(28 t) < B }.
Suppose ONE hypothetical plane h is invisible at k distinct split primes p_1..p_k
(all > 2^28, all == 1 mod n, each with a clean census: max = 6 + side conditions).
By the trichotomy each p_i divides one of h's three fixed integers; assigning each
prime to one target gives t_bc + t_ad + t_det = k with t_bc, t_ad <= cap(B_coord),
t_det <= cap(B_det).  Hence k <= 2 cap(B_coord) + cap(B_det).  Running
  k(n) := 2 cap(B_coord(n)) + cap(B_det(n)) + 1
clean primes is therefore a contradiction — no such h exists, and **M(n) <= 6**.
Combined with the exact char-0 lower bound (RESULTS-CHAR0-ANCHOR.md): **M(n) = 6**.

Quantifier order (the subtle point): the three case-integers are attached to the
single hypothetical plane h, fixed BEFORE any prime is chosen; the pigeonhole is per
plane, so the conclusion is the nonexistence of every individual h — no union bound
over planes is needed.


## 4. Exact bounds, capacities, ladder lengths

All values exact integers; 'bits' = bit length.  cap() per Section 3; primes counted are > 2^28.

| n | m | B_coord = 3^(3m/2) | bits | B_det = 54^m | bits | cap_c | cap_d | k(n) Hadamard | k(n) L1 (6^m / 72^m) | k run |
|---|---|--------------------|------|--------------|------|-------|-------|---------------|----------------------|-------|
| 8 | 4 | 729 | 10 | 8503056 | 24 | 0 | 0 | 1 | 1 | 2 |
| 16 | 8 | 531441 | 20 | 72301961339136 | 47 | 0 | 1 | 2 | 2 | 2 |
| 32 | 16 | 282429536481 | 39 | 5227573613485916806405226496 | 93 | 1 | 3 | 6 | 6 | 8 |
| 64 | 32 | 79766443076872509863361 | 77 | 27327525884414205519790497974303154461449992065060438016 | 185 | 2 | 6 | 11 | 12 | 12 |

The L1-only variant (no Hadamard, |sigma(v_k)| <= 6, |sigma(det_v)| <= 72) is shown to make the result robust to the choice of height route; the runs below satisfy BOTH ladder lengths at every n.

## 5. Ladder runs

### n = 8
- primes (2 run / 1 needed Hadamard / 1 needed L1): 268435537, 268435561
- histogram (IDENTICAL at every prime): {3:336, 4:88, 5:20, 6:12}; max = 6
  - primes_distinct: True
  - primes_split_gt_2pow28: True
  - max_is_6_everywhere: True
  - histograms_bit_identical: True
  - recount_uncapped_everywhere: True
  - flats_are_coordinate_lines_invalid: True
  - top1_canon_identical: True
  - M_p_equals_6_everywhere: True
- verdict: rigorous (Hadamard ladder) = True; rigorous (L1 ladder) = True

### n = 16
- primes (2 run / 2 needed Hadamard / 2 needed L1): 268435537, 268435649
- histogram (IDENTICAL at every prime): {3:11448, 4:2264, 5:100, 6:300}; max = 6
  - primes_distinct: True
  - primes_split_gt_2pow28: True
  - max_is_6_everywhere: True
  - histograms_bit_identical: True
  - recount_uncapped_everywhere: True
  - flats_are_coordinate_lines_invalid: True
  - top1_canon_identical: True
  - M_p_equals_6_everywhere: True
- verdict: rigorous (Hadamard ladder) = True; rigorous (L1 ladder) = True

### n = 32
- primes (8 run / 6 needed Hadamard / 6 needed L1): 268435649, 268435873, 268436801, 268437409, 268437569, 268437857, 268437889, 268438081
- histogram (IDENTICAL at every prime): {3:326472, 4:28056, 5:260, 6:1932}; max = 6
  - primes_distinct: True
  - primes_split_gt_2pow28: True
  - max_is_6_everywhere: True
  - histograms_bit_identical: True
  - recount_uncapped_everywhere: True
  - flats_are_coordinate_lines_invalid: True
  - top1_canon_identical: True
  - M_p_equals_6_everywhere: True
- verdict: rigorous (Hadamard ladder) = True; rigorous (L1 ladder) = True

### n = 64
- primes (12 run / 11 needed Hadamard / 12 needed L1): 268435649, 268436801, 268437569, 268437889, 268438081, 268438337, 268438657, 268438913, 268439681, 268440449, 268440577, 268440833
- histogram (IDENTICAL at every prime): {3:6778728, 4:249368, 5:580, 6:9420}; max = 6
  - primes_distinct: True
  - primes_split_gt_2pow28: True
  - max_is_6_everywhere: True
  - histograms_bit_identical: True
  - recount_uncapped_everywhere: True
  - flats_are_coordinate_lines_invalid: True
  - top1_canon_identical: True
  - M_p_equals_6_everywhere: True
- verdict: rigorous (Hadamard ladder) = True; rigorous (L1 ladder) = True

### per-prime run table

| n | p | z | M_p | hist == ladder hist | capped | flats | wall (s) |
|---|---|---|-----|---------------------|--------|-------|----------|
| 32 | 268435649 | 23172711 | 6 | True | False | 2xL=32 invalid | 4.6 |
| 32 | 268435873 | 157076058 | 6 | True | False | 2xL=32 invalid | 4.54 |
| 32 | 268436801 | 138746359 | 6 | True | False | 2xL=32 invalid | 4.54 |
| 32 | 268437409 | 58749795 | 6 | True | False | 2xL=32 invalid | 5.46 |
| 32 | 268437569 | 244693005 | 6 | True | False | 2xL=32 invalid | 4.92 |
| 32 | 268437857 | 137449957 | 6 | True | False | 2xL=32 invalid | 5.53 |
| 32 | 268437889 | 99093966 | 6 | True | False | 2xL=32 invalid | 4.24 |
| 32 | 268438081 | 136632571 | 6 | True | False | 2xL=32 invalid | 4.31 |
| 64 | 268435649 | 213385133 | 6 | True | False | 2xL=64 invalid | 273.31 |
| 64 | 268436801 | 71287583 | 6 | True | False | 2xL=64 invalid | 214.49 |
| 64 | 268437569 | 76738881 | 6 | True | False | 2xL=64 invalid | 215.68 |
| 64 | 268437889 | 227464787 | 6 | True | False | 2xL=64 invalid | 229.6 |
| 64 | 268438081 | 263982620 | 6 | True | False | 2xL=64 invalid | 305.86 |
| 64 | 268438337 | 119902728 | 6 | True | False | 2xL=64 invalid | 235.33 |
| 64 | 268438657 | 98791136 | 6 | True | False | 2xL=64 invalid | 211.34 |
| 64 | 268438913 | 247669418 | 6 | True | False | 2xL=64 invalid | 263.17 |
| 64 | 268439681 | 179837695 | 6 | True | False | 2xL=64 invalid | 212.88 |
| 64 | 268440449 | 84219064 | 6 | True | False | 2xL=64 invalid | 278.5 |
| 64 | 268440577 | 57956187 | 6 | True | False | 2xL=64 invalid | 234.56 |
| 64 | 268440833 | 29433285 | 6 | True | False | 2xL=64 invalid | 271.78 |

## 6. Verdict

- **M(8) <= 6 is RIGOROUS** (k_run = 2, k_needed = 1 Hadamard / 1 L1); with the proven lower bound, M(8) = 6.
- **M(16) <= 6 is RIGOROUS** (k_run = 2, k_needed = 2 Hadamard / 2 L1); with the proven lower bound, M(16) = 6.
- **M(32) <= 6 is RIGOROUS** (k_run = 8, k_needed = 6 Hadamard / 6 L1); with the proven lower bound, M(32) = 6.
- **M(64) <= 6 is RIGOROUS** (k_run = 12, k_needed = 11 Hadamard / 12 L1); with the proven lower bound, M(64) = 6.

**Overall: the upper bound M(n) <= 6 is now RIGOROUS at every n in {8, 16, 32, 64}**, hence M(n) = 6 at all four sizes (lower bound: RESULTS-CHAR0-ANCHOR.md).

## 7. Caveats / scope

- The statement is exactly about M(n) as defined (non-normalizer, invertible
  hyperplanes against P(i,j) over (Z/n)^2) for n in {8, 16, 32, 64}; nothing is
  claimed for other n.
- Load-bearing inputs: (a) the derivation above (every inequality exact; the
  Hadamard step |det| <= (sqrt 3)^3 is classical and used only through the integer
  bounds 3^(3m/2) and 54^m); (b) per-prime census outputs: no histogram key >= 7,
  recount uncapped, the two-coordinate-line bucket fact, point distinctness
  (asserted in-run); (c) the in-source multiplicity lemma (mult 1 <=> count 3).
  The bit-identical histograms ACROSS primes are extra evidence, not load-bearing.
- The original prompt's "content divides" shortcut for the phi_p(v) = 0 mode is NOT
  valid (vanishing under one embedding-reduction does not force p | content); it is
  replaced here by the norm/divisibility lemma, which also subsumes that mode into
  the normalizer-collapse case integer D_bc.
- The mod-p surplus layer (census counts can only exceed char-0 counts) is exactly
  why the per-prime maxima are upper bounds for M(n); no surplus was observed at any
  ladder prime (all histograms bit-identical).
- Self-checks run before the ladder: symbolic identity census-formula == minor form
  (exact multivariate expansion); height + norm bounds on random surface triples
  (exact Bareiss norms); reduction-commutation spot check; the census's own
  cross-product-vs-nullspace self-test.
