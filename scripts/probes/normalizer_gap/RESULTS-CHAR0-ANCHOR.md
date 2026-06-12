# Char-0 anchor — exact verification of the census argmax (ArkLib#371)

Continuation of `RESULTS-CHAR0.md` (two-prime census, `results_char0_census.json`).
`probe_char0_anchor.py` re-verifies the census argmax PURELY in characteristic zero:
exact integer arithmetic in Z[x]/Phi_n(x) (Phi_n = x^{n/2}+1 for 2-power n), K-rank
via the regular-representation expansion (Q-span of {z^k P_t} = K-span of {P_t}, so
rank_K = rank_Q(big integer matrix)/m), fraction-free Bareiss with asserted-exact
division. No mod-p reduction is load-bearing anywhere in part (1).

## (1) Exact verification — all checks PASS

| n | S (argmax, canonical) | rank over K | non-norm. | det!=0 in K | char-0 count | census | mod-p match |
|---|----------------------|-------------|-----------|-------------|--------------|--------|-------------|
| 8 | (0,0), (1,1), (2,3), (3,5), (4,6), (6,7) | exactly 3 (big rank 12 = 3·4) | True | True | 6 | 6 | True |
| 16 | (0,0), (1,1), (2,3), (4,10), (7,13), (14,15) | exactly 3 (big rank 24 = 3·8) | True | True | 6 | 6 | True |
| 32 | (0,0), (1,1), (2,3), (4,18), (15,29), (30,31) | exactly 3 (big rank 48 = 3·16) | True | True | 6 | 6 | True |
| 64 | (0,0), (1,1), (2,3), (4,34), (31,61), (62,63) | exactly 3 (big rank 96 = 3·32) | True | True | 6 | 6 | True |

Every n: the 4×6 point matrix has K-rank EXACTLY 3; the cross-product normal is
non-normalizer with ad−bc ≠ 0 over Q(zeta_n); all six incidences vanish IDENTICALLY
in the cyclotomic ring; and the exact char-0 incidence count over the full torus
(Z/n)^2 equals the census count 6 — no hidden seventh point in characteristic zero.
Hence **M(n) ≥ 6 is PROVEN in char 0 for n = 8, 16, 32, 64**, and the witness plane
is exactly the census argmax (its mod-p reduction reproduces the census normal
projectively where the census stored the untranslated representative).
All argmax incidence sets are partial injections i → j and equal the uniform family
S(n) = {(0,0), (1,1), (2,3), (4, n/2+2), (n/2−1, n−3), (n−2, n−1)}.

## (2) Structure of the verified argmax systems

Cross-n laws (verified exactly at every n, not eyeballed):
- **Uniform normal family** (PASS): after removing integer
  content and minimizing over the units ±z^k, the argmax normal is the SAME closed
  form for all n (m = n/2; n = 8 is the collapsed m = 4 case):
    c = −z^{m−1} + z − 2,   d = 2z^{m−1} − z^{m−2} − z^3 + z^2 + z,
    −a = −z^{m−1} + z^{m−2} + z^3 − 2z^2 + 1,   −b = (z − 1)^2,
  with max |coefficient| = 2. One Z[zeta]-normal family realizes S(n) at every n.
- **Difference-class law** (PASS): the multiset of j−i mod n
  is {0, 0, 1, 1, n/2−2, n/2−2} at every n — exactly three difference classes, each
  hit twice; the swapneg pairing (i,j) → (1−j, 1−i) preserves j−i and exchanges the
  members of each pair.
- **Symmetry collapse**: the unique swapneg translation is (1,1) at every n
  (sigma ~ sigma^{-1} invariance, confirming the census claim exactly); plain swap
  and plain negation admit translations ONLY at n = 8 ((3,5) and (4,6) resp.) — the
  full dihedral symmetry of the n = 8 maximizer is lost for n ≥ 16.
- **No coset structure**: the translation stabilizer is trivial at every n, so S(n)
  is not a union of cosets of any nontrivial subgroup of (Z/n)^2 (consistent with
  the points being in 'general position' on the Mobius hyperbola rather than on a
  torsion coset).

### n = 8
- (i+j mod n, j−i mod n) classes: [[0, 0], [0, 2], [2, 0], [2, 2], [5, 1], [5, 1]]
- translation stabilizer is trivial: S is a union of cosets of NO nontrivial subgroup of (Z/n)^2 (only of the trivial subgroup)
- twisted symmetries (translations (s,t) with φ(S)+(s,t)=S): swap [[3, 5]]; negation [[4, 6]]; swap∘negation [[1, 1]]
- normal scaled into Z[zeta_8] (content 1 removed, unit z^1): (c, d, −a, −b) =
    - c = -z^3 + z - 2
    - d = z^3 + z
    - -a = -z^2 + 1
    - -b = z^2 - 2*z + 1
  max |coefficient| = 2

### n = 16
- (i+j mod n, j−i mod n) classes: [[0, 0], [2, 0], [4, 6], [5, 1], [13, 1], [14, 6]]
- translation stabilizer is trivial: S is a union of cosets of NO nontrivial subgroup of (Z/n)^2 (only of the trivial subgroup)
- twisted symmetries (translations (s,t) with φ(S)+(s,t)=S): swap NONE; negation NONE; swap∘negation [[1, 1]]
- normal scaled into Z[zeta_16] (content 1 removed, unit z^5): (c, d, −a, −b) =
    - c = -z^7 + z - 2
    - d = 2*z^7 - z^6 - z^3 + z^2 + z
    - -a = -z^7 + z^6 + z^3 - 2*z^2 + 1
    - -b = z^2 - 2*z + 1
  max |coefficient| = 2

### n = 32
- (i+j mod n, j−i mod n) classes: [[0, 0], [2, 0], [5, 1], [12, 14], [22, 14], [29, 1]]
- translation stabilizer is trivial: S is a union of cosets of NO nontrivial subgroup of (Z/n)^2 (only of the trivial subgroup)
- twisted symmetries (translations (s,t) with φ(S)+(s,t)=S): swap NONE; negation NONE; swap∘negation [[1, 1]]
- normal scaled into Z[zeta_32] (content 1 removed, unit z^13): (c, d, −a, −b) =
    - c = -z^15 + z - 2
    - d = 2*z^15 - z^14 - z^3 + z^2 + z
    - -a = -z^15 + z^14 + z^3 - 2*z^2 + 1
    - -b = z^2 - 2*z + 1
  max |coefficient| = 2

### n = 64
- (i+j mod n, j−i mod n) classes: [[0, 0], [2, 0], [5, 1], [28, 30], [38, 30], [61, 1]]
- translation stabilizer is trivial: S is a union of cosets of NO nontrivial subgroup of (Z/n)^2 (only of the trivial subgroup)
- twisted symmetries (translations (s,t) with φ(S)+(s,t)=S): swap NONE; negation NONE; swap∘negation [[1, 1]]
- normal scaled into Z[zeta_64] (content 1 removed, unit z^29): (c, d, −a, −b) =
    - c = -z^31 + z - 2
    - d = 2*z^31 - z^30 - z^3 + z^2 + z
    - -a = -z^31 + z^30 + z^3 - 2*z^2 + 1
    - -b = z^2 - 2*z + 1
  max |coefficient| = 2

## (3) Law hunt — M(n) against candidate closed forms

Exact data: M(n) = 6 at n = [8, 16, 32, 64] (lower bounds proven in char 0; upper bounds are
the two-prime census values — see caveat).

| model | best fit | predictions at n = 8, 16, 32, 64 | SSE | RMS |
|-------|----------|----------------|-----|-----|
| const c | c = 6 | [6.0, 6.0, 6.0, 6.0] | 0 | 0 |
| c*n^(2/3) | c = 0.528069 | [2.1123, 3.353, 5.3226, 8.4491] | 28.58 | 2.673 |
| a + b*n/log2(n) | a = 6, b = 0 | [6.0, 6.0, 6.0, 6.0] | 0 | 0 |
| 3n/8 (fixed) | - | [3.0, 6.0, 12.0, 24.0] | 369 | 9.605 |
| n/2 - c | c = 9 | [-5.0, -1.0, 7.0, 23.0] | 460 | 10.72 |
| c*n(n-4)^2/8 (chord-law analogue) | c = 0.000230462 | [0.0037, 0.0664, 0.7227, 6.6373] | 99.42 | 4.985 |

M(n) = [6, 6, 6, 6] over n = [8, 16, 32, 64]: flat across a factor-8 range. The data are CONSISTENT WITH the constant law M(n) = 6 (a uniform Beukers-Smyth-type torsion-point cap on the Mobius hyperbola c*xy + d*y - a*x - b = 0; BS-type bounds allow up to ~22, we observe exactly 6). Every growing candidate (c*n^{2/3}, 3n/8, n/2 - c, chord-law c*n(n-4)^2/8) is excluded outright by the flatness; a + b*n/log2(n) fits only by degenerating to b = 0 (the constant). Four data points: 'consistent with', not 'is'.

## Caveats

- The char-0 LOWER bound M(n) ≥ 6 is a theorem (this probe, exact arithmetic).
- The UPPER bound M(n) ≤ 6 inherits the census status: proven-by-height at n = 8, 16
  (Hadamard bounds < 2^56 < p1·p2), two-prime evidence at n = 32, 64 (bit-identical
  histograms at both primes; a larger char-0 system would need p1·p2 | Norm(det)).
  **UPDATE (2026-06-12): the n = 32, 64 upper bounds are now RIGOROUS too** — see
  `RESULTS-CHAR0-RIGOR.md` (exact invisibility bound + prime ladders of length 8 and
  12); M(n) = 6 is a theorem at all four sizes.
- Four data points, all equal: 'consistent with the constant law', not 'is'.
- The mod-p layer (q-decreasing F_q maxima at n = 32) is OUTSIDE this probe's scope;
  this anchors only the char-0 core of the two-layer signature.
