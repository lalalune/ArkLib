# Char-0 incidence census — M(n) for the normalizer-gap lane (ArkLib#371)

M(n) = max over non-normalizer (b=c=0 / a=d=0 excluded), invertible (ad != bc)
hyperplanes h of #{(i,j) in (Z/n)^2 : (z^{i+j}, z^j, z^i, 1) on h}, computed by
reduction mod two split primes p == 1 (mod n), p > 2^28 (smallest such), with the
torus-action quotient (first triple point fixed to P(0,0)).  M_p(n) >= M(n);
agreement of the two primes (and of the canonical argmax (i,j)-sets) is the
char-0 signal.

| n | p1 | p2 | M_p1 | M_p2 | agree | M(n) cand | top-1 sets match | deg-flat max (valid) |
|---|----|----|------|------|-------|-----------|------------------|----------------------|
| 8 | 268435537 | 268435561 | 6 | 6 | True | 6 | True | None / None |
| 16 | 268435537 | 268435649 | 6 | 6 | True | 6 | True | None / None |
| 32 | 268435649 | 268435873 | 6 | 6 | True | 6 | True | None / None |
| 64 | 268435649 | 268436801 | 6 | 6 | True | 6 | True | None / None |

## n = 8
- p = 268435537 (z = 39845900): histogram over deduped non-normalizer planes through P(0,0): {3:336, 4:88, 5:20, 6:12}; rank-2 triples 42; normalizer-type skipped 42, singular skipped 1029; pass1 0.0s, recount 0.0s.
  - degenerate flats (rank-2 point sets through P00): L=8 valid=False; L=8 valid=False
  - argmax: count 6, canonical (i,j)-set [[0, 0], [1, 1], [2, 3], [3, 5], [4, 6], [6, 7]]
- p = 268435561 (z = 60851162): histogram over deduped non-normalizer planes through P(0,0): {3:336, 4:88, 5:20, 6:12}; rank-2 triples 42; normalizer-type skipped 42, singular skipped 1029; pass1 0.0s, recount 0.0s.
  - degenerate flats (rank-2 point sets through P00): L=8 valid=False; L=8 valid=False
  - argmax: count 6, canonical (i,j)-set [[0, 0], [1, 1], [2, 3], [3, 5], [4, 6], [6, 7]]

## n = 16
- p = 268435537 (z = 85424310): histogram over deduped non-normalizer planes through P(0,0): {3:11448, 4:2264, 5:100, 6:300}; rank-2 triples 210; normalizer-type skipped 210, singular skipped 10125; pass1 0.07s, recount 0.15s.
  - degenerate flats (rank-2 point sets through P00): L=16 valid=False; L=16 valid=False
  - argmax: count 6, canonical (i,j)-set [[0, 0], [1, 1], [2, 3], [4, 10], [7, 13], [14, 15]]
- p = 268435649 (z = 157800305): histogram over deduped non-normalizer planes through P(0,0): {3:11448, 4:2264, 5:100, 6:300}; rank-2 triples 210; normalizer-type skipped 210, singular skipped 10125; pass1 0.07s, recount 0.15s.
  - degenerate flats (rank-2 point sets through P00): L=16 valid=False; L=16 valid=False
  - argmax: count 6, canonical (i,j)-set [[0, 0], [1, 1], [2, 3], [4, 10], [7, 13], [14, 15]]

## n = 32
- p = 268435649 (z = 23172711): histogram over deduped non-normalizer planes through P(0,0): {3:326472, 4:28056, 5:260, 6:1932}; rank-2 triples 930; normalizer-type skipped 930, singular skipped 89373; pass1 1.5s, recount 6.66s.
  - degenerate flats (rank-2 point sets through P00): L=32 valid=False; L=32 valid=False
  - argmax: count 6, canonical (i,j)-set [[0, 0], [1, 1], [2, 3], [4, 18], [15, 29], [30, 31]]
- p = 268435873 (z = 157076058): histogram over deduped non-normalizer planes through P(0,0): {3:326472, 4:28056, 5:260, 6:1932}; rank-2 triples 930; normalizer-type skipped 930, singular skipped 89373; pass1 1.46s, recount 6.43s.
  - degenerate flats (rank-2 point sets through P00): L=32 valid=False; L=32 valid=False
  - argmax: count 6, canonical (i,j)-set [[0, 0], [1, 1], [2, 3], [4, 18], [15, 29], [30, 31]]

## n = 64
- p = 268435649 (z = 213385133): histogram over deduped non-normalizer planes through P(0,0): {3:6778728, 4:249368, 5:580, 6:9420}; rank-2 triples 3906; normalizer-type skipped 3906, singular skipped 750141; pass1 26.91s, recount 227.39s.
  - degenerate flats (rank-2 point sets through P00): L=64 valid=False; L=64 valid=False
  - argmax: count 6, canonical (i,j)-set [[0, 0], [1, 1], [2, 3], [4, 34], [31, 61], [62, 63]]
- p = 268436801 (z = 71287583): histogram over deduped non-normalizer planes through P(0,0): {3:6778728, 4:249368, 5:580, 6:9420}; rank-2 triples 3906; normalizer-type skipped 3906, singular skipped 750141; pass1 27.17s, recount 222.36s.
  - degenerate flats (rank-2 point sets through P00): L=64 valid=False; L=64 valid=False
  - argmax: count 6, canonical (i,j)-set [[0, 0], [1, 1], [2, 3], [4, 34], [31, 61], [62, 63]]

## Findings (addendum)

1. **M(n) = 6 for n = 8, 16, 32, 64.** Both split primes agree at every n; moreover the FULL
   incidence histograms are bit-identical across the two primes at every n — no mod-p surplus
   is visible at p ~ 2^28 (as expected: surplus requires p to divide fixed nonzero cyclotomic
   resultants). The char-0 core of the two-layer signature is **flat in n**: the q-decreasing
   F_q maxima at n=32 (18@97, 14@193, 12@257) sit entirely in the mod-p surplus layer above a
   core of 6, which matches the field-independent value 6 already seen at n=8.
2. **Uniform argmax family.** The lexicographic top-1 canonical incidence set at every n is the
   single n-parametrized family
   `S(n) = {(0,0), (1,1), (2,3), (4, n/2+2), (n/2-1, n-3), (n-2, n-1)}`
   (n=8: also fully dihedral-symmetric; all argmaxes are sigma ~ sigma^{-1} symmetric modulo
   the torus action, i.e. invariant under (i,j) -> (-j,-i) up to translation). Count-6 plane
   totals grow with n (12, 300, 1932, 9420 through P(0,0)) but the cap stays 6 — consistent
   with a uniform torsion-point bound (Beukers–Smyth-type "cyclotomic points on curves") for
   the Mobius hyperbola c·xy + d·y − a·x − b = 0.
3. **Degenerate flats are exactly the two coordinate lines** {i=0} and {j=0} (L=n each;
   rank-2 triple count = (n-1)(n-2) = 2·C(n-1,2), matching the bucket prediction). Their
   hyperplane pencils are **identically singular** (e.g. the {i=0} pencil forces
   ad − bc = 0), so they never contribute a non-normalizer invertible incidence count —
   verified exactly, not by sampling.
4. **Verification.** (a) generalized-cross-product nullspace checked against fraction-free
   Gaussian elimination on 500 random triples; (b) the multiplicity shortcut
   (triple-multiplicity 1 <=> incidence count 3) proved in-source and verified by full
   brute-force recount of every deduped plane at n=8 and n=16 (0 violations, histograms
   reproduced exactly); (c) n=8 calibration M >= 6 passed with equality; (d) every argmax
   incidence set is a partial injection i -> j with count <= n (asserted).
5. **Symbolic char-0 witness (`char0_witness_check.py`).** For every n in {8,16,32,64} the
   family S(n) is realized over Z[x]/Phi_n(x) by the exact cross-product hyperplane of
   (P(0,0), P(1,1), P(2,3)): all six incidences vanish identically in the cyclotomic ring,
   the normal is non-normalizer with det != 0 over Q(zeta_n), and its exact char-0 incidence
   count over all of (Z/n)^2 is 6. Hence **M(n) >= 6 is proven** (no mod-p reduction); the
   census upper bound M(n) <= 6 rests on two-prime agreement (see caveat below).

### Caveat on the upper bound

Reduction mod a split prime preserves incidences, so M_p(n) >= M(n) holds for every char-0
system whose reduction stays admissible (det and the normalizer zero-pattern survive). A
hypothetical char-0 system with > 6 incidences could evade ONE prime only if p divides the
norm of its (small-height, cross-product-normalized) determinant; evading BOTH primes needs
p1*p2 | Norm(det). At n=8,16 the Hadamard height bounds rule this out outright (norms < 2^56);
at n=32,64 the bound (up to ~2^224) does not formally exclude it, so there the value 6 is
two-prime evidence (plus bit-identical histograms) rather than a proof. Surplus, if any, can
only push the true M(n) BELOW the per-prime maxima; both primes already agree at 6, and the
proven lower bound pins M(n) = 6 unless both primes simultaneously miss the same larger system.

**UPDATE (2026-06-12): this caveat is RESOLVED.** `RESULTS-CHAR0-RIGOR.md`
(`probe_char0_rigor.py`) derives the exact invisibility bound (norm case-integers
D_bc, D_ad <= 3^(3m/2), D_det <= 54^m + capacity pigeonhole) and runs clean prime
ladders of length k(32) = 8 >= 6 and k(64) = 12 >= 12 needed — the upper bound
M(n) <= 6 is now RIGOROUS at all n in {8, 16, 32, 64}, hence M(n) = 6.

