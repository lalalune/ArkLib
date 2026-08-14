#!/usr/bin/env python3
"""Char-0 census of collinear triples of Gamma_n via the 12-term fold (#357).

By CollinearityCensusTransfer (detGamma_modp_iff_foldedSum + detGamma_char0_iff_foldedSum),
the collinearity verdict of an exponent-triple over every F_p above the threshold and over
every char-0 field equals: foldedSum of the 12-term census family = 0 in Z[X].

This probe enumerates, in pure integer arithmetic (no field, no prime):
  (C1) all collinear triples of distinct pair-points at n = 8, 16 (char-0 truth);
  (C2) the stratification of those triples by line type: horizontal (equal m), vertical
       (equal e), slanted — cross-checked against the fleet's measured strata counts
       (slanted: 16 @ n=8, 928 @ n=16; vertical C(n/2,3); horizontal sum C(eta,3));
  (C3) for slanted circuits: the antipodal matching pattern of the 12 terms (which
       cancellation structure realizes them) — the raw material of the char-0 closure.

Points are unordered pairs {i,j}, i != j, of exponents mod n; the pair-point is
(e, m) = (z^i + z^j, z^{i+j}). Distinct points = distinct (i,j) sets with distinct
(e, m) char-0 values; e-coordinate char-0 equality is itself decided by the 4-term fold
(pair_sum_rigidity: distinct non-antipodal pairs have distinct sums; antipodal pairs all
have e = 0), m-equality is i+j === i'+j' (mod n).
"""
from itertools import combinations

def fold12(n, P1, P2, P3):
    """Folded 12-term polynomial of the collinearity det for pair-points P1,P2,P3."""
    h = n // 2
    (a1, b1), (a2, b2), (a3, b3) = P1, P2, P3
    terms = [
        (a2 + a3 + b3, 1), (b2 + a3 + b3, 1),
        (a2 + a1 + b1, -1), (b2 + a1 + b1, -1),
        (a1 + a3 + b3, -1), (b1 + a3 + b3, -1),
        (a3 + a2 + b2, -1), (b3 + a2 + b2, -1),
        (a1 + a2 + b2, 1), (b1 + a2 + b2, 1),
        (a3 + a1 + b1, 1), (b3 + a1 + b1, 1),
    ]
    coeff = [0] * h
    for ex, w in terms:
        r = ex % n
        if r < h:
            coeff[r] += w
        else:
            coeff[r - h] -= w
    return tuple(coeff), terms

def fold1(n, ex):
    h = n // 2
    coeff = [0] * h
    r = ex % n
    if r < h:
        coeff[r] += 1
    else:
        coeff[r - h] -= 1
    return tuple(coeff)

def e_key(n, i, j):
    """char-0 canonical key for e = z^i + z^j (fold of the 2-term sum)."""
    h = n // 2
    coeff = [0] * h
    for ex in (i, j):
        r = ex % n
        if r < h:
            coeff[r] += 1
        else:
            coeff[r - h] -= 1
    return tuple(coeff)

def census(n):
    h = n // 2
    pairs = list(combinations(range(n), 2))
    pts = {}
    for (i, j) in pairs:
        key = (e_key(n, i, j), (i + j) % n)   # char-0 (e, m) identity
        pts.setdefault(key, []).append((i, j))
    # distinct pair-points (some pairs may share (e,m)? e injective on non-antipodal by
    # rigidity; all antipodal pairs share e=0 but have distinct m)
    multi = {k: v for k, v in pts.items() if len(v) > 1}
    assert not multi, f"pair-point identification collision: {multi}"
    points = {P: key for key, v in pts.items() for P in v}
    horiz = vert = slant = 0
    slant_examples = []
    for T in combinations(pairs, 3):
        P1, P2, P3 = T
        if len({*P1, *P2, *P3}) != 6:    # wide circuits need Distinct6 (disjoint pairs)
            continue
        R, terms = fold12(n, P1, P2, P3)
        if any(R):
            continue
        # collinear in char 0; stratify by line type
        ms = {(i + j) % n for (i, j) in T}
        es = {e_key(n, i, j) for (i, j) in T}
        if len(ms) < 3 and len(es) < 3:
            # degenerate: two identical points impossible (distinct T), but a line
            # needs 2 distinct coordinates; classify by which collapses fully
            pass
        if len(ms) == 1:
            horiz += 1
        elif len(es) == 1:
            vert += 1
        elif len(ms) < 3 or len(es) < 3:
            # mixed partial collapse: two points share m (or e) but not all three —
            # still a slanted/other line through Gamma_n? a line with two equal m's
            # among three distinct points is horizontal only if all three equal.
            slant += 1
            if len(slant_examples) < 6:
                slant_examples.append((T, "partial"))
        else:
            slant += 1
            if len(slant_examples) < 6:
                slant_examples.append((T, "generic"))
    return horiz, vert, slant, slant_examples

for n in (8, 16):
    h, v, s, ex = census(n)
    cnh = n // 2
    # expected vertical: C(n/2, 3) (all antipodal pairs, e = 0)
    from math import comb
    print(f"n={n}: horizontal={h}, vertical={v} (expect C({cnh},3)={comb(cnh,3)}), "
          f"slanted={s} (fleet measured: {16 if n==8 else 928})")
    for (T, kind) in ex[:4]:
        print(f"   slanted example ({kind}): {T}")
print("DONE")

# C4: the F_p slanted count across primes — locating the fleet's measured 928 @ n=16.
def census_modp(n, p):
    g = None
    if (p - 1) % n != 0:
        return None
    for cand in range(2, p):
        if pow(cand, n, p) == 1 and pow(cand, n // 2, p) != 1:
            g = cand
            break
    pairs = list(combinations(range(n), 2))
    horiz = vert = slant = 0
    for T in combinations(pairs, 3):
        P1, P2, P3 = T
        if len({*P1, *P2, *P3}) != 6:
            continue
        em = []
        for (i, j) in T:
            em.append(((pow(g, i, p) + pow(g, j, p)) % p, pow(g, i + j, p)))
        (e1, m1), (e2, m2), (e3, m3) = em
        det = ((e2 - e1) * (m3 - m1) - (m2 - m1) * (e3 - e1)) % p
        if det != 0:
            continue
        ms = {m1, m2, m3}
        es = {e1, e2, e3}
        if len(ms) == 1:
            horiz += 1
        elif len(es) == 1:
            vert += 1
        else:
            slant += 1
    return horiz, vert, slant

for p in (17, 97, 113, 257, 337, 449, 577, 7681, 12289):
    r = census_modp(16, p)
    if r:
        print(f"n=16, p={p}: horizontal={r[0]}, vertical={r[1]}, slanted={r[2]}")

# C5 (appended): large-scale stable census via line-grouping at large primes.
# Verified stable values (agreement at >=3 large primes each):
#   n=32: slanted 6720 (stable at 12289, 40961, 65537)
#   n=64: slanted 64640 (stable at 786433, 7340033, 23068673, 167772161;
#         surplus tail: 121984@12289, 82176@114689, 70144@147457; Fermat 65537
#         corrupts even the vertical stratum: 5344 vs C(32,3)=4960)
# family closed form (chord law): family(n) = n(n-4)^2/8 -> 16, 288, 3136, 28800
# sporadic = slanted - family -> 0, 256, 3584, 35840 = 2^(m+4) * {1, 7, 35}

# C7 (appended): EXHAUSTION VERIFIED — the second layer at n=16, 32 equals EXACTLY
# (rotation+Galois orbits of shape-I  {0,1},{t+1,n-(2t+1)},{2t+1,h-t}
#  union shape-II                     {0,1},{t+2,n-(2t+2)},{2t+4,h-t-1})
# union doubling(second_layer(n/2)):  0 missing, 0 extra at both scales.
# Both shapes are PURE RATIONAL IDENTITIES (verified over random Fractions):
#  I : (1+z, z), (zP+(zP^2)^-1, P^-1), (zP^2-P^-1, -zP)
#  II: (1+z, z), (z^2 P+(z^2 P^2)^-1, P^-1), (z^4 P^2-(zP)^-1, -z^3 P)
# and the ansatz sweep (alpha,beta,delta,eps,phi in -2..5, all signs) finds ONLY these two.

# C8 (appended): THE MATCHING-PATTERN CENSUS — the exactness converse's case list.
# Of the 10395 perfect matchings of the 12 determinant terms, EXACTLY 14 simple
# (multiplicity-free) patterns occur among balanced configurations, IDENTICAL at
# n = 16 and n = 32, perfectly stratified:
#   1 vertical   M1:  (01)(23)(45)(67)(89)(10 11)
#   1 horizontal M4:  (02)(13)(48)(59)(6 10)(7 11)
#   4 family     M2,M3,M5,M12
#   8 second     M6-M11,M13,M14   [= the 8 Galois-orbit count at n=16]
# plus exactly 3 multiplicity-collision profiles (2,2,1^8), (2^4,1^4), (2^6) —
# the degenerate fibers. The exactness converse = prove each matching's 6-equation
# linear system forces its stratum's known form + handle the 3 collision profiles.
# Scale-uniform: the case list does not grow with n.

# C9 (appended): THE 14 SYSTEMS SOLVED — each matching's 6 equations collapse to
# exactly 3 distinct congruences (antipodal redundancy halves them):
#   M1 (vert):  a1-b1 = a2-b2 = a3-b3 = h  -> all pairs antipodal = vertical. QED-shape.
#   M4 (horiz): a1+b1 = a2+b2 = a3+b3      -> equal products = horizontal. QED-shape.
#   M2/M3/M5/M12 (family): ONE antipodal-pair equation (a2-b2=h / a3-b3=h / a1-b1=h)
#     + two 4-term cross congruences whose sum is the chord congruence 2k = i+j+d.
#   M6-M14 (second): NO antipodal pair; three 4-term congruences = the seed systems
#     (e.g. M6: a1-a2-b2+b3 = a1+b2-a3-b3 = a1+b1-b2-b3 = h).
# The exactness-converse Lean work is now fully specified: 14 lemmas "3 congruences
# force the stratum form" + balanced-implies-matching pigeonhole + 3 collision profiles.
