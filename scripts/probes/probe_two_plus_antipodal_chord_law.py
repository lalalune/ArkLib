#!/usr/bin/env python3
"""Falsifier for the two-plus-antipodal chord law (#357 slanted-family closed form).

Claim (TwoPlusAntipodalChordLaw.lean): for pair-points of Gamma_n (n = 2^m) of shapes
{i, i+d}, {j, j+d} (same non-antipodal difference class d, distinct: z^i != z^j) and
{k, k+n/2} (antipodal), the collinearity determinant factors as

    det = (z^j - z^i) * (1 + z^d) * (z^(i+j+d) - z^(2k))

so the triple is collinear  IFF  2k === i + j + d (mod n)  — uniformly (the horizontal
degenerations j === i + n/2 are included on both sides; slanted-ness is downstream
classification, not part of the law).

Verified here over exact cyclotomic integers (the 12-term fold) at n = 8, 16, 32:
every (i, j, k, d) with d non-antipodal and i !== j (mod n) satisfies
fold12-vanishing == congruence; plus the factorization identity itself is checked
symbolically mod p at several primes (exact arithmetic).
"""
from itertools import combinations

def fold12(n, P1, P2, P3):
    h = n // 2
    (a1,b1),(a2,b2),(a3,b3) = P1,P2,P3
    terms = [(a2+a3+b3,1),(b2+a3+b3,1),(a2+a1+b1,-1),(b2+a1+b1,-1),
             (a1+a3+b3,-1),(b1+a3+b3,-1),(a3+a2+b2,-1),(b3+a2+b2,-1),
             (a1+a2+b2,1),(b1+a2+b2,1),(a3+a1+b1,1),(b3+a1+b1,1)]
    coeff = [0]*h
    for ex,w in terms:
        r = ex % n
        if r < h: coeff[r] += w
        else: coeff[r-h] -= w
    return not any(coeff)

for n in (8, 16, 32):
    h = n // 2
    checked = 0
    for d in range(1, n):
        if d % n == h:
            continue
        for i in range(n):
            for j in range(n):
                if i % n == j % n:
                    continue
                for k in range(n):
                    P1 = tuple(sorted((i % n, (i + d) % n)))
                    P2 = tuple(sorted((j % n, (j + d) % n)))
                    P3 = tuple(sorted((k % n, (k + h) % n)))
                    # the law is about the det of the three (e,m) data, which only
                    # depends on (i,j,k,d); degenerate index overlaps are fine for the
                    # algebraic law (the det is still the det of the three value-pairs)
                    truth = fold12(n, (i, (i+d) % n), (j, (j+d) % n), (k, (k+h) % n))
                    law = (2 * k) % n == (i + j + d) % n
                    assert truth == law, (n, d, i, j, k, truth, law)
                    checked += 1
    print(f"n={n}: chord law PASS on {checked} (i,j,k,d) tuples")

# factorization identity check mod several primes (exact)
def check_factorization(n, p):
    g = None
    if (p - 1) % n != 0:
        return False
    for cand in range(2, p):
        if pow(cand, n, p) == 1 and pow(cand, n // 2, p) != 1:
            g = cand; break
    h = n // 2
    for d in range(1, n):
        for i in range(n):
            for j in range(n):
                for k in range(0, n, 3):   # sampled k
                    a, b = pow(g, i, p), pow(g, j, p)
                    e1 = (a + a * pow(g, d, p)) % p
                    e2 = (b + b * pow(g, d, p)) % p
                    m1 = (a * a % p) * pow(g, d, p) % p
                    m2 = (b * b % p) * pow(g, d, p) % p
                    kk = pow(g, k, p)
                    e3 = (kk + kk * pow(g, h, p)) % p
                    m3 = kk * kk % p * pow(g, h, p) % p
                    det = ((e2 - e1) * (m3 - m1) - (m2 - m1) * (e3 - e1)) % p
                    fac = ((b - a) % p) * ((1 + pow(g, d, p)) % p) % p \
                          * ((pow(g, (i + j + d) % n, p) - pow(g, (2 * k) % n, p)) % p) % p
                    assert det == fac % p, (n, p, d, i, j, k, det, fac)
    return True

for (n, p) in ((8, 41), (8, 97), (16, 97)):
    assert check_factorization(n, p)
    print(f"n={n}, p={p}: determinant factorization identity PASS (exact mod p)")
print("ALL PASS")
