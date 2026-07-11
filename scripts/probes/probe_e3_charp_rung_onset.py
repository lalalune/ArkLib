# Probe: does E_3(mu_n) in char-p EXCEED the char-0 census 15n^3-45n^2+40n
# (and the ERM r=3 ceiling 15n^3)? If yes -> r=3 is the first ERM rung that FAILS
# on mu_n in char-p = the BGK/Lam-Leung wall onset at depth 3.
#
# E_r(G) = #{(x_1..x_r,y_1..y_r) in G^{2r} : sum x = sum y}  (additive energy, depth r).
# E_3 = #{6-tuples (a,b,c,d,e,f) in G^6 : a+b+c = d+e+f}  (a+b+c-d-e-f = 0 mod p).
# mu_n = n-th roots of unity in F_p (n=2^a | p-1).
#
# r=2 is PROVEN-equal to the char-0 census (3n^2-3n) and <= 3n^2 (in-tree
# GaussianEnergyBoundMuNDepthTwo). This probe checks whether r=3 already exceeds
# 15n^3 (the (2*3-1)!!=15 ERM ceiling) at structured/prize primes.

import itertools
import math
from collections import Counter


def order(cand, p):
    o = 1
    x = cand % p
    while x != 1:
        x = (x * cand) % p
        o += 1
        if o > p:
            return -1
    return o


def roots_of_unity(p, n):
    for cand in range(2, p):
        if order(cand, p) == n:
            return sorted({pow(cand, k, p) for k in range(n)})
    return None


def E3_charp(G, p):
    cnt = Counter()
    for a in G:
        for b in G:
            ab = (a + b) % p
            for c in G:
                cnt[(ab + c) % p] += 1
    return sum(v * v for v in cnt.values())


def census_charzero(n):
    return 15 * n ** 3 - 45 * n ** 2 + 40 * n


def main():
    print("%8s %4s %6s %12s %12s %12s %10s %11s" % (
        "p", "n", "beta", "E3_charp", "15n^3", "census_c0", "E3>15n^3", "E3>census"))
    cases = [
        (97, 4), (193, 4), (257, 4), (769, 4), (12289, 4), (40961, 4), (65537, 4),
        (193, 8), (257, 8), (769, 8), (12289, 8), (40961, 8), (65537, 8),
        (257, 16), (769, 16), (12289, 16), (40961, 16), (65537, 16),
        (12289, 32), (40961, 32), (65537, 32),
    ]
    for p, n in cases:
        if (p - 1) % n != 0:
            continue
        G = roots_of_unity(p, n)
        if G is None or len(G) != n:
            print("%8d %4d  skip (no order-%d elt)" % (p, n, n))
            continue
        e3 = E3_charp(G, p)
        c15 = 15 * n ** 3
        cc = census_charzero(n)
        beta = math.log(p) / math.log(n)
        print("%8d %4d %6.2f %12d %12d %12d %10s %11s" % (
            p, n, beta, e3, c15, cc, str(e3 > c15), str(e3 > cc)))


if __name__ == "__main__":
    main()
