# Focused thin/prize-regime sweep of the r=3 ERM rung on mu_n in char-p.
#
# QUESTION: in the prize regime (n=2^a, p > n^3, beta = log p / log n >= ~3-5),
# does the char-p depth-3 additive energy E_3(mu_n) stay <= 15 n^3 (the ERM
# (2*3-1)!!=15 ceiling, i.e. GaussianEnergyBound mu_n 3), or does it breach it?
#
# E_3 = #{6-tuples a+b+c=d+e+f in mu_n} = sum_t (#{a+b+c=t})^2.
# char-0 census value = 15 n^3 - 45 n^2 + 40 n (exact, Lam-Leung).
# char-p coincidence excess = E_3(charp) - census_c0 >= 0 (extra collisions mod p).
# ERM ceiling = 15 n^3. Breach iff E_3 > 15 n^3, i.e. excess > 45 n^2 - 40 n.

import math
from collections import Counter


def find_gen(p):
    # smallest primitive root of F_p^*
    from sympy import primitive_root
    return primitive_root(p)


def roots_of_unity(p, n):
    g = find_gen(p)
    step = (p - 1) // n
    base = pow(g, step, p)
    out = []
    x = 1
    for _ in range(n):
        out.append(x)
        x = (x * base) % p
    return sorted(set(out))


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
    print("%9s %4s %6s %14s %14s %14s %10s %10s" % (
        "p", "n", "beta", "E3_charp", "15n^3_ceil", "census_c0",
        "breach15", "charp_exc"))
    # n=16: primes with increasing beta (p just over n^3=4096 up to deep thin)
    # n=32: n^3 = 32768; deep thin needs p >> 32768
    cases = []
    n16_primes = [4129, 4513, 4673, 6113, 8161, 12289, 16417, 24593, 32833,
                  40961, 65537, 114689, 147457, 163841, 786433]
    for p in n16_primes:
        cases.append((p, 16))
    n32_primes = [40961, 65537, 114689, 147457, 163841, 270337, 786433,
                  1179649, 5767169, 7340033]
    for p in n32_primes:
        cases.append((p, 32))
    n64_primes = [786433, 1179649, 5767169, 7340033, 23068673, 104857601]
    for p in n64_primes:
        cases.append((p, 64))
    for p, n in cases:
        if (p - 1) % n != 0:
            continue
        try:
            G = roots_of_unity(p, n)
        except Exception as e:
            print("%9d %4d skip (%s)" % (p, n, e))
            continue
        if len(G) != n:
            print("%9d %4d skip (|G|=%d)" % (p, n, len(G)))
            continue
        e3 = E3_charp(G, p)
        ceil15 = 15 * n ** 3
        cc = census_charzero(n)
        beta = math.log(p) / math.log(n)
        breach = e3 > ceil15
        excess = e3 - cc
        print("%9d %4d %6.2f %14d %14d %14d %10s %10d" % (
            p, n, beta, e3, ceil15, cc, str(breach), excess))


if __name__ == "__main__":
    main()
