# Find the SMALLEST (decide-feasible) char-p witness where E_3(mu_n) > 15 n^3,
# i.e. the ERM r=3 ceiling is breached. Scan small n in {4,8,16} over ALL primes p
# with n | p-1, including THICK (small beta) where char-p coincidences are largest.

import math
from collections import Counter
from sympy import primitive_root, isprime


def roots_of_unity(p, n):
    g = primitive_root(p)
    step = (p - 1) // n
    base = pow(g, step, p)
    out = set()
    x = 1
    for _ in range(n):
        out.add(x)
        x = (x * base) % p
    return sorted(out)


def E3_charp(G, p):
    cnt = Counter()
    for a in G:
        for b in G:
            ab = (a + b) % p
            for c in G:
                cnt[(ab + c) % p] += 1
    return sum(v * v for v in cnt.values())


def main():
    print("Smallest breaches E_3(mu_n) > 15 n^3 by n (thick edge):")
    print("%4s %9s %6s %12s %12s %8s" % ("n", "p", "beta", "E3", "15n^3", "exc"))
    for n in [4, 8, 16]:
        found = []
        for p in range(n + 1, 4000):
            if not isprime(p):
                continue
            if (p - 1) % n != 0:
                continue
            G = roots_of_unity(p, n)
            if len(G) != n:
                continue
            e3 = E3_charp(G, p)
            ceil15 = 15 * n ** 3
            if e3 > ceil15:
                beta = math.log(p) / math.log(n)
                cc = 15 * n ** 3 - 45 * n ** 2 + 40 * n
                found.append((p, beta, e3, ceil15, e3 - cc))
        if found:
            for (p, beta, e3, c15, exc) in found[:5]:
                print("%4d %9d %6.2f %12d %12d %8d" % (n, p, beta, e3, c15, exc))
        else:
            print("%4d   (no breach for p<4000)" % n)


if __name__ == "__main__":
    main()
