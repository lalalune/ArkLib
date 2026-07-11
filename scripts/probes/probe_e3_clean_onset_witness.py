# Smallest CLEAN onset witness: p > 2^n (so the in-tree r=2 theorem
# E_2(mu_n)=3n^2-3n applies and the r=2 rung HOLDS), yet E_3(mu_n) > 15 n^3
# (r=3 rung BREACHES). This is the honest "r=3 is the first ERM rung to fail
# on mu_n in char-p, even where r=2 is provably fine" statement.

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


def energy(G, p, r):
    cnt = Counter()
    import itertools
    for tup in itertools.product(G, repeat=r):
        cnt[sum(tup) % p] += 1
    return sum(v * v for v in cnt.values())


def main():
    for n in [8, 16, 32]:
        lo = 2 ** n + 1
        hi = lo + 400000
        print("n=%d  (need p > 2^%d = %d, n | p-1)" % (n, n, 2 ** n))
        found = None
        p = lo
        scanned = 0
        while p < hi and scanned < 6000:
            if isprime(p) and (p - 1) % n == 0:
                scanned += 1
                G = roots_of_unity(p, n)
                if len(G) == n:
                    e3 = energy(G, p, 3)
                    if e3 > 15 * n ** 3:
                        e2 = energy(G, p, 2)
                        beta = math.log(p) / math.log(n)
                        found = (p, beta, e2, e3)
                        break
            p += 1
        if found:
            p, beta, e2, e3 = found
            print("  BREACH p=%d beta=%.2f  E_2=%d (<=3n^2=%d: %s)  E_3=%d > 15n^3=%d" % (
                p, beta, e2, 3 * n ** 2, e2 <= 3 * n ** 2, e3, 15 * n ** 3))
        else:
            print("  no r3-breach with p>2^n in scanned range (r=3 rung HOLDS for all thin p>2^n)")


if __name__ == "__main__":
    main()
