#!/usr/bin/env python3
"""
Probe (#444 / I031): does the (q-1)/n distinct-modulus alphabet ||eta_b|| have NON-TRIVIAL
concentration structure (few distinct moduli << (q-1)/n, or clustering near a small set of
circles)? If YES -> a deterministic structural lever for the sup bound. If NO (moduli spread
~uniformly, as many distinct as cosets) -> mapped refutation: the orbit reduction gives no FREE
modulus concentration; the sup over reps is genuinely a sup over (q-1)/n essentially-distinct values.

Reports, over Fp* at prize-regime primes (PROPER mu_n=2^a, n|p-1, p>>n^3, NEVER n=q-1):
  - #cosets = (p-1)/n
  - #distinct ||eta_b|| (rounded coarse, 3 dp) vs #cosets  (ratio -> concentration)
  - max ||eta_b|| / sqrt(n)   (the prize quantity M/sqrt(n); prize wants <= C*sqrt(log(p/n)))
  - fraction of cosets whose ||eta|| is within 10% of the max (top-cluster mass)
"""
import cmath
import sys
from collections import Counter


def is_prime(m):
    if m < 2:
        return False
    i = 2
    while i * i <= m:
        if m % i == 0:
            return False
        i += 1
    return True


def primitive_root(p):
    if p == 2:
        return 1
    phi = p - 1
    fac = set()
    x = phi
    d = 2
    while d * d <= x:
        while x % d == 0:
            fac.add(d)
            x //= d
        d += 1
    if x > 1:
        fac.add(x)
    for g in range(2, p):
        if all(pow(g, phi // q, p) != 1 for q in fac):
            return g
    return None


def test(n, p):
    g = primitive_root(p)
    step = (p - 1) // n
    mu = [pow(g, (k * step) % (p - 1), p) for k in range(n)]
    w = 2.0 * cmath.pi / p

    def eta_mod(b):
        s = 0j
        for x in mu:
            s += cmath.exp(1j * w * ((b * x) % p))
        return abs(s)

    # one rep per coset: iterate b, skip seen cosets (coset of b = {z*b})
    muset = set(mu)
    seen = set()
    mods = []
    for b in range(1, p):
        if b in seen:
            continue
        seen |= set((z * b) % p for z in muset)
        mods.append(eta_mod(b))
    ncoset = (p - 1) // n
    assert len(mods) == ncoset, f"{len(mods)} != {ncoset}"
    coarse = Counter(round(m, 3) for m in mods)
    ndistinct = len(coarse)
    mx = max(mods)
    sqrtn = n ** 0.5
    top_mass = sum(1 for m in mods if m >= 0.9 * mx) / ncoset
    import math
    sqrt_log = math.sqrt(math.log(p / n))
    print(f"n={n:4d} p={p:8d} | #cosets={ncoset:7d} #distinct|eta|(3dp)={ndistinct:7d} "
          f"conc={ndistinct/ncoset:.3f} | max/sqrt(n)={mx/sqrtn:.3f} "
          f"sqrt(log(p/n))={sqrt_log:.3f} ratio={mx/sqrtn/sqrt_log:.3f} top10%mass={top_mass:.4f}")


if __name__ == "__main__":
    cases = []
    for a in range(2, 6):  # n=4,8,16,32
        n = 2 ** a
        target = max(n ** 3, 1000)
        found = 0
        p = ((target // n) + 1) * n + 1
        while found < 1:
            if is_prime(p):
                cases.append((n, p))
                found += 1
            p += n
    for (n, p) in cases:
        test(n, p)
    sys.exit(0)
