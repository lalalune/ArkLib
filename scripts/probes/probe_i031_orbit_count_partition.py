#!/usr/bin/env python3
"""
Probe (#444 / I031): the mu_n-orbits PARTITION Fp* into exactly (p-1)/n equal blocks of size n.
Validates the global partition-cardinality fact the orbit-quotient transversal lemma consumes:
  - n | (p-1)  (required for mu_n to exist as a subgroup of order n)
  - the dilation action of mu_n on Fp* is free (trivial stabilizers) => every orbit has size n
  - # orbits = (p-1)/n  EXACTLY  (orbit-counting / Lagrange)
PROPER mu_n: n=2^a, n | p-1, p >> n^3, NEVER n=q-1.
"""
import sys


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
    assert (p - 1) % n == 0, f"n={n} does not divide p-1={p-1}"
    g = primitive_root(p)
    step = (p - 1) // n
    mu = set(pow(g, (k * step) % (p - 1), p) for k in range(n))
    assert len(mu) == n, f"|mu_n| = {len(mu)} != {n}"
    for a in mu:
        for b in mu:
            assert (a * b) % p in mu
    nonzero = set(range(1, p))
    seen = set()
    orbits = []
    free = True
    for b in range(1, p):
        if b in seen:
            continue
        orb = set((z * b) % p for z in mu)
        orbits.append(orb)
        seen |= orb
        if len(orb) != n:
            free = False
    num_orbits = len(orbits)
    expected = (p - 1) // n
    cover = (seen == nonzero)
    sizes_ok = all(len(o) == n for o in orbits)
    disjoint = (sum(len(o) for o in orbits) == p - 1)
    verdict = (num_orbits == expected) and cover and sizes_ok and disjoint and free
    print(f"n={n:4d} p={p:8d} (p-1)/n={expected:8d} | #orbits={num_orbits:8d} "
          f"all_size_n={sizes_ok} covers_Fp*={cover} disjoint={disjoint} free={free} "
          f"| {'OK' if verdict else 'FAIL'}")
    return verdict


if __name__ == "__main__":
    cases = []
    for a in range(2, 7):  # n = 4,8,16,32,64
        n = 2 ** a
        target = max(n ** 3, 1000)  # p >> n^3
        found = 0
        p = ((target // n) + 1) * n + 1
        while found < 2:
            if is_prime(p):
                cases.append((n, p))
                found += 1
            p += n
    allok = True
    for (n, p) in cases:
        allok &= test(n, p)
    print("\nALL OK" if allok else "\nSOME FAIL")
    sys.exit(0 if allok else 1)
