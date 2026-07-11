#!/usr/bin/env python3
"""
Probe (#444 / I031): the number of DISTINCT Gauss-period values |eta_b| over Fp* is <= (q-1)/n,
UNCONDITIONALLY (no supplied transversal). Because eta_b is constant on each mu_n-coset and there
are exactly (q-1)/n cosets (orbit_count), the distinct-period count is bounded by the coset count.
This is the metric-entropy collapse log p -> log(p/n) at the period-VALUE level.

Also reports the EXACT distinct count to see how tight (q-1)/n is (it's an upper bound; collisions
across cosets make it loose, but it never exceeds (q-1)/n).
PROPER mu_n: n=2^a, n | p-1, p >> n^3, NEVER n=q-1.
"""
import cmath
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
    g = primitive_root(p)
    step = (p - 1) // n
    mu = [pow(g, (k * step) % (p - 1), p) for k in range(n)]
    assert len(set(mu)) == n
    # use a single additive character psi(t) = exp(2pi i t / p)
    w = 2.0 * cmath.pi / p

    def eta(b):
        s = 0j
        for x in mu:
            s += cmath.exp(1j * w * ((b * x) % p))
        return s

    # distinct period VALUES (complex) and distinct MODULI over Fp*
    vals = set()
    mods = set()
    for b in range(1, p):
        e = eta(b)
        vals.add((round(e.real, 7), round(e.imag, 7)))
        mods.add(round(abs(e), 7))
    expected_coset_count = (p - 1) // n
    distinct_vals = len(vals)
    distinct_mods = len(mods)
    val_ok = distinct_vals <= expected_coset_count
    mod_ok = distinct_mods <= expected_coset_count
    print(f"n={n:4d} p={p:8d} (p-1)/n={expected_coset_count:7d} | "
          f"#distinct_eta_vals={distinct_vals:7d} (<=count:{val_ok}) "
          f"#distinct_|eta|={distinct_mods:7d} (<=count:{mod_ok})")
    return val_ok and mod_ok


if __name__ == "__main__":
    cases = []
    for a in range(2, 6):  # n = 4,8,16,32  (keep p modest for speed)
        n = 2 ** a
        target = max(n ** 3, 1000)
        found = 0
        p = ((target // n) + 1) * n + 1
        while found < 1:
            if is_prime(p):
                cases.append((n, p))
                found += 1
            p += n
    allok = True
    for (n, p) in cases:
        allok &= test(n, p)
    print("\nALL OK" if allok else "\nSOME FAIL")
    sys.exit(0 if allok else 1)
