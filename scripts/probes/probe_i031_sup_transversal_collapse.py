"""Probe (#444 I031, VALUE-level capstone): the per-frequency core

    M(n) = max_{b in F_p*} |eta_b|,   eta_b = sum_{x in mu_n} e_p(b x)

equals the max taken over ONE representative per mu_n-coset (a transversal of
F_p* / mu_n), i.e. over exactly (q-1)/n values. This is the value-level
companion to orbit_count (the COUNT (q-1)/n is proven; this confirms the SUP
literally collapses onto the transversal). NEVER n=q-1.

Mechanism (proven facts being combined): |eta_b| is constant on each coset
b*mu_n (eta_norm_const_on_coset), and the cosets partition F_p* into (q-1)/n
blocks (orbit_count). So max over F_p* = max over any transversal.
"""
import cmath
import math


def is_prime(m):
    if m < 2:
        return False
    if m % 2 == 0:
        return m == 2
    i = 3
    while i * i <= m:
        if m % i == 0:
            return False
        i += 2
    return True


def find_prime(n, base=None):
    # prize-shaped p >> n^3, p ≡ 1 mod n; small enough to enumerate F_p* fast
    p = (base if base is not None else max(int(n ** 3.5), 8 * n * n * n)) | 1
    while True:
        if p % n == 1 and is_prime(p):
            return p
        p += 2


def primitive_root(p):
    phi = p - 1
    fac = set()
    m = phi
    d = 2
    while d * d <= m:
        while m % d == 0:
            fac.add(d)
            m //= d
        d += 1
    if m > 1:
        fac.add(m)
    for g in range(2, p):
        if all(pow(g, phi // q, p) != 1 for q in fac):
            return g
    return None


def mu_n(p, g, n):
    h = pow(g, (p - 1) // n, p)
    s = []
    x = 1
    for _ in range(n):
        s.append(x)
        x = x * h % p
    return s


def eta_abs(b, mun, p):
    tot = 0j
    for x in mun:
        tot += cmath.exp(1j * 2 * math.pi * ((b * x) % p) / p)
    return abs(tot)


def main():
    print("Test: max_{F_p*}|eta| == max over (q-1)/n coset reps (transversal)")
    for n in [8, 16, 32]:
        p = find_prime(n)
        g = primitive_root(p)
        mun = set(mu_n(p, g, n))
        # full sup over F_p*
        full = 0.0
        seen = set()
        transversal = []
        for b in range(1, p):
            full = max(full, eta_abs(b, mun, p))
            if b not in seen:
                # mark whole coset b*mu_n as seen, b is its representative
                transversal.append(b)
                for x in mun:
                    seen.add((b * x) % p)
        trans_sup = max(eta_abs(b, mun, p) for b in transversal)
        ncoset = len(transversal)
        expected = (p - 1) // n
        ok = abs(full - trans_sup) < 1e-12 and ncoset == expected
        print(f"  n={n} p={p}: #reps={ncoset} (=(q-1)/n={expected}? {ncoset==expected})  "
              f"sup_full={full:.6f} sup_trans={trans_sup:.6f}  match={ok}")


if __name__ == "__main__":
    main()
