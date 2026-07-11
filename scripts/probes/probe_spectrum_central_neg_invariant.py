#!/usr/bin/env python3
"""
probe_spectrum_central_neg_invariant.py  (#444, lane spectralcentral)

O229 gave dilation invariance g*spectrum=spectrum (union of mu_n-orbits). The palindrome gives
spectrum(n-r) = -spectrum(r) (ACROSS depths). NEW joint content: at the SELF-COMPLEMENTARY central
depth r = n/2, those collapse to a WITHIN-depth NEGATION invariance:
    spectrum(n/2) = -spectrum(n/2)     (negation-closed at the central depth),
because complementation S |-> mu minus S is a fixed-point-free involution on powersetCard (n/2) mu
sending sum_S |-> -sum_S (when sum_mu = 0). Combined with dilation, spectrum(n/2) is invariant
under <mu_n, -1>. We verify on PROPER thin mu_n (n=2^a), p >> n^3, p == 1 mod n, NEVER n=q-1.
"""
import sys
from sympy import isprime, primitive_root
from itertools import combinations

def find_primes(n, count, lo):
    out, p = [], lo - (lo % n) + 1
    while len(out) < count:
        if p > n and isprime(p) and (p - 1) % n == 0:
            out.append(p)
        p += n
    return out

def muN(p, n):
    g = primitive_root(p)
    e = (p - 1) // n
    base = pow(g, e, p)
    return sorted({pow(base, j, p) for j in range(n)})

def spectrum(mu, r, p):
    return {sum(S) % p for S in combinations(mu, r)}

def main():
    total = fails = 0
    for a in range(2, 5):           # n = 4,8,16  (n/2 = 2,4,8 -> C(16,8)=12870 ok)
        n = 1 << a
        lo = n ** 3 + 1
        for p in find_primes(n, 3, lo):
            mu = muN(p, n)
            assert sum(mu) % p == 0, "mu_n must sum to 0 (n even)"
            r = n // 2
            spec = spectrum(mu, r, p)
            neg = {(-v) % p for v in spec}
            total += 1
            ok = (neg == spec)
            if not ok:
                fails += 1
                print(f"FAIL neg-invariance n={n} p={p} r={r}")
            print(f"n={n:2d} p={p:6d} r=n/2={r:2d}: |spec|={len(spec):4d} neg-invariant={ok}")
    print(f"\n=== {total} central-depth instances, {fails} fails ===")
    if fails == 0:
        print("VERIFIED: spectrum(n/2) = -spectrum(n/2). Central depth is negation-closed.")
    sys.exit(1 if fails else 0)

if __name__ == "__main__":
    main()
