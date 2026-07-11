#!/usr/bin/env python3
"""
probe_407_n32_height1_check.py  (#407)

Reconcile with 1fa2d5e58's claim C*(n=32)=1 (a height-1 {-1,0,1} relation vanishes at n=32 prize prime).
If TRUE, the realizable break is height-1 (even stronger than my height-2 witness). Verify via MITM at
height 1 (and report the minimal height) across several n=32 prize-band primes. Also re-confirm n=16
p=65537 has NO height-1 or height-2 realizable relation (so the n=16 chain genuinely holds at realizable
support, my correction stands).
"""
import math
from itertools import product

def isprime(x):
    if x < 2: return False
    if x % 2 == 0: return x == 2
    i = 3
    while i*i <= x:
        if x % i == 0: return False
        i += 2
    return True

def primitive_2pow_root(p, m):
    n = 1 << m
    if (p-1) % n != 0: return None
    e = (p-1)//n
    for base in range(2, p):
        r = pow(base, e, p)
        if pow(r, n//2, p) != 1 and pow(r, n, p) == 1:
            return r
    return None

def mitm_has_relation(omega, N, p, maxC):
    pw = [pow(omega, j, p) for j in range(N)]
    half = N//2
    rng = range(-maxC, maxC+1)
    left = {}
    for gl in product(rng, repeat=half):
        s = 0
        for j in range(half):
            if gl[j]: s = (s + gl[j]*pw[j]) % p
        left.setdefault(s, gl)
    for gr in product(rng, repeat=N-half):
        s = 0
        for j in range(N-half):
            if gr[j]: s = (s + gr[j]*pw[half+j]) % p
        need = (-s) % p
        if need in left:
            g = left[need] + gr
            if any(x != 0 for x in g):
                return True, g
    return False, None

def min_height_mitm(omega, N, p, maxC):
    for h in range(1, maxC+1):
        has, g = mitm_has_relation(omega, N, p, h)
        if has: return h, g
    return None, None

def prime_band(m, blo, bhi, count):
    n = 1 << m
    lo = int(n**blo); hi = int(n**bhi)
    base = lo - (lo % n) + 1
    out = []; c = base
    while c <= hi and len(out) < count:
        if isprime(c) and (c-1) % n == 0: out.append(c)
        c += n
    return out

def main():
    print("=== n=32 (N=16) minimal realizable height across prize-band primes (beta~4) ===")
    band = prime_band(5, 4.0, 4.15, 8)
    h1 = 0
    for p in band:
        om = primitive_2pow_root(p, 5)
        if om is None: continue
        h, g = min_height_mitm(om, 16, p, 2)
        beta = math.log(p, 32)
        if h == 1: h1 += 1
        print("  p=%10d beta=%.3f  min realizable height=%s  g=%s" % (p, beta, h, g))
    print("  => height-1 realizable relation at %d/%d n=32 prize-band primes" % (h1, len(band)))

    print("\n=== n=16 p=65537 recheck: min realizable height (confirm none <=2 => chain holds) ===")
    om = primitive_2pow_root(65537, 4)
    h, g = min_height_mitm(om, 8, 65537, 2)
    print("  n=16 p=65537  min realizable height (<=2) = %s  (None => INDEPENDENT, chain holds)" % (h,))

if __name__ == "__main__":
    main()
