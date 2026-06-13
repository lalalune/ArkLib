#!/usr/bin/env python3
"""Single a=8 (n=256) point, p~n^2.7 to keep the b-sweep tractable (~1e6 primes).
Decisive: does C(n) at n=256 stay sub-sqrt(log n) vs the n=128 value 1.36?"""
import math

def setup(a, target_p):
    n = 2 ** a
    p = max(target_p, n + 1)
    while True:
        p += 1
        if (p - 1) % n:
            continue
        if all(p % d for d in range(2, int(p ** 0.5) + 1)):
            break
    g = None
    for c in range(2, p):
        o = 1; y = c % p
        while y != 1:
            y = (y * c) % p; o += 1
            if o > p: break
        if o == p - 1:
            g = c; break
    h = pow(g, (p - 1) // n, p)
    return p, [pow(h, i, p) for i in range(n)]

def worst_mag(p, H, n):
    w = 2 * math.pi / p
    best = -1.0
    seen = bytearray(p)
    for b in range(1, p):
        if seen[b]:
            continue
        for u in H:
            seen[(b * u) % p] = 1
        sr = si = 0.0
        for x in H:
            ang = w * ((b * x) % p)
            sr += math.cos(ang); si += math.sin(ang)
        m = sr * sr + si * si
        if m > best:
            best = m
    return math.sqrt(best)

a = 8; n = 2 ** a
p, H = setup(a, int(n ** 2.7))   # ~ 256^2.7 ~ 1.1e6
mag = worst_mag(p, H, n)
C = mag / math.sqrt(n * math.log(p / n))
print(f"a={a} n={n} p={p}  |S_b*|={mag:.3f}  C={C:.3f}")
print(f"vs n=128 C~1.36, n=64 C~1.23. sqrt(log2 n) at n=256 = {math.sqrt(math.log2(n)):.3f}")
print(f"C/sqrt(log2 n) = {C/math.sqrt(math.log2(n)):.4f}  (compare n=128: 0.515, n=64: 0.503)")
