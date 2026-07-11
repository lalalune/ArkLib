#!/usr/bin/env python3
"""
MULTI-PRIME confirmation of C(n) at a=6,7 (and a=8 if feasible): is the worst-freq
constant C = |S_b*|/sqrt(n log(p/n)) bounded, or does it creep? The single-prime a=7
point ticked to 1.34; average several primes per a to see the true constant.
Uses coset-rep sweep (|S_b| constant on mu_n cosets) to stay O(p) per prime.
"""
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

print("multi-prime worst-freq constant C(n) = |S_b*|/sqrt(n*log(p/n))")
print(f"{'a':>2} {'n':>5} {'#primes':>8} {'C_mean':>8} {'C_max':>7} {'C values'}")
print("-" * 70)
for a in [6, 7]:
    n = 2 ** a
    base = int(n ** 3)
    Cs = []
    tp = base
    tries = 0
    while len(Cs) < (4 if a == 6 else 3) and tries < 60:
        tries += 1
        p, H = setup(a, tp)
        mag = worst_mag(p, H, n)
        C = mag / math.sqrt(n * math.log(p / n))
        Cs.append(C)
        tp = p + max(1000, n)  # jump to next region for a distinct prime
    cmean = sum(Cs) / len(Cs)
    print(f"{a:>2} {n:>5} {len(Cs):>8} {cmean:>8.3f} {max(Cs):>7.3f}   {[round(c,3) for c in Cs]}")

print()
print("If C_mean stays ~1.1-1.2 at a=7 across primes => the a=7 1.34 was a single-prime")
print("fluctuation, constant is bounded => conjecture-consistent at worst freq.")
