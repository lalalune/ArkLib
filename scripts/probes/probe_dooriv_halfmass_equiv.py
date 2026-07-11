#!/usr/bin/env python3
"""
Door-(iv) Lane 2/3 — is the prize EQUIVALENT to a half-mass L1 bound? (tightness check)

My bricks established: |eta_b| <= ||A||+||B|| (coherence<=1, norm_le_halfMass) for EVERY b, and
|eta_{b*}| = ||A||+||B|| at the prize-worst b* (coherence=1). Define the worst half-mass
  H(n) = max_{b!=0} (||A_b|| + ||B_b||)   (A,B = index-2 coset-half sums of eta_b).
Then for the PRIZE object M(n) = max_b |eta_b|:
  (upper)  M(n) <= H(n)            [every b: |eta_b| <= half-mass]
  (lower)  M(n) >= |eta_{b*}| = ||A_{b*}||+||B_{b*}||   where b* = argmax |eta_b|, but the argmax of
           half-mass may differ from argmax of |eta|; so M(n) >= half-mass(argmax|eta|), NOT H(n).

So the question for an EQUIVALENCE prize <=> H(n)=O(sqrt(n log)) is whether H(n) and M(n) are within a
constant factor. Probe both maxes and their ratio H/M in the prize regime.

If H(n)/M(n) is bounded (~const), then M(n)=O(.) <=> H(n)=O(.) and the half-mass L1 is an EQUIVALENT
target (citable reduction). If H/M grows, the half-mass is only an UPPER envelope (one direction).
PROBE-FIRST. proper mu_n, p>>n^3, n=16 FULL F_p* scan, never n=q-1.
"""
import cmath
import math
import random


def is_prime(n):
    if n < 2:
        return False
    for q in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if n % q == 0:
            return n == q
    d = n - 1
    r = 0
    while d % 2 == 0:
        d //= 2
        r += 1
    for a in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(r - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True


def find_prime(n, beta):
    target = int(round(n ** beta))
    k0 = max(2, target // n)
    for dk in range(0, 400000):
        for k in (k0 + dk, k0 - dk):
            if k < 2:
                continue
            p = k * n + 1
            if p > n ** 3 and is_prime(p):
                return p
    return None


def primitive_root(p):
    phi = p - 1
    factors = set()
    m = phi
    d = 2
    while d * d <= m:
        if m % d == 0:
            factors.add(d)
            while m % d == 0:
                m //= d
        d += 1
    if m > 1:
        factors.add(m)
    for g in range(2, p):
        if all(pow(g, phi // f, p) != 1 for f in factors):
            return g
    return None


def halves(n, p, g):
    m = (p - 1) // n
    h = pow(g, m, p)
    mu = [pow(h, j, p) for j in range(n)]
    even = [mu[j] for j in range(0, n, 2)]
    odd = [mu[j] for j in range(1, n, 2)]
    return even, odd


print(f"{'n':>5} {'p':>11} {'M=max|eta|/sqn':>15} {'H=maxHalf/sqn':>15} {'H/M':>8} "
      f"{'mode':>10}")
for a, full in ((4, True), (5, False), (6, False)):
    n = 2 ** a
    p = find_prime(n, 4.0)
    g = primitive_root(p)
    even, odd = halves(n, p, g)
    sqn = math.sqrt(n)
    tau = 2.0 * math.pi / p
    if full:
        bs = range(1, p)
    else:
        random.seed(55 + n)
        bs = random.sample(range(1, p), min(8000, p - 1))
    M = 0.0
    H = 0.0
    for b in bs:
        A = sum(cmath.exp(1j * tau * ((b * y) % p)) for y in even)
        B = sum(cmath.exp(1j * tau * ((b * y) % p)) for y in odd)
        M = max(M, abs(A + B) / sqn)
        H = max(H, (abs(A) + abs(B)) / sqn)
    print(f"{n:>5} {p:>11} {M:>15.4f} {H:>15.4f} {H / M:>8.4f} {'FULL' if full else 'sampled':>10}")

print()
print("READING:")
print("- H/M ~ const (bounded) => half-mass L1 is an EQUIVALENT prize target (citable reduction).")
print("- H/M grows => half-mass is only an upper envelope (one direction); the reduction is one-way.")
print("  (norm_le_halfMass already gives M<=H always; this checks the reverse constant-factor.)")
